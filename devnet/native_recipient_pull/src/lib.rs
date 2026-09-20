//! Raw signed transaction integration on unchanged ethrex LEVM, Hegota.
//! All contracts/proofs/transactions are external reviewed fixtures. Only chain
//! genesis funding and the pinned client's system contracts are seeded here.
//! Each case replays real deployment/setup transactions on a fresh database.
//! This exercises native transaction execution, not networking or block import.

#[cfg(test)]
mod tests {
    use bytes::Bytes;
    use ethrex_common::{
        Address, H256, U256,
        constants::EMPTY_KECCAK_HASH,
        types::{
            Account, AccountInfo, AccountState, ChainConfig, Code, CodeMetadata, Fork, Transaction,
            frame_tx_nonce_manager, frame_tx_recent_root,
        },
        utils::keccak,
    };
    use ethrex_crypto::NativeCrypto;
    use ethrex_levm::{
        db::{Database, gen_db::GeneralizedDatabase},
        environment::{EVMConfig, Environment},
        errors::DatabaseError,
        tracing::LevmCallTracer,
        vm::{VM, VMType},
    };
    use rustc_hash::FxHashMap;
    use serde::Deserialize;
    use serde_json::{Value, json};
    use std::{
        collections::{BTreeMap, BTreeSet},
        fs,
        path::{Path, PathBuf},
        str::FromStr,
        sync::Arc,
    };

    type Storage = BTreeMap<String, BTreeMap<String, String>>;

    #[derive(Deserialize)]
    struct Manifest {
        chain_id: u64,
        slot_number: u64,
        #[serde(default = "base_fee")]
        base_fee: u64,
        #[serde(default = "block_gas_limit")]
        block_gas_limit: u64,
        #[serde(default)]
        timestamp: Option<u64>,
        accounts: Vec<SeedAccount>,
        #[serde(default)]
        setup: Vec<Step>,
        cases: Vec<Case>,
    }
    fn base_fee() -> u64 {
        1
    }
    fn block_gas_limit() -> u64 {
        60_000_000
    }

    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct SeedAccount {
        address: String,
        balance: String,
        #[serde(default)]
        nonce: u64,
        #[serde(default)]
        code: Option<String>,
        #[serde(default)]
        storage: BTreeMap<String, String>,
    }

    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Case {
        name: String,
        transactions: Vec<Step>,
    }

    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Step {
        raw: String,
        #[serde(default)]
        slot_number: Option<u64>,
        #[serde(default)]
        statuses: Option<Vec<u8>>,
        #[serde(default)]
        frame_state_gas: Option<Vec<u64>>,
        #[serde(default)]
        success: Option<bool>,
        #[serde(default)]
        accepted: Option<bool>,
        #[serde(default)]
        error_contains: Option<String>,
        #[serde(default)]
        storage: Storage,
        #[serde(default)]
        balances: BTreeMap<String, String>,
        #[serde(default)]
        balance_delta: BTreeMap<String, String>,
        #[serde(default)]
        balance_delta_before_gas: BTreeMap<String, String>,
        #[serde(default)]
        nonces: BTreeMap<String, u64>,
        #[serde(default)]
        code_hashes: BTreeMap<String, String>,
        #[serde(default)]
        allowed_changed_accounts: Option<Vec<String>>,
    }

    struct EmptyDatabase;
    impl Database for EmptyDatabase {
        fn get_account_state(&self, _: Address) -> Result<AccountState, DatabaseError> {
            Ok(AccountState::default())
        }
        fn get_storage_value(&self, _: Address, _: H256) -> Result<U256, DatabaseError> {
            Ok(U256::zero())
        }
        fn get_block_hash(&self, _: u64) -> Result<H256, DatabaseError> {
            Ok(H256::zero())
        }
        fn get_chain_config(&self) -> Result<ChainConfig, DatabaseError> {
            Ok(ChainConfig::default())
        }
        fn get_account_code(&self, _: H256) -> Result<Code, DatabaseError> {
            Ok(Code::from_bytecode(Bytes::new(), &NativeCrypto))
        }
        fn get_code_metadata(&self, _: H256) -> Result<CodeMetadata, DatabaseError> {
            Ok(CodeMetadata { length: 0 })
        }
    }

    fn address(text: &str) -> Result<Address, String> {
        Address::from_str(text).map_err(|e| format!("address {text}: {e}"))
    }
    fn quantity(text: &str) -> Result<U256, String> {
        if let Some(value) = text.strip_prefix("0x") {
            U256::from_str_radix(value, 16).map_err(|e| e.to_string())
        } else {
            U256::from_dec_str(text).map_err(|e| e.to_string())
        }
    }
    fn slot_key(text: &str) -> Result<H256, String> {
        Ok(H256::from(quantity(text)?.to_big_endian()))
    }
    fn read_hex(root: &Path, file: &str) -> Result<Bytes, String> {
        let text = fs::read_to_string(root.join(file)).map_err(|e| format!("{file}: {e}"))?;
        hex::decode(text.trim().strip_prefix("0x").unwrap_or(text.trim()))
            .map(Bytes::from)
            .map_err(|e| format!("{file}: {e}"))
    }

    // Extract the literal directly from this pinned client's unchanged source,
    // and verify its own published hash. No substituted recent-root behavior.
    fn recent_root_code() -> Result<Bytes, String> {
        let source = include_str!(concat!(
            env!("ETHREX_SOURCE"),
            "/crates/vm/system_contracts.rs"
        ));
        let array = source
            .split("pub const RECENT_ROOT_RUNTIME_BYTECODE: [u8; 345] = [")
            .nth(1)
            .ok_or("missing recent-root literal")?
            .split("];")
            .next()
            .ok_or("unterminated recent-root literal")?;
        let code: Vec<u8> = array
            .split(',')
            .filter(|word| !word.trim().is_empty())
            .map(|word| {
                u8::from_str_radix(word.trim().trim_start_matches("0x"), 16)
                    .map_err(|e| e.to_string())
            })
            .collect::<Result<_, _>>()?;
        if code.len() != 345
            || format!("{:x}", keccak(&code))
                != "cd1cae00e1d37cf97195f9e716dfa1b9a804e36bb5d7726c4f2c50e2580275a5"
        {
            return Err("recent-root source runtime/hash changed".into());
        }
        Ok(code.into())
    }

    fn seeded_db(manifest: &Manifest, root: &Path) -> Result<GeneralizedDatabase, String> {
        let mut cache = FxHashMap::default();
        for seed in &manifest.accounts {
            let addr = address(&seed.address)?;
            if addr == frame_tx_recent_root() || addr == frame_tx_nonce_manager() {
                return Err("fixture cannot override chain system accounts".into());
            }
            let mut storage = FxHashMap::default();
            for (key, value) in &seed.storage {
                storage.insert(slot_key(key)?, quantity(value)?);
            }
            let code = match &seed.code {
                Some(path) => read_hex(root, path)?,
                None => Bytes::new(),
            };
            let account = Account::new(
                quantity(&seed.balance)?,
                Code::from_bytecode(code, &NativeCrypto),
                seed.nonce,
                storage,
            );
            if cache.insert(addr, account).is_some() {
                return Err(format!("duplicate genesis address {addr:?}"));
            }
        }
        for (addr, code) in [
            (frame_tx_recent_root(), recent_root_code()?),
            (
                frame_tx_nonce_manager(),
                Bytes::from_static(&[0x60, 0, 0x60, 0, 0xfd]),
            ),
        ] {
            cache.insert(
                addr,
                Account::new(
                    U256::zero(),
                    Code::from_bytecode(code, &NativeCrypto),
                    1,
                    FxHashMap::default(),
                ),
            );
        }
        Ok(GeneralizedDatabase::new_with_account_state(
            Arc::new(EmptyDatabase),
            cache,
        ))
    }

    fn balance(db: &GeneralizedDatabase, addr: Address) -> U256 {
        db.current_accounts_state
            .get(&addr)
            .map(|a| a.info.balance)
            .unwrap_or_default()
    }
    fn storage_value(db: &GeneralizedDatabase, addr: Address, key: H256) -> U256 {
        db.current_accounts_state
            .get(&addr)
            .and_then(|a| a.storage.get(&key))
            .copied()
            .unwrap_or_default()
    }
    fn snapshot(
        db: &GeneralizedDatabase,
    ) -> BTreeMap<Address, (AccountInfo, BTreeMap<H256, U256>)> {
        db.current_accounts_state
            .iter()
            .filter_map(|(addr, account)| {
                let storage: BTreeMap<_, _> = account
                    .storage
                    .iter()
                    .filter(|(_, v)| !v.is_zero())
                    .map(|(k, v)| (*k, *v))
                    .collect();
                if account.info.balance.is_zero()
                    && account.info.nonce == 0
                    && account.info.code_hash == *EMPTY_KECCAK_HASH
                    && storage.is_empty()
                {
                    None
                } else {
                    Some((*addr, (account.info.clone(), storage)))
                }
            })
            .collect()
    }
    fn state_json(db: &GeneralizedDatabase) -> Value {
        Value::Object(snapshot(db).into_iter().map(|(addr, (info, storage))| (format!("{addr:#x}"), json!({"balance":format!("{:#x}",info.balance),"nonce":info.nonce,"code_hash":format!("{:#x}",info.code_hash),"storage":storage.into_iter().map(|(k,v)|(format!("{k:#x}"),format!("{v:#x}"))).collect::<BTreeMap<_,_>>() }))).collect())
    }

    fn execute_step(
        manifest: &Manifest,
        root: &Path,
        db: &mut GeneralizedDatabase,
        step: &Step,
    ) -> Result<Value, String> {
        let raw = read_hex(root, &step.raw)?;
        let tx =
            Transaction::decode_canonical(&raw).map_err(|e| format!("canonical decode: {e}"))?;
        if tx.chain_id() != Some(manifest.chain_id) {
            return Err("transaction chain id does not match native environment".into());
        }
        let sender = tx
            .sender(&NativeCrypto)
            .map_err(|e| format!("transaction signature recovery: {e}"))?;
        let slot = step.slot_number.unwrap_or(manifest.slot_number);
        let mut env = Environment {
            origin: sender,
            gas_limit: tx.gas_limit(),
            block_gas_limit: manifest.block_gas_limit,
            config: EVMConfig::new(Fork::Hegota, EVMConfig::canonical_values(Fork::Hegota)),
            chain_id: U256::from(manifest.chain_id),
            base_fee_per_gas: U256::from(manifest.base_fee),
            gas_price: tx
                .effective_gas_price(Some(manifest.base_fee))
                .ok_or("max fee below base fee")?,
            tx_nonce: tx.nonce(),
            block_number: slot,
            timestamp: manifest.timestamp.unwrap_or(slot * 12),
            tx_max_priority_fee_per_gas: tx.max_priority_fee(),
            tx_max_fee_per_gas: tx.max_fee_per_gas(),
            tx_max_fee_per_blob_gas: tx.max_fee_per_blob_gas(),
            tx_blob_hashes: tx.blob_versioned_hashes(),
            base_blob_fee_per_gas: U256::one(),
            ..Default::default()
        };
        env.slot_number = U256::from(slot);
        env.config.slot_number = U256::from(slot);
        // Execute each transaction in isolation at its specified slot, with
        // the full block allowance. This does not perform block import or
        // cumulative block accounting. No VM bypass flags are enabled.
        if tx.gas_limit() > manifest.block_gas_limit {
            return Err("transaction exceeds declared fresh-block gas allowance".into());
        }
        let before = snapshot(db);
        let mut before_balances = BTreeMap::new();
        for addr in step
            .balance_delta
            .keys()
            .chain(step.balance_delta_before_gas.keys())
        {
            before_balances.insert(addr.clone(), balance(db, address(addr)?));
        }
        let effective_price = env.gas_price;
        let result = VM::new(
            env,
            db,
            &tx,
            LevmCallTracer::disabled(),
            VMType::L1,
            &NativeCrypto,
            None,
        )
        .map_err(|e| format!("VM::new: {e:?}"))?
        .execute();
        let mut errors = Vec::new();
        let mut paid_fee = None;
        let execution = match result {
            Ok(report) => {
                let fee = U256::from(report.gas_spent)
                    .checked_mul(effective_price)
                    .ok_or("actual fee overflow")?;
                paid_fee = Some((report.payer_address.unwrap_or(sender), fee));
                if let Some(expected) = &step.frame_state_gas {
                    let observed = report
                        .frame_results
                        .as_ref()
                        .map(|frames| frames.iter().map(|frame| frame.2).collect::<Vec<_>>());
                    if observed.as_ref() != Some(expected) {
                        errors.push(format!(
                            "frame state gas {observed:?}, expected {expected:?}"
                        ));
                    }
                }
                if step.error_contains.is_some() || step.accepted == Some(false) {
                    errors.push(
                        "transaction accepted but an invalid-transaction error was expected"
                            .to_string(),
                    );
                }
                let statuses = report
                    .frame_results
                    .as_ref()
                    .map(|frames| frames.iter().map(|frame| frame.0).collect::<Vec<_>>());
                if let Some(expected) = &step.statuses {
                    if statuses.as_ref() != Some(expected) {
                        errors.push(format!(
                            "frame statuses {statuses:?}, expected {expected:?}"
                        ));
                    }
                } else if matches!(tx, Transaction::FrameTransaction(_))
                    && step.error_contains.is_none()
                    && step.accepted != Some(false)
                {
                    errors.push("FrameTx fixture must explicitly state expected statuses".into());
                }
                let expected_success = step.success.unwrap_or_else(|| {
                    step.statuses
                        .as_ref()
                        .map(|s| s.iter().all(|v| *v == 1))
                        .unwrap_or(true)
                });
                if report.is_success() != expected_success {
                    errors.push(format!(
                        "aggregate result {:?}, expected success={expected_success}",
                        report.result
                    ));
                }
                json!({"valid":true,"report":report})
            }
            Err(error) => {
                let description = format!("{error:?}");
                match &step.error_contains {
                    Some(expected) if description.contains(expected) => {}
                    Some(expected) => errors.push(format!(
                        "invalid transaction error {description}, expected substring {expected}"
                    )),
                    None if step.accepted == Some(false) => {}
                    None => errors.push(format!("unexpected invalid transaction: {description}")),
                }
                if snapshot(db) != before {
                    errors.push("invalid transaction changed persistent state".into());
                }
                json!({"valid":false,"error":description})
            }
        };
        if let Some(addresses) = &step.allowed_changed_accounts {
            let allowed = addresses
                .iter()
                .map(|value| address(value))
                .collect::<Result<BTreeSet<_>, _>>()?;
            let after = snapshot(db);
            let all_addresses: BTreeSet<_> = before.keys().chain(after.keys()).copied().collect();
            for addr in all_addresses {
                if before.get(&addr) != after.get(&addr) && !allowed.contains(&addr) {
                    errors.push(format!(
                        "unexpected account state change outside allowlist: {addr:#x}"
                    ));
                }
            }
        }
        for (addr, expected) in &step.balances {
            let observed = balance(db, address(addr)?);
            if observed != quantity(expected)? {
                errors.push(format!("balance {addr}: {observed}, expected {expected}"));
            }
        }
        for (addr, delta) in &step.balance_delta {
            let previous = before_balances[addr];
            let expected = if let Some(value) = delta.strip_prefix('-') {
                previous
                    .checked_sub(quantity(value)?)
                    .ok_or("negative expected balance")?
            } else {
                previous
                    .checked_add(quantity(delta.trim_start_matches('+'))?)
                    .ok_or("expected balance overflow")?
            };
            let observed = balance(db, address(addr)?);
            if observed != expected {
                errors.push(format!(
                    "balance delta {addr}: before {previous}, after {observed}, expected {delta}"
                ));
            }
        }
        for (addr, delta) in &step.balance_delta_before_gas {
            let account = address(addr)?;
            let previous = before_balances[addr];
            let before_fee = if let Some(value) = delta.strip_prefix('-') {
                previous
                    .checked_sub(quantity(value)?)
                    .ok_or("negative expected business balance")?
            } else {
                previous
                    .checked_add(quantity(delta.trim_start_matches('+'))?)
                    .ok_or("business balance overflow")?
            };
            let fee = paid_fee
                .filter(|(payer, _)| *payer == account)
                .map(|(_, amount)| amount)
                .unwrap_or_default();
            let expected = before_fee
                .checked_sub(fee)
                .ok_or("expected payer balance below fees")?;
            let observed = balance(db, account);
            if observed != expected {
                errors.push(format!("fee-adjusted balance delta {addr}: before {previous}, after {observed}, expected business delta {delta}, fee {fee}"));
            }
        }
        for (addr, slots) in &step.storage {
            for (key, expected) in slots {
                let observed = storage_value(db, address(addr)?, slot_key(key)?);
                if observed != quantity(expected)? {
                    errors.push(format!(
                        "storage {addr}[{key}]: {observed:#x}, expected {expected}"
                    ));
                }
            }
        }
        for (addr, expected) in &step.nonces {
            let observed = db
                .current_accounts_state
                .get(&address(addr)?)
                .map(|a| a.info.nonce)
                .unwrap_or_default();
            if observed != *expected {
                errors.push(format!("nonce {addr}: {observed}, expected {expected}"));
            }
        }
        for (addr, expected) in &step.code_hashes {
            let observed = db
                .current_accounts_state
                .get(&address(addr)?)
                .map(|a| a.info.code_hash)
                .unwrap_or(*EMPTY_KECCAK_HASH);
            if observed != slot_key(expected)? {
                errors.push(format!(
                    "code hash {addr}: {observed:#x}, expected {expected}"
                ));
            }
        }
        Ok(
            json!({"raw":step.raw,"raw_hash":format!("{:#x}",keccak(&raw)),"sender":format!("{sender:#x}"),"slot_number":slot,"effective_gas_price":format!("{effective_price:#x}"),"paid_fee":paid_fee.map(|(payer,amount)|json!({"payer":format!("{payer:#x}"),"amount":format!("{amount:#x}")})),"execution":execution,"errors":errors,"state":state_json(db)}),
        )
    }

    #[test]
    fn native_integration_cases() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures");
        let manifest: Manifest = serde_json::from_str(
            &fs::read_to_string(root.join("manifest.json"))
                .expect("fixtures/manifest.json must exist"),
        )
        .expect("valid fixture manifest");
        assert!(
            !manifest.cases.is_empty(),
            "integration fixture must contain cases"
        );
        let filter = std::env::var("NATIVE_CASE_FILTER").unwrap_or_default();
        let mut cases = Vec::new();
        let mut failures = Vec::new();
        for case in manifest
            .cases
            .iter()
            .filter(|case| case.name.contains(&filter))
        {
            println!("native case: {}", case.name);
            let mut db = seeded_db(&manifest, &root).expect("valid chain genesis");
            let mut steps = Vec::new();
            for step in manifest.setup.iter().chain(case.transactions.iter()) {
                match execute_step(&manifest, &root, &mut db, step) {
                    Ok(report) => {
                        let errors = report["errors"].as_array().expect("error array");
                        let execution = &report["execution"];
                        if execution["valid"] == true {
                            let result = &execution["report"];
                            let frames = result["frame_results"].as_array().map(|frames| {
                                frames.iter().map(|frame| json!({
                                    "status":frame[0],"execution_gas":frame[1],"state_gas":frame[2]
                                })).collect::<Vec<_>>()
                            });
                            println!(
                                "  {}: {}",
                                step.raw,
                                json!({
                                    "result":result["result"],"gas_spent":result["gas_spent"],
                                    "state_gas":result["state_gas_used"],"frames":frames,"errors":errors
                                })
                            );
                        } else {
                            println!(
                                "  {}: {}",
                                step.raw,
                                json!({"error":execution["error"],"errors":errors})
                            );
                        }
                        let failed = !errors.is_empty();
                        if failed {
                            failures.push(format!(
                                "{} / {}: {}",
                                case.name, step.raw, report["errors"]
                            ));
                        }
                        steps.push(report);
                        if failed {
                            break;
                        }
                    }
                    Err(error) => {
                        failures.push(format!("{} / {}: {error}", case.name, step.raw));
                        break;
                    }
                }
            }
            cases.push(json!({"name":case.name,"steps":steps}));
        }
        assert!(!cases.is_empty(), "case filter selected no fixtures");
        let output = std::env::var("NATIVE_REPORT")
            .map(PathBuf::from)
            .unwrap_or_else(|_| {
                PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("native-report.json")
            });
        fs::write(&output, serde_json::to_string_pretty(&json!({"client":"ethrex hegota-testnet 247e2dd2","chain_id":manifest.chain_id,"block_gas_limit":manifest.block_gas_limit,"cases":cases,"failures":failures})).unwrap()).expect("write native report");
        assert!(
            failures.is_empty(),
            "native integration failures: {}",
            failures.join("\n")
        );
    }
}
