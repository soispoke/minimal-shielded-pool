// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.24;

import {ShieldedPoolLogic} from "../src/ShieldedPoolLogic.sol";
import {IPool, LogicProxy, MockPoseidonT3, MockPoseidonT4} from "./DispatcherPool.t.sol";

interface RecipientPullVm {
    function addr(uint256 key) external returns (address);
    function sign(uint256 key, bytes32 digest) external returns (uint8, bytes32, bytes32);
    function deal(address who, uint256 amount) external;
    function prank(address sender) external;
    function chainId(uint256 id) external;
}

/// @dev TEST MODEL ONLY. Forge does not execute TXPARAMLOAD or FRAMEPARAM status reads.
/// The test driver reports the actual attempted settlement calldata and result,
/// and vm.prank models ENTRY_POINT as DEFAULT frame 3's caller. This trusted oracle
/// is not a deployable substitute for authenticated frame context opcodes.
contract RecipientPullFrameContext {
    address private immutable driver = msg.sender;
    address public pool;
    address public recipient;
    address public transactionSender;
    address public currentTarget;
    bytes32 public settlementHash;
    bool public settlementSucceeded;
    bool public active;
    uint256 public frameIndex;

    function open(address pool_, ShieldedPoolLogic.Spend calldata spend, bool succeeded, uint256 index) external {
        require(msg.sender == driver, "test driver only");
        pool = pool_;
        recipient = spend.recipient;
        settlementHash = keccak256(abi.encode(spend));
        settlementSucceeded = succeeded;
        frameIndex = index;
        active = true;
    }

    function enterFrame(address sender, address target) external {
        require(msg.sender == driver, "test driver only");
        transactionSender = sender;
        currentTarget = target;
    }

    function close() external {
        require(msg.sender == driver, "test driver only");
        active = false;
    }
}

/// @dev TEST-ONLY EXISTING ACCOUNT, deliberately not a production account SDK.
/// Settlement and payout use the unchanged ShieldedPoolLogic. Owner signatures
/// authorize one exact call; a valid note proof does not authorize this account.
contract RecipientPullAccount {
    struct Action {
        address pool;
        address target;
        uint256 value;
        bytes data;
        uint256 callGas;
        uint256 nonce;
        bytes32 settlementHash;
    }

    bytes32 private constant DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant ACTION_TYPEHASH = keccak256(
        "PullAction(address pool,address target,uint256 value,bytes data,uint256 callGas,uint256 nonce,bytes32 settlementHash)"
    );
    uint256 private constant HALF_ORDER = 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0;

    address public immutable owner;
    RecipientPullFrameContext private immutable context;
    uint256 public nonce;
    bool private entered;

    error Unauthorized();
    error WrongNonce();
    error WrongFrame();
    error SettlementFailed();
    error Reentrant();

    constructor(address owner_, RecipientPullFrameContext context_) {
        require(owner_ != address(0));
        owner = owner_;
        context = context_;
    }

    function digest(Action calldata a) public view returns (bytes32) {
        bytes32 domainSeparator = keccak256(
            abi.encode(
                DOMAIN_TYPEHASH, keccak256("RecipientPullTestAccount"), keccak256("1"), block.chainid, address(this)
            )
        );
        bytes32 actionHash = keccak256(
            abi.encode(
                ACTION_TYPEHASH, a.pool, a.target, a.value, keccak256(a.data), a.callGas, a.nonce, a.settlementHash
            )
        );
        return keccak256(abi.encodePacked("\x19\x01", domainSeparator, actionHash));
    }

    function execute(Action calldata a, uint8 v, bytes32 r, bytes32 s) external {
        if (entered) revert Reentrant();
        if (
            !context.active() || context.frameIndex() != 3 || msg.sender != address(0xAA)
                || context.transactionSender() != a.pool || context.currentTarget() != address(this)
                || context.pool() != a.pool || context.recipient() != address(this)
                || context.settlementHash() != a.settlementHash
        ) revert WrongFrame();
        if (!context.settlementSucceeded()) revert SettlementFailed();
        if (a.nonce != nonce) revert WrongNonce();
        if ((v != 27 && v != 28) || uint256(s) > HALF_ORDER || ecrecover(digest(a), v, r, s) != owner) {
            revert Unauthorized();
        }
        entered = true;
        nonce++;
        // A permissionless claimant may already have delivered this credit to
        // the account. Claim all outstanding credit, spend only signed value.
        if (IPool(a.pool).withdrawalCredit(address(this)) != 0) {
            IPool(a.pool).claimWithdrawal(payable(address(this)));
        }
        (bool ok, bytes memory ret) = a.target.call{value: a.value, gas: a.callGas}(a.data);
        if (!ok) assembly { revert(add(ret, 32), mload(ret)) }
        entered = false;
    }

    receive() external payable {}
}

contract RecipientPullTarget {
    uint256 public calls;
    uint256 public marker;
    address public caller;
    error ActionFailed();

    function act(uint256 marker_) external payable {
        calls++;
        marker = marker_;
        caller = msg.sender;
    }

    function fail() external payable {
        calls++;
        revert ActionFailed();
    }

    function exhaustGas() external payable {
        while (true) {}
    }
}

contract RecipientPullReentrantTarget {
    address private account;
    IPool private pool;
    bytes private payload;
    bytes4 public accountError;
    bytes4 public claimError;
    uint256 public calls;

    function configure(address account_, IPool pool_, bytes calldata payload_) external {
        account = account_;
        pool = pool_;
        payload = payload_;
    }

    function attack() external payable {
        calls++;
        (bool ok, bytes memory ret) = account.call(payload);
        require(!ok, "account reentered");
        // Only the four-byte revert selector is compared; arguments are intentionally discarded.
        // forge-lint: disable-next-line(unsafe-typecast)
        accountError = bytes4(ret);
        (ok, ret) = address(pool).call(abi.encodeCall(IPool.claimWithdrawal, (payable(account))));
        require(!ok, "pool paid twice");
        // Only the four-byte revert selector is compared; arguments are intentionally discarded.
        // forge-lint: disable-next-line(unsafe-typecast)
        claimError = bytes4(ret);
    }
}

/// @dev Negative control: entry-point caller and successful-frame checks alone do not
/// establish recipient authority. A note owner can choose another recipient.
contract RecipientPullUnauthenticatedAccount {
    function execute(IPool pool, address payable target, uint256 value) external {
        require(msg.sender == address(0xAA));
        pool.claimWithdrawal(payable(address(this)));
        (bool ok,) = target.call{value: value}("");
        require(ok);
    }

    receive() external payable {}
}

contract RecipientPullTest {
    RecipientPullVm private constant vm = RecipientPullVm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 private constant OWNER_KEY = 0xA11CE;
    uint256 private constant NOTE_OWNER_KEY = 0xB0B;
    bytes32 private constant SINK_0 = 0x23f1b896ada6ee5dac80945b11329e7ab64412c2be9f5c87cfa3261cc1d8216f;
    bytes32 private constant SINK_1 = 0x2fd476622c67c880b3049a76c7337192362834c9d6dfb55c5060bb96c98932bb;

    ShieldedPoolLogic private logic;
    LogicProxy private proxy;
    IPool private pool;
    RecipientPullFrameContext private context;
    RecipientPullAccount private account;
    RecipientPullTarget private target;
    uint256 private nextNullifier = 1;

    function setUp() public {
        logic = new ShieldedPoolLogic(address(new MockPoseidonT3()), address(new MockPoseidonT4()));
        proxy = new LogicProxy(address(logic));
        pool = IPool(address(proxy));
        context = new RecipientPullFrameContext();
        account = new RecipientPullAccount(vm.addr(OWNER_KEY), context);
        target = new RecipientPullTarget();
        vm.deal(address(proxy), 100 ether);
    }

    function _spend(uint256 amount, address recipient) private returns (ShieldedPoolLogic.Spend memory s) {
        s = ShieldedPoolLogic.Spend({
            root: bytes32(uint256(7)),
            rootSlot: 9,
            epoch: 0,
            domain: pool.domain(),
            nf1: bytes32(nextNullifier++),
            nf2: bytes32(nextNullifier++),
            outCm1: SINK_0,
            outCm2: SINK_1,
            publicAmount: amount,
            fee: 1,
            recipient: recipient,
            authorizer: vm.addr(NOTE_OWNER_KEY)
        });
    }

    function _action(ShieldedPoolLogic.Spend memory s) private view returns (RecipientPullAccount.Action memory a) {
        a = RecipientPullAccount.Action({
            pool: address(pool),
            target: address(target),
            value: s.publicAmount,
            data: abi.encodeCall(RecipientPullTarget.act, (42)),
            callGas: 200_000,
            nonce: account.nonce(),
            settlementHash: keccak256(abi.encode(s))
        });
    }

    function _signed(RecipientPullAccount who, RecipientPullAccount.Action memory a, uint256 key)
        private
        returns (bytes memory)
    {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, who.digest(a));
        return abi.encodeCall(RecipientPullAccount.execute, (a, v, r, s));
    }

    function _settle(LogicProxy which, ShieldedPoolLogic.Spend memory s) private returns (bool ok) {
        // The dispatcher proof/nonce gate is outside this test's scope. The
        // proxy admits test spends, then runs the real production settlement.
        (ok,) = address(which).call(abi.encodeCall(LogicProxy.settleAsSelf, (s)));
        context.open(address(which), s, ok, 3);
    }

    function _frame(address sender, address recipient, bytes memory payload, uint256 gasCap)
        private
        returns (bool ok, bytes memory ret)
    {
        context.enterFrame(sender, recipient);
        vm.prank(address(0xAA));
        (ok, ret) = recipient.call{gas: gasCap}(payload);
        context.close();
    }

    function _run(ShieldedPoolLogic.Spend memory s, bytes memory payload) private returns (bool, bytes memory) {
        require(_settle(proxy, s), "fixture settlement failed");
        return _frame(address(pool), address(account), payload, 1_000_000);
    }

    function _assertRejected(bytes4 expected, bool ok, bytes memory ret) private view {
        // Only the four-byte revert selector is compared; arguments are intentionally discarded.
        // forge-lint: disable-next-line(unsafe-typecast)
        require(!ok && bytes4(ret) == expected, "wrong rejection");
        require(account.nonce() == 0 && target.calls() == 0, "unauthorized action changed state");
    }

    function test_success_claims_to_account_and_executes_once() public {
        ShieldedPoolLogic.Spend memory s = _spend(2 ether, address(account));
        s.outCm1 = bytes32(uint256(301));
        s.outCm2 = bytes32(uint256(302));
        (bool ok,) = _run(s, _signed(account, _action(s), OWNER_KEY));
        require(ok && account.nonce() == 1 && target.calls() == 1, "action missing");
        require(target.caller() == address(account) && target.marker() == 42, "wrong call");
        require(address(target).balance == 2 ether && address(account).balance == 0, "wrong payout");
        require(pool.withdrawalCredit(address(account)) == 0, "credit not claimed");
        require(pool.isLeaf(s.outCm1) && pool.isLeaf(s.outCm2), "settlement outputs missing");
    }

    function test_success_fits_three_hundred_thousand_forge_execution_cap() public {
        ShieldedPoolLogic.Spend memory s = _spend(2 ether, address(account));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        require(_settle(proxy, s));
        // Single EVM budget, including oracle calls. This does not establish
        // an EIP-8141 execution/state split or a universal downstream-call cap.
        (bool ok,) = _frame(address(pool), address(account), payload, 300_000);
        require(ok && account.nonce() == 1 && target.calls() == 1, "300k fixture cap exhausted");
        require(address(target).balance == 2 ether && pool.withdrawalCredit(address(account)) == 0);
    }

    function test_downstream_revert_restores_claim_and_nonce_but_preserves_settlement() public {
        ShieldedPoolLogic.Spend memory s = _spend(2 ether, address(account));
        s.outCm1 = bytes32(uint256(303));
        s.outCm2 = bytes32(uint256(304));
        RecipientPullAccount.Action memory a = _action(s);
        a.data = abi.encodeCall(RecipientPullTarget.fail, ());
        (bool ok, bytes memory ret) = _run(s, _signed(account, a, OWNER_KEY));
        _assertRejected(RecipientPullTarget.ActionFailed.selector, ok, ret);
        require(pool.withdrawalCredit(address(account)) == 2 ether, "claim did not roll back");
        require(address(account).balance == 0 && address(target).balance == 0, "value escaped");
        require(pool.isLeaf(s.outCm1) && pool.isLeaf(s.outCm2), "prior settlement rolled back");
        pool.claimWithdrawal(payable(address(account)));
        require(address(account).balance == 2 ether, "fallback claim unavailable");
    }

    function test_note_owner_cannot_authorize_another_recipients_action() public {
        require(_settle(proxy, _spend(4 ether, address(account))));
        context.close();
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        RecipientPullAccount.Action memory a = _action(s);
        a.value = 5 ether;
        (bool ok, bytes memory ret) = _run(s, _signed(account, a, NOTE_OWNER_KEY));
        _assertRejected(RecipientPullAccount.Unauthorized.selector, ok, ret);
        require(pool.withdrawalCredit(address(account)) == 5 ether, "victim credit changed");
    }

    function test_negative_control_entrypoint_caller_alone_lets_note_owner_spend_victim_credit() public {
        RecipientPullUnauthenticatedAccount victim = new RecipientPullUnauthenticatedAccount();
        address payable thief = payable(vm.addr(NOTE_OWNER_KEY));
        require(_settle(proxy, _spend(4 ether, address(victim))));
        require(_settle(proxy, _spend(1 ether, address(victim))));
        (bool ok,) = _frame(
            address(pool),
            address(victim),
            abi.encodeCall(RecipientPullUnauthenticatedAccount.execute, (pool, thief, 5 ether)),
            1_000_000
        );
        require(ok && thief.balance == 5 ether, "negative control did not expose missing authority");
    }

    function test_replay_same_authorization_rejects_even_with_successful_frame_context() public {
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        (bool ok,) = _run(s, payload);
        require(ok);
        // Deliberately keep the same successful context available, a stronger
        // replay opportunity than a separate transaction with spent note keys.
        context.open(address(pool), s, true, 3);
        bytes memory ret;
        (ok, ret) = _frame(address(pool), address(account), payload, 1_000_000);
        // Only the four-byte revert selector is compared; arguments are intentionally discarded.
        // forge-lint: disable-next-line(unsafe-typecast)
        require(!ok && bytes4(ret) == RecipientPullAccount.WrongNonce.selector, "replay accepted");
        require(target.calls() == 1 && account.nonce() == 1, "replay changed account");
    }

    function test_cross_account_signature_rejects_for_same_owner() public {
        RecipientPullAccount other = new RecipientPullAccount(vm.addr(OWNER_KEY), context);
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(other));
        RecipientPullAccount.Action memory a = _action(s);
        bytes memory payload = _signed(account, a, OWNER_KEY);
        require(_settle(proxy, s));
        (bool ok, bytes memory ret) = _frame(address(pool), address(other), payload, 1_000_000);
        // Only the four-byte revert selector is compared; arguments are intentionally discarded.
        // forge-lint: disable-next-line(unsafe-typecast)
        require(!ok && bytes4(ret) == RecipientPullAccount.Unauthorized.selector, "cross-account replay");
        require(other.nonce() == 0 && pool.withdrawalCredit(address(other)) == 1 ether, "other account changed");
    }

    function test_cross_pool_retargeted_action_rejects_signature() public {
        LogicProxy other = new LogicProxy(address(logic));
        vm.deal(address(other), 10 ether);
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        s.domain = IPool(address(other)).domain();
        RecipientPullAccount.Action memory a = _action(s);
        (uint8 v, bytes32 r, bytes32 sigS) = vm.sign(OWNER_KEY, account.digest(a));
        a.pool = address(other);
        require(_settle(other, s));
        (bool ok, bytes memory ret) = _frame(
            address(other), address(account), abi.encodeCall(RecipientPullAccount.execute, (a, v, r, sigS)), 1_000_000
        );
        _assertRejected(RecipientPullAccount.Unauthorized.selector, ok, ret);
        require(IPool(address(other)).withdrawalCredit(address(account)) == 1 ether, "other pool credit changed");
    }

    function test_cross_chain_signature_rejects() public {
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        require(_settle(proxy, s));
        vm.chainId(block.chainid + 1);
        (bool ok, bytes memory ret) = _frame(address(pool), address(account), payload, 1_000_000);
        _assertRejected(RecipientPullAccount.Unauthorized.selector, ok, ret);
    }

    function testFuzz_each_action_field_is_authenticated(uint8 field) public {
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        RecipientPullAccount.Action memory a = _action(s);
        (uint8 v, bytes32 r, bytes32 sigS) = vm.sign(OWNER_KEY, account.digest(a));
        uint8 selected = field % 4;
        if (selected == 0) a.target = address(0xCAFE);
        if (selected == 1) a.value++;
        if (selected == 2) a.data = abi.encodeCall(RecipientPullTarget.act, (43));
        if (selected == 3) a.callGas++;
        (bool ok, bytes memory ret) = _run(s, abi.encodeCall(RecipientPullAccount.execute, (a, v, r, sigS)));
        _assertRejected(RecipientPullAccount.Unauthorized.selector, ok, ret);
    }

    function test_different_settlement_cannot_reuse_action_authorization() public {
        ShieldedPoolLogic.Spend memory first = _spend(1 ether, address(account));
        bytes memory payload = _signed(account, _action(first), OWNER_KEY);
        ShieldedPoolLogic.Spend memory second = _spend(1 ether, address(account));
        (bool ok, bytes memory ret) = _run(second, payload);
        _assertRejected(RecipientPullAccount.WrongFrame.selector, ok, ret);
    }

    function test_retargeted_settlement_hash_invalidates_signature() public {
        ShieldedPoolLogic.Spend memory first = _spend(1 ether, address(account));
        RecipientPullAccount.Action memory a = _action(first);
        (uint8 v, bytes32 r, bytes32 sigS) = vm.sign(OWNER_KEY, account.digest(a));
        ShieldedPoolLogic.Spend memory second = _spend(1 ether, address(account));
        a.settlementHash = keccak256(abi.encode(second));
        (bool ok, bytes memory ret) = _run(second, abi.encodeCall(RecipientPullAccount.execute, (a, v, r, sigS)));
        _assertRejected(RecipientPullAccount.Unauthorized.selector, ok, ret);
    }

    function test_signed_wrong_nonce_rejects() public {
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        RecipientPullAccount.Action memory a = _action(s);
        a.nonce = 1;
        (bool ok, bytes memory ret) = _run(s, _signed(account, a, OWNER_KEY));
        _assertRejected(RecipientPullAccount.WrongNonce.selector, ok, ret);
    }

    function test_reentrant_action_cannot_execute_twice_or_claim_twice() public {
        RecipientPullReentrantTarget reentrant = new RecipientPullReentrantTarget();
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        RecipientPullAccount.Action memory a = _action(s);
        a.target = address(reentrant);
        a.data = abi.encodeCall(RecipientPullReentrantTarget.attack, ());
        bytes memory payload = _signed(account, a, OWNER_KEY);
        reentrant.configure(address(account), pool, payload);
        (bool ok,) = _run(s, payload);
        require(ok && reentrant.calls() == 1 && account.nonce() == 1, "reentrancy disrupted action");
        require(reentrant.accountError() == RecipientPullAccount.Reentrant.selector, "missing account guard");
        require(reentrant.claimError() == ShieldedPoolLogic.NoCredit.selector, "pool claim repeated");
        require(address(reentrant).balance == 1 ether && pool.withdrawalCredit(address(account)) == 0, "double payout");
    }

    function test_accumulated_credit_claims_all_but_spends_only_signed_value() public {
        require(_settle(proxy, _spend(3 ether, address(account))));
        context.close();
        vm.deal(address(account), 4 ether);
        ShieldedPoolLogic.Spend memory s = _spend(2 ether, address(account));
        (bool ok,) = _run(s, _signed(account, _action(s), OWNER_KEY));
        require(ok && address(target).balance == 2 ether, "wrong authorized spend");
        require(address(account).balance == 7 ether, "old credit or balance consumed");
        require(pool.withdrawalCredit(address(account)) == 0, "did not claim accumulated credit");
    }

    function test_prior_permissionless_claim_does_not_block_authorized_action() public {
        ShieldedPoolLogic.Spend memory s = _spend(2 ether, address(account));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        require(_settle(proxy, s));
        // Explicitly stress a stronger interleaving than contiguous frames
        // permit. Permissionless payout already delivered the funds to self.
        vm.prank(vm.addr(NOTE_OWNER_KEY));
        pool.claimWithdrawal(payable(address(account)));
        require(address(account).balance == 2 ether && pool.withdrawalCredit(address(account)) == 0);
        (bool ok,) = _frame(address(pool), address(account), payload, 1_000_000);
        require(ok && address(target).balance == 2 ether && account.nonce() == 1, "prior claim blocked action");
    }

    function test_failed_settlement_cannot_use_old_credit_or_balance() public {
        ShieldedPoolLogic.Spend memory prior = _spend(3 ether, address(account));
        prior.outCm1 = bytes32(uint256(501));
        prior.outCm2 = bytes32(uint256(502));
        require(_settle(proxy, prior));
        context.close();
        vm.deal(address(account), 4 ether);
        ShieldedPoolLogic.Spend memory s = _spend(2 ether, address(account));
        // Fresh note keys and canonical shape can pass envelope approval, but
        // a commitment collision remains a settlement-time failure.
        s.outCm1 = prior.outCm1;
        s.outCm2 = bytes32(uint256(503));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        require(!_settle(proxy, s), "invalid settlement unexpectedly succeeded");
        (bool ok, bytes memory ret) = _frame(address(pool), address(account), payload, 1_000_000);
        _assertRejected(RecipientPullAccount.SettlementFailed.selector, ok, ret);
        require(pool.withdrawalCredit(address(account)) == 3 ether, "old credit consumed");
        require(address(account).balance == 4 ether, "old account balance consumed");
    }

    function test_action_out_of_gas_restores_claim_and_nonce() public {
        ShieldedPoolLogic.Spend memory s = _spend(2 ether, address(account));
        RecipientPullAccount.Action memory a = _action(s);
        a.data = abi.encodeCall(RecipientPullTarget.exhaustGas, ());
        a.callGas = 30_000;
        (bool ok,) = _run(s, _signed(account, a, OWNER_KEY));
        require(!ok && account.nonce() == 0 && target.calls() == 0, "gas failure committed action");
        require(pool.withdrawalCredit(address(account)) == 2 ether, "gas failure lost credit");
        require(address(account).balance == 0 && address(target).balance == 0, "gas failure leaked funds");
    }

    function test_fourth_frame_out_of_gas_preserves_prior_settlement() public {
        ShieldedPoolLogic.Spend memory s = _spend(2 ether, address(account));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        require(_settle(proxy, s));
        (bool ok,) = _frame(address(pool), address(account), payload, 10_000);
        require(!ok && account.nonce() == 0 && target.calls() == 0, "small cap unexpectedly succeeded");
        require(pool.withdrawalCredit(address(account)) == 2 ether, "prior settlement lost");
    }

    function test_wrong_frame_index_rejects() public {
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        require(_settle(proxy, s));
        context.open(address(pool), s, true, 2);
        (bool ok, bytes memory ret) = _frame(address(pool), address(account), payload, 1_000_000);
        _assertRejected(RecipientPullAccount.WrongFrame.selector, ok, ret);
    }

    function test_wrong_transaction_sender_rejects() public {
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        require(_settle(proxy, s));
        (bool ok, bytes memory ret) = _frame(vm.addr(NOTE_OWNER_KEY), address(account), payload, 1_000_000);
        _assertRejected(RecipientPullAccount.WrongFrame.selector, ok, ret);
    }

    function test_wrong_frame_caller_rejects() public {
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        require(_settle(proxy, s));
        context.enterFrame(address(pool), address(account));
        vm.prank(vm.addr(NOTE_OWNER_KEY));
        (bool ok, bytes memory ret) = address(account).call(payload);
        context.close();
        _assertRejected(RecipientPullAccount.WrongFrame.selector, ok, ret);
    }

    function test_wrong_current_target_rejects_even_with_inherited_success_context() public {
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        require(_settle(proxy, s));
        context.enterFrame(address(pool), address(target));
        vm.prank(address(0xAA));
        (bool ok, bytes memory ret) = address(account).call(payload);
        context.close();
        _assertRejected(RecipientPullAccount.WrongFrame.selector, ok, ret);
    }

    function test_no_active_frame_rejects() public {
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(account));
        bytes memory payload = _signed(account, _action(s), OWNER_KEY);
        require(_settle(proxy, s));
        context.close();
        (bool ok, bytes memory ret) = _frame(address(pool), address(account), payload, 1_000_000);
        _assertRejected(RecipientPullAccount.WrongFrame.selector, ok, ret);
    }

    function test_settlement_for_another_recipient_rejects() public {
        ShieldedPoolLogic.Spend memory s = _spend(1 ether, address(0xCAFE));
        (bool ok, bytes memory ret) = _run(s, _signed(account, _action(s), OWNER_KEY));
        _assertRejected(RecipientPullAccount.WrongFrame.selector, ok, ret);
        require(pool.withdrawalCredit(address(0xCAFE)) == 1 ether, "other recipient credit lost");
    }
}
