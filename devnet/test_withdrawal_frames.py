#!/usr/bin/env python3
"""Wallet shape, authorization binding, and per-frame outcome regressions."""
import contextlib
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from eth_keys import keys

import pool_frametx as wallet
from frametx import FrameTx
from gas_profile import (
    CLAIM_FRAME_GAS, CLAIM_FRAME_STATE_GAS, POOL_PROFILE,
    RECIPIENT_FRAME_MAX_DATA, RECIPIENT_FRAME_MAX_GAS, RECIPIENT_FRAME_MAX_STATE_GAS,
)

FIXTURE = Path(__file__).resolve().parent.parent / "wallet" / "smoke_fixture.json"


class WithdrawalFramesTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = json.loads(FIXTURE.read_text())
        cls.pool = int(cls.fixture["pool_address"], 16)
        cls.entries = {}
        cls.calldata = {}
        for name in ("transfer", "withdraw"):
            entry = copy.deepcopy(cls.fixture[name])
            entry["root_slot"] = "1"
            cls.entries[name] = entry
            cls.calldata[name] = wallet.cast_calldata(f"settle({wallet.SPEND_TUPLE})", wallet.spend_args(entry))

    def _tail(self, **options):
        return wallet.withdrawal_frame(self.pool, self.calldata["withdraw"], **options)

    def _run(self, name="withdraw", simulation="auto", receipt=None, dry_run=True, **options):
        entry = self.entries[name]
        pk = keys.PrivateKey(bytes.fromhex(entry["authorizer_private_key"][2:]))
        self.calls = []
        self.built = []

        def create_tx(**arguments):
            tx = FrameTx(**arguments)
            self.built.append(tx)
            return tx

        def rpc(_url, method, params):
            self.calls.append((method, params))
            if method == "eth_chainId":
                return hex(int(self.fixture["chain_id"]))
            if method == "eth_getTransactionCount":
                return "0x0"
            if method == "eth_getBlockByNumber":
                return {"baseFeePerGas": "0x1"}
            if method == "eth_sendRawTransaction":
                return "0x" + "12" * 32
            if method == "eth_getTransactionReceipt":
                return receipt
            raise AssertionError(method)

        def simulate(_url, raw):
            self.assertEqual(raw, "0x" + self.built[-1].raw().hex())
            if simulation != "auto":
                return simulation
            return {"valid": True, "executionStatus": "success", "gasUsed": "0x100",
                    "frames": [{"succeeded": True, "gasUsed": "0x40"} for _ in self.built[-1].frames]}

        with patch.object(wallet, "rpc", side_effect=rpc), patch.object(wallet, "simulate", side_effect=simulate), \
             patch.object(wallet, "FrameTx", side_effect=create_tx), contextlib.redirect_stdout(io.StringIO()):
            result = wallet.build_and_send(
                "mock://rpc", pk, self.pool, 0, self.calldata[name],
                protocol_nonces=sorted([int(entry["nf1"], 16), int(entry["nf2"], 16)]),
                proof_verify=True, recent_root=b"\x01" * 72, sender_override=self.pool,
                frame0_data=wallet.proof_bytes(entry), dry_run=dry_run, **options)
        return self.built[-1], result

    @staticmethod
    def _simulation(statuses):
        return {"valid": True, "executionStatus": "success" if all(statuses) else "reverted",
                "frames": [{"succeeded": success, "gasUsed": "0x10"} for success in statuses]}

    @staticmethod
    def _receipt(statuses):
        return {"status": "0x1" if all(s == "0x1" for s in statuses) else "0x0",
                "blockNumber": "0x1", "gasUsed": "0x100", "type": "0x6",
                "frameReceipts": [{"status": status} for status in statuses]}

    def test_private_transfer_has_three_frames(self):
        tx, _ = self._run("transfer")
        self.assertEqual(len(tx.frames), 3)
        self.assertEqual([frame.mode for frame in tx.frames], [1, 1, 2])

    def test_public_withdrawal_defaults_to_exact_pool_claim(self):
        tx, _ = self._run()
        self.assertEqual(len(tx.frames), 4)
        tail = tx.frames[3]
        recipient = int(self.entries["withdraw"]["recipient"], 16)
        self.assertEqual((tail.mode, tail.flags, tail.target, tail.value), (0, 0, self.pool, 0))
        self.assertEqual((tail.gas_limit, tail.state_limit), (CLAIM_FRAME_GAS, CLAIM_FRAME_STATE_GAS))
        self.assertEqual(tail.data, wallet.cast_calldata("claimWithdrawal(address)", f"0x{recipient:040x}"))

    def test_recipient_call_target_comes_from_settlement(self):
        tx, _ = self._run(recipient_call=b"account-signature", recipient_gas=123_456, recipient_state_gas=234_567)
        tail = tx.frames[3]
        self.assertEqual((tail.mode, tail.flags, tail.value), (0, 0, 0))
        self.assertEqual(tail.target, int(self.entries["withdraw"]["recipient"], 16))
        self.assertEqual((tail.gas_limit, tail.state_limit), (123_456, 234_567))
        self.assertEqual(tail.data, b"account-signature")
        changed = bytearray(self.calldata["withdraw"])
        changed[4 + 10 * 32:4 + 11 * 32] = (0xCAFE).to_bytes(32, "big")
        derived = wallet.withdrawal_frame(self.pool, bytes(changed), recipient_call=b"account-signature")
        self.assertEqual(derived.target, 0xCAFE)

    def test_maximum_recipient_limits_and_data_are_accepted(self):
        tail = self._tail(recipient_call=b"\x00" * RECIPIENT_FRAME_MAX_DATA)
        self.assertEqual((tail.gas_limit, tail.state_limit), (RECIPIENT_FRAME_MAX_GAS, RECIPIENT_FRAME_MAX_STATE_GAS))
        self.assertEqual(len(tail.data), RECIPIENT_FRAME_MAX_DATA)

    def test_empty_oversized_and_nonbytes_calldata_are_rejected(self):
        for data in (b"", b"x" * (RECIPIENT_FRAME_MAX_DATA + 1), "0x1234"):
            with self.subTest(data_length=len(data)), self.assertRaises(ValueError):
                self._tail(recipient_call=data)

    def test_zero_negative_and_oversized_budgets_are_rejected(self):
        for option, bound in (("recipient_gas", RECIPIENT_FRAME_MAX_GAS),
                              ("recipient_state_gas", RECIPIENT_FRAME_MAX_STATE_GAS)):
            for value in (0, -1, bound + 1):
                with self.subTest(option=option, value=value), self.assertRaises(ValueError):
                    self._tail(recipient_call=b"x", **{option: value})

    def test_budget_overrides_need_explicit_recipient_calldata(self):
        for option in ("recipient_gas", "recipient_state_gas"):
            with self.subTest(option=option), self.assertRaisesRegex(ValueError, "require --recipient-call"):
                self._tail(**{option: 1})

    def test_private_transfer_cannot_have_recipient_options(self):
        with self.assertRaisesRegex(ValueError, "public withdrawal"):
            wallet.withdrawal_frame(self.pool, self.calldata["transfer"], recipient_call=b"x")

    def test_malformed_settlement_is_rejected(self):
        data = self.calldata["withdraw"]
        for malformed in (data[:-1], data + b"x", b"\x00" * 4 + data[4:]):
            with self.subTest(length=len(malformed)), self.assertRaises(ValueError):
                wallet.withdrawal_frame(self.pool, malformed)

    def test_zero_and_noncanonical_recipient_are_rejected(self):
        for recipient in (0, 1 << 160):
            changed = bytearray(self.calldata["withdraw"])
            changed[4 + 10 * 32:4 + 11 * 32] = recipient.to_bytes(32, "big")
            with self.subTest(recipient=recipient), self.assertRaises(ValueError):
                wallet.withdrawal_frame(self.pool, bytes(changed))

    def test_recipient_option_parser_requires_values_and_calldata(self):
        for arguments in (["--recipient-call"], ["--recipient-call", "--recipient-gas", "1"],
                          ["--recipient-call", "0xzz"], ["--recipient-gas", "1"],
                          ["--recipient-call", "0x12", "--recipient-state-gas", "bad"]):
            with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                wallet.recipient_options(arguments)
        self.assertEqual(wallet.recipient_options(["--recipient-call", "0x1234", "--recipient-gas", "0x64"]),
                         {"recipient_call": b"\x12\x34", "recipient_gas": 100})

    def test_actual_builder_signs_every_tail_field_and_frame_count(self):
        for options in ({}, {"recipient_call": b"owner-signed-action"}):
            tx, _ = self._run(**options)
            encoded = tx.signatures[0].signature
            signature = keys.Signature(vrs=(encoded[0], int.from_bytes(encoded[1:33], "big"),
                                            int.from_bytes(encoded[33:65], "big")))
            expected = tx.signatures[0].signer.to_bytes(20, "big")
            self.assertEqual(signature.recover_public_key_from_msg_hash(tx.sig_hash()).to_canonical_address(), expected)
            for field in ("mode", "flags", "target", "gas_limit", "state_limit", "value", "data"):
                candidate = copy.deepcopy(tx)
                value = getattr(candidate.frames[3], field)
                setattr(candidate.frames[3], field, value + b"x" if field == "data" else value + 1)
                recovered = signature.recover_public_key_from_msg_hash(candidate.sig_hash()).to_canonical_address()
                self.assertNotEqual(recovered, expected, field)
            for count in (3, 5):
                candidate = copy.deepcopy(tx)
                candidate.frames = candidate.frames[:3] if count == 3 else candidate.frames + [candidate.frames[3]]
                self.assertNotEqual(signature.recover_public_key_from_msg_hash(candidate.sig_hash()).to_canonical_address(), expected)

    def test_preflight_refuses_failed_tail_without_claiming_settlement_failed(self):
        with self.assertRaisesRegex(SystemExit, "settlement succeeded.*another frame failed"):
            self._run(simulation=self._simulation([True, True, True, False]), dry_run=False)
        self.assertNotIn("eth_sendRawTransaction", [method for method, _ in self.calls])

    def test_preflight_refuses_failed_settlement_even_if_tail_succeeded(self):
        with self.assertRaisesRegex(SystemExit, "settlement frame 2 did not explicitly succeed"):
            self._run(simulation=self._simulation([True, True, False, True]), dry_run=False)
        self.assertNotIn("eth_sendRawTransaction", [method for method, _ in self.calls])

    def test_preflight_requires_explicit_per_frame_success(self):
        for simulation in ({"valid": True, "executionStatus": "success"},
                           self._simulation([True, True]),
                           {"valid": True, "executionStatus": "success", "frames": [{}, {}, {}, {}]}):
            with self.subTest(simulation=simulation), self.assertRaisesRegex(SystemExit, "did not explicitly succeed"):
                self._run(simulation=simulation, dry_run=False)
            self.assertNotIn("eth_sendRawTransaction", [method for method, _ in self.calls])

    def test_failed_mined_tail_is_recoverable_after_successful_settlement(self):
        with self.assertRaisesRegex(SystemExit, "settlement succeeded.*withdrawal frame failed.*recoverable") as error:
            self._run(receipt=self._receipt(["0x1", "0x1", "0x1", "0x0"]), dry_run=False)
        self.assertNotIn("burned", str(error.exception))

    def test_missing_execution_summary_refuses_without_sending(self):
        simulation = self._simulation([True, True, True, True])
        del simulation["executionStatus"]
        with self.assertRaisesRegex(SystemExit, "execution did not succeed.*outcome unavailable"):
            self._run(simulation=simulation, dry_run=False)
        self.assertNotIn("eth_sendRawTransaction", [method for method, _ in self.calls])

    def test_failed_mined_settlement_is_distinguished_from_tail_failure(self):
        with self.assertRaisesRegex(SystemExit, "settlement frame did not succeed.*nullifiers may have been consumed"):
            self._run(receipt=self._receipt(["0x1", "0x1", "0x0", "0x1"]), dry_run=False)

    def test_missing_mined_frame_outcome_is_unknown(self):
        receipt = self._receipt(["0x1", "0x1", "0x1", "0x1"])
        del receipt["frameReceipts"]
        with self.assertRaisesRegex(SystemExit, "settlement outcome unavailable"):
            self._run(receipt=receipt, dry_run=False)

    def test_missing_or_unknown_tail_does_not_claim_credit_is_recoverable(self):
        for statuses in (["0x1", "0x1", "0x1"], ["0x1", "0x1", "0x1", None]):
            with self.subTest(statuses=statuses), \
                 self.assertRaisesRegex(SystemExit, "settlement succeeded.*later frame outcome is unknown") as error:
                self._run(receipt=self._receipt(statuses), dry_run=False)
            self.assertNotIn("remains recoverable", str(error.exception))

    def test_successful_mined_withdrawal_returns_receipt(self):
        receipt = self._receipt(["0x1", "0x1", "0x1", "0x1"])
        _, result = self._run(receipt=receipt, dry_run=False)
        self.assertEqual(result, receipt)

    def test_cli_refuses_historical_or_unknown_pool_profile(self):
        for profile in (None, "old-three-frame-pool"):
            with tempfile.TemporaryDirectory() as directory:
                config = Path(directory) / "config.json"
                config.write_text(json.dumps({"pool": hex(self.pool), "poolProfile": profile}))
                argv = ["pool_frametx.py", "mock://rpc", str(config), str(FIXTURE), "withdraw", "unused"]
                with patch.object(wallet.sys, "argv", argv), patch.object(wallet, "rpc") as rpc, \
                     self.assertRaisesRegex(SystemExit, f"poolProfile={POOL_PROFILE}.*fresh deployment"):
                    wallet.main()
                rpc.assert_not_called()


if __name__ == "__main__":
    unittest.main()
