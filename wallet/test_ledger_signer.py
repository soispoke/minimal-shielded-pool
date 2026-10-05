"""Ledger signer checks against a simulated RAILGUN app. Run: python3 wallet/test_ledger_signer.py

The simulation holds a software key and answers APDUs in the wire format
ledger_signer.py documents. It shows that the adapter encodes requests and
decodes answers consistently with that format, and that it refuses malformed
or wrong answers; it cannot show that the real app matches the format.
"""
import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import gen_smoke
import ledger_signer as ls
import wallet as w
from poseidon_bn254 import hex32

bjj = w.bjj


class SimulatedApp:
    """The RAILGUN app's GET_PUBLIC_KEY and SIGN_HASH over one account's key."""

    def __init__(self, secret, account, echo=True, tamper=None):
        self.secret, self.account, self.echo, self.tamper = secret, account, echo, tamper
        self.sent = []

    def exchange(self, request):
        self.sent.append(request)
        cla, ins, p1, p2, length = request[:5]
        data = request[5:]
        assert (cla, p2, length) == (ls.CLA, 0, len(data)), request.hex()
        assert int.from_bytes(data[:4], "big") == self.account
        if ins == ls.INS_GET_PUBLIC_KEY:
            assert p1 == 1
            x, y = bjj.public_key(self.secret) if self.tamper != "key" else (1, 1)
            return x.to_bytes(32, "big") + y.to_bytes(32, "big")
        assert ins == ls.INS_SIGN_HASH and p1 == 0 and len(data) == 36
        message = int.from_bytes(data[4:], "little")
        if self.tamper == "message":
            message += 1
        r8x, r8y, s = bjj.sign(self.secret, message)
        echoed = data[4:] if self.tamper != "echo" else bytes(32)
        return (b"\x00" + b"".join(v.to_bytes(32, "big") for v in (r8x, r8y, s))
                + (echoed if self.echo else b""))


class LedgerSignerTest(unittest.TestCase):
    SECRET, ACCOUNT = 0xC0FFEE, 7

    def signer(self, **kwargs):
        app = SimulatedApp(self.SECRET, self.ACCOUNT, **kwargs)
        return ls.RailgunLedgerSigner(app.exchange, self.ACCOUNT), app

    def test_signs_the_message_the_circuit_checks(self):
        """The device signs the spend's auth message, and the signature passes
        the reference verifier, which mirrors the circuit's checks."""
        signer, app = self.signer()
        self.assertEqual(signer.public_key, bjj.public_key(self.SECRET))
        w.set_seed(3)
        nk, rho = w.new_note()
        tree = w.Tree()
        tree.append(w.commitment(signer.public_key, nk, rho, 100))
        witness = w.build_witness(tree, [{"nk": nk, "rho": rho, "value": 100, "idx": 0}, w.dummy_input()],
                                  w.sink_outputs(), 5, signer=signer, authorizer=1,
                                  public_amount=100, recipient="0x" + "34" * 20)
        message = w.auth_message(w.witness_statement(witness))
        self.assertEqual(app.sent[-1][-32:], message.to_bytes(32, "little"))
        self.assertTrue(bjj.verify(signer.public_key, message,
                                   tuple(int(witness[k]) for k in ("R8x", "R8y", "S"))))

    def test_response_without_echo(self):
        signer, _ = self.signer(echo=False)
        self.assertTrue(bjj.verify(signer.public_key, 42, signer.sign(42)))

    def test_refuses_wrong_answers(self):
        with self.assertRaisesRegex(ls.DeviceError, "prime-order subgroup"):
            self.signer(tamper="key")
        signer, _ = self.signer(tamper="echo")
        with self.assertRaisesRegex(ls.DeviceError, "another message"):
            signer.sign(42)
        signer, _ = self.signer(tamper="message", echo=False)
        with self.assertRaisesRegex(ls.DeviceError, "does not verify"):
            signer.sign(42)
        with self.assertRaisesRegex(ls.DeviceError, "bytes, not 64"):
            ls.RailgunLedgerSigner(lambda _: b"\x00" * 63, self.ACCOUNT)

    def test_fixture_keeps_only_the_device_public_key(self):
        """gen_smoke --ledger-account proves Alice's two spends with the device's
        signatures, records no secret of hers, and asks the device for nothing else."""
        app = SimulatedApp(self.SECRET, self.ACCOUNT)
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "fixture.json"
            argv = ["gen_smoke.py", f"--ledger-account={self.ACCOUNT}", f"--output={out}"]
            connect = staticmethod(lambda account: ls.RailgunLedgerSigner(app.exchange, account))
            with mock.patch.object(sys, "argv", argv), \
                    mock.patch.object(ls.RailgunLedgerSigner, "connect", connect), \
                    contextlib.redirect_stdout(io.StringIO()):
                gen_smoke.main()
            fixture = json.loads(out.read_text())
        pub = [hex32(c) for c in bjj.public_key(self.SECRET)]
        for name in ("transfer", "withdraw_seed"):
            self.assertEqual((fixture[name]["spend_pub"], fixture[name]["ledger_account"]),
                             (pub, self.ACCOUNT), name)
            self.assertNotIn("spend_key", fixture[name])
        self.assertIn("spend_key", fixture["withdraw"])  # Bob's software key
        self.assertEqual(sum(r[1] == ls.INS_SIGN_HASH for r in app.sent), 2)

    def test_device_refusal_propagates(self):
        def refuse(_):
            raise RuntimeError("0x6985: denied on the device")
        with self.assertRaisesRegex(RuntimeError, "denied"):
            ls.RailgunLedgerSigner(refuse, self.ACCOUNT)


if __name__ == "__main__":
    unittest.main()
