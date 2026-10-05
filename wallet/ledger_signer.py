"""A spending key on a Ledger, through the RAILGUN Ledger app's BabyJubjub signer.

The RAILGUN app (github.com/Railgun-Community/ledger-client) derives a
BabyJubjub key per account index on the device and signs any field element
with circomlibjs's EdDSA-Poseidon, which the spend circuit verifies. The key
never leaves the device; wallet.build_witness hands this signer the spend's
message and gets back only a signature.

This is blind signing: the device shows the message, a Poseidon hash, not the
spend it authorizes. It keeps the key from malware on the host, but malware
that controls the host can still ask for a signature over a spend of its
choosing. Clear signing needs a device app that recomputes the statement from
its values and shows them.

Use an account index that no RAILGUN wallet uses, so this pool's key is not
also a RAILGUN spending key. That does not stop host malware, which can ask
the app to sign under any account. The wire format follows ledger-client
v0.4.1 (c19dd76):

  GET_PUBLIC_KEY  E0 01 01 00 | account u32 BE        -> Ax || Ay (32 bytes BE each)
  SIGN_HASH       E0 12 00 00 | account u32 BE | M (32 bytes LE)
                  -> prefix (1) || R8x || R8y || S (32 bytes BE each) [|| M echoed]

The prefix is the signature's length, 0x60; like ledger-client's own parser,
this adapter does not check it, since the signature itself is verified.

Not yet tested against a device, only against the simulated app in
test_ledger_signer.py.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "reference"))
import babyjubjub as bjj  # noqa: E402
from poseidon_bn254 import P  # noqa: E402

CLA, INS_GET_PUBLIC_KEY, INS_SIGN_HASH = 0xE0, 0x01, 0x12


class DeviceError(Exception):
    """The device's answer is malformed or not a valid key or signature."""


def apdu(ins, p1, data):
    return bytes([CLA, ins, p1, 0, len(data)]) + data


class RailgunLedgerSigner:
    """The wallet's signer interface over a Ledger: `public_key` and
    `sign(message)`. `exchange` sends one APDU and returns the response data,
    raising on an error status, as ledgerblue's `Dongle.exchange` does."""

    def __init__(self, exchange, account):
        if not 0 <= account < 1 << 32:
            raise ValueError("account must be a 32-bit index")
        self.exchange = exchange
        self.account = account.to_bytes(4, "big")
        data = exchange(apdu(INS_GET_PUBLIC_KEY, 0x01, self.account))
        if len(data) != 64:
            raise DeviceError(f"public key response has {len(data)} bytes, not 64")
        pub = (int.from_bytes(data[:32], "big"), int.from_bytes(data[32:], "big"))
        # The circuit only needs 8*A to be a generator, but a device key outside
        # the prime-order subgroup means the app is not the one described above.
        if not bjj.on_curve(pub) or bjj.mul(pub, bjj.L) != bjj.IDENTITY or pub == bjj.IDENTITY:
            raise DeviceError("device public key is not a point of the prime-order subgroup")
        self.public_key = pub

    @classmethod
    def connect(cls, account):
        """The first Ledger ledgerblue finds, with the RAILGUN app open."""
        from ledgerblue.comm import getDongle  # optional: pip install ledgerblue
        return cls(getDongle().exchange, account)

    def sign(self, message):
        if not 0 <= message < P:
            raise ValueError("message must be a field element")
        sent = message.to_bytes(32, "little")
        data = self.exchange(apdu(INS_SIGN_HASH, 0, self.account + sent))
        if len(data) not in (97, 129):
            raise DeviceError(f"signature response has {len(data)} bytes, not 97 or 129")
        if len(data) == 129 and data[97:] != sent:
            raise DeviceError("device signed another message than the one sent")
        r8x, r8y, s = (int.from_bytes(data[1 + 32 * i:33 + 32 * i], "big") for i in range(3))
        # wallet.sign_witness verifies the signature itself; this names the fault.
        if not bjj.verify(self.public_key, message, (r8x, r8y, s)):
            raise DeviceError("device signature does not verify under its own public key")
        return r8x, r8y, s
