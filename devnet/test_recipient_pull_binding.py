#!/usr/bin/env python3
"""Complete tail-signature binding; these vectors do not establish proof validity."""
import copy
import json

from eth_keys import keys
from test_pool_envelope_binding import build


def main():
    count = 0
    for options in ({}, {"recipient_call": b"account-request-and-owner-signature"}):
        tx, authorizer = build("withdraw", **options)
        original_hash = tx.sig_hash()
        encoded = tx.signatures[0].signature
        sig = keys.Signature(vrs=(encoded[0], int.from_bytes(encoded[1:33], "big"),
                                  int.from_bytes(encoded[33:65], "big")))
        tail = tx.frames[3]
        mutations = []
        for field, value in (("target", tail.target ^ 1), ("mode", 2), ("flags", 4),
                             ("gas_limit", tail.gas_limit + 1),
                             ("state_limit", tail.state_limit + 1), ("value", 1),
                             ("data", tail.data + b"changed")):
            candidate = copy.deepcopy(tx)
            setattr(candidate.frames[3], field, value)
            mutations.append((field, candidate))
        candidate = copy.deepcopy(tx)
        candidate.frames.pop()
        mutations.append(("remove-tail", candidate))
        candidate = copy.deepcopy(tx)
        candidate.frames.append(copy.deepcopy(candidate.frames[3]))
        mutations.append(("extra-tail", candidate))
        for name, candidate in mutations:
            assert candidate.sig_hash() != original_hash, name
            recovered = sig.recover_public_key_from_msg_hash(candidate.sig_hash()).to_canonical_address()
            assert recovered != authorizer.to_bytes(20, "big"), name
        count += len(mutations)
    print(json.dumps({"tail_mutations_rejected_by_signature": count, "withdrawal_profiles": 2,
                      "scope": "canonical hash and ECDSA, not dispatcher or proof validity"}, sort_keys=True))


if __name__ == "__main__":
    main()
