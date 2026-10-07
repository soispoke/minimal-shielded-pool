#!/usr/bin/env python3
"""Harden snarkjs's generated verifier for the restricted VERIFY prefix.

The Hegotá validation observer bans the GAS opcode. snarkjs emits
`staticcall(sub(gas(), 2000), ...)` for ECADD, ECMUL, and pairing. Replace all
three with a fixed request; EIP-150 still caps it to 63/64 of remaining gas.
It also rejects noncanonical BN254 point-coordinate aliases and infinity
encodings before the pairing precompile. Fail closed if a future snarkjs output
changes shape.
"""
from pathlib import Path

VERIFIER = Path(__file__).parent.parent / "core" / "contracts" / "src" / "Groth16Verifier.sol"
NEEDLE = "staticcall(sub(gas(), 2000),"
REPLACEMENT = "staticcall(500000,"
MARKER = "// CANONICAL_PROOF_COORDINATES"
# The memory prologue snarkjs emits; the guard goes right before it.
PROLOGUE = """\
            let pMem := mload(0x40)
            mstore(0x40, add(pMem, pLastMem))
"""
GUARD = """\
            // CANONICAL_PROOF_COORDINATES: the pairing precompile accepts
            // field elements, but a proof has one canonical uint256 encoding.
            // Reject aliases such as pA.y + q and reject infinity points.
            function checkCoordinate(v) {
                if iszero(lt(v, q)) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }
            let ax := calldataload(_pA)
            let ay := calldataload(add(_pA, 32))
            let bx0 := calldataload(_pB)
            let bx1 := calldataload(add(_pB, 32))
            let by0 := calldataload(add(_pB, 64))
            let by1 := calldataload(add(_pB, 96))
            let cx := calldataload(_pC)
            let cy := calldataload(add(_pC, 32))
            checkCoordinate(ax)
            checkCoordinate(ay)
            checkCoordinate(bx0)
            checkCoordinate(bx1)
            checkCoordinate(by0)
            checkCoordinate(by1)
            checkCoordinate(cx)
            checkCoordinate(cy)
            if iszero(or(ax, ay)) { mstore(0, 0) return(0, 0x20) }
            if iszero(or(or(bx0, bx1), or(by0, by1))) { mstore(0, 0) return(0, 0x20) }
            if iszero(or(cx, cy)) { mstore(0, 0) return(0, 0x20) }

"""


def main():
    source = VERIFIER.read_text()
    count = source.count(NEEDLE)
    if count == 3:
        source = source.replace(NEEDLE, REPLACEMENT)
        print("patched 3 verifier precompile calls to fixed gas")
    elif count == 0 and source.count(REPLACEMENT) == 3:
        print("verifier already uses 3 fixed-gas precompile calls")
    else:
        raise SystemExit(f"expected 3 snarkjs GAS calls, found {count}; inspect generated verifier")

    if MARKER not in source:
        if source.count(PROLOGUE) != 1:
            raise SystemExit("generated verifier memory prologue changed; inspect before hardening")
        source = source.replace(PROLOGUE, GUARD + PROLOGUE)
        print("added canonical BN254 coordinate and infinity checks")
    else:
        print("verifier already has canonical proof-coordinate checks")

    VERIFIER.write_text(source)


if __name__ == "__main__":
    main()
