// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.24;

import {Poseidon16} from "../src/Poseidon16.sol";

/// Minimal cheatcode surface (no forge-std dependency).
interface Vm {
    function readFile(string calldata) external view returns (string memory);
    function parseJsonUintArray(string calldata, string calldata) external pure returns (uint256[] memory);
    function toString(uint256) external pure returns (string memory);
}

/// Differential tests against vectors exported from leanVM commit 12e6151
/// (vectors/poseidon16_vectors.json, see vectors/README.md). Every permute and
/// compress vector, the pool's tagged owner_pk/cm/nf/claim chain, the canonical
/// digest packing, and a soundness check that a single flipped input lane
/// changes the output.
contract Poseidon16VectorsTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    string constant PATH = "vectors/poseidon16_vectors.json";

    function _arr16(string memory json, string memory key) internal pure returns (uint256[16] memory out) {
        uint256[] memory v = vm.parseJsonUintArray(json, key);
        require(v.length == 16, "vector is not 16 wide");
        for (uint256 i = 0; i < 16; i++) out[i] = v[i];
    }

    function _arr8(string memory json, string memory key) internal pure returns (uint256[8] memory out) {
        uint256[] memory v = vm.parseJsonUintArray(json, key);
        require(v.length == 8, "vector is not 8 wide");
        for (uint256 i = 0; i < 8; i++) out[i] = v[i];
    }

    function _eq8(uint256[8] memory a, uint256[8] memory b) internal pure returns (bool) {
        for (uint256 i = 0; i < 8; i++) if (a[i] != b[i]) return false;
        return true;
    }

    function test_permute_vectors() external view {
        string memory json = vm.readFile(PATH);
        for (uint256 k = 0; k < 32; k++) {
            string memory idx = vm.toString(k);
            uint256[16] memory input = _arr16(json, string.concat(".permute[", idx, "].in"));
            uint256[16] memory expected = _arr16(json, string.concat(".permute[", idx, "].out"));
            uint256[16] memory got = Poseidon16.permute(input);
            for (uint256 i = 0; i < 16; i++) {
                require(got[i] == expected[i], string.concat("permute mismatch at vector ", idx));
            }
        }
    }

    function test_compress_vectors() external view {
        string memory json = vm.readFile(PATH);
        for (uint256 k = 0; k < 32; k++) {
            string memory idx = vm.toString(k);
            uint256[16] memory input = _arr16(json, string.concat(".compress[", idx, "].in"));
            uint256[8] memory expected = _arr8(json, string.concat(".compress[", idx, "].out"));
            require(_eq8(Poseidon16.compress(input), expected),
                    string.concat("compress mismatch at vector ", idx));
        }
    }

    /// The pool's spend chain, end to end: owner_pk, cm, nf, claim (the exact
    /// values the leanVM circuit computes for the same seeded secrets).
    function test_pool_chain() external view {
        string memory json = vm.readFile(PATH);
        uint256[8] memory spendKey = _arr8(json, ".pool_chain.spend_key");
        uint256[8] memory rho = _arr8(json, ".pool_chain.rho");
        uint256[8] memory root = _arr8(json, ".pool_chain.root");
        uint256[8] memory outCm = _arr8(json, ".pool_chain.out_cm");
        uint256[8] memory ctx = _arr8(json, ".pool_chain.ctx");
        uint256[8] memory zero8;

        uint256[8] memory ownerPk = Poseidon16.tagged(1, spendKey, zero8);
        require(_eq8(ownerPk, _arr8(json, ".pool_chain.owner_pk")), "owner_pk mismatch");
        uint256[8] memory cm = Poseidon16.tagged(2, ownerPk, rho);
        require(_eq8(cm, _arr8(json, ".pool_chain.cm")), "cm mismatch");
        uint256[8] memory nf = Poseidon16.tagged(3, spendKey, cm);
        require(_eq8(nf, _arr8(json, ".pool_chain.nf")), "nf mismatch");
        uint256[8] memory claim = Poseidon16.tagged(
            4, Poseidon16.compressPair(root, nf), Poseidon16.compressPair(outCm, ctx));
        require(_eq8(claim, _arr8(json, ".pool_chain.claim")), "claim mismatch");
    }

    function test_pack_unpack_roundtrip() external view {
        string memory json = vm.readFile(PATH);
        uint256[8] memory claim = _arr8(json, ".pool_chain.claim");
        bytes32 packed = Poseidon16.packDigest(claim);
        require(_eq8(Poseidon16.unpackDigest(packed), claim), "pack/unpack roundtrip");
        // the top bit of every 32-bit word is zero for canonical digests
        require(uint256(packed) & (uint256(0x80000000) << 224) == 0, "top bit set");
    }

    /// A single flipped lane must change the compression (smoke soundness).
    function test_flip_changes_output() external view {
        string memory json = vm.readFile(PATH);
        uint256[16] memory input = _arr16(json, ".compress[3].in");
        uint256[8] memory base = Poseidon16.compress(input);
        for (uint256 i = 0; i < 16; i++) {
            uint256[16] memory mutated = input;
            mutated[i] = (mutated[i] + 1) % Poseidon16.P;
            require(!_eq8(Poseidon16.compress(mutated), base), "flip did not change output");
        }
    }

    /// Gas ceiling: keep the naive implementation honest about its cost.
    function test_gas_compress_under_ceiling() external view {
        string memory json = vm.readFile(PATH);
        uint256[16] memory input = _arr16(json, ".compress[0].in");
        uint256 g0 = gasleft();
        Poseidon16.compress(input);
        uint256 used = g0 - gasleft();
        require(used < 200_000, "compress gas regression (>= 200k)");
    }
}

/// External wrapper so `forge test --gas-report` prices the primitives, and so
/// the non-canonical unpack revert can be exercised through an external call.
contract Poseidon16Harness {
    function compress(uint256[16] calldata x) external pure returns (uint256[8] memory) {
        return Poseidon16.compress(x);
    }

    function compressPair(uint256[8] calldata a, uint256[8] calldata b)
        external pure returns (uint256[8] memory)
    {
        return Poseidon16.compressPair(a, b);
    }

    function unpack(bytes32 b) external pure returns (uint256[8] memory) {
        return Poseidon16.unpackDigest(b);
    }
}

contract Poseidon16HarnessTest {
    function test_unpack_rejects_noncanonical_word() external {
        Poseidon16Harness h = new Poseidon16Harness();
        bytes32 bad = bytes32(uint256(2130706433) << 224); // word 0 == P
        (bool ok, ) = address(h).call(abi.encodeCall(h.unpack, (bad)));
        require(!ok, "non-canonical digest was accepted");
        bytes32 good = bytes32(uint256(2130706432) << 224); // word 0 == P - 1
        (ok, ) = address(h).call(abi.encodeCall(h.unpack, (good)));
        require(ok, "canonical digest was rejected");
    }
}
