// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.24;

interface EnvelopeVm {
    function readFile(string calldata) external view returns (string memory);
    function parseBytes(string calldata) external pure returns (bytes memory);
    function store(address, bytes32, bytes32) external;
    function load(address, bytes32) external view returns (bytes32);
}

// Proof validity is independently tested by the repository's verifier vectors.
// This fixture isolates the unchanged proof encoding and candidate envelope gates.
contract EnvelopeVerifier {
    fallback() external {
        assembly {
            mstore(0, 1)
            return(0, 32)
        }
    }
}

contract RecipientPullEnvelopeTest {
    EnvelopeVm constant vm = EnvelopeVm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    bytes32 constant TAG = 0x40752e102d2a749c61d42a71e297edd3b493de639003b9480a700d589d98065b;
    address probe;
    uint256 constant RECIPIENT = 0xb0b;
    bytes proof;

    function _store(uint256 slot, uint256 value) internal {
        vm.store(probe, bytes32(slot), bytes32(value));
    }

    function _tx(uint256 p, uint256 v) internal {
        _store(0x1000 + p, v);
    }

    function _frame(uint256 i, uint256 p, uint256 v) internal {
        _store(0x2000 + i * 0x100 + p, v);
    }

    function _data(uint256 i, uint256 o, uint256 v) internal {
        _store(0x3000 + i * 0x1000 + o, v);
    }

    function setUp() public {
        bytes memory init = abi.encodePacked(
            vm.parseBytes(vm.readFile("../devnet/build/recipient_pull_probe.hex")),
            bytes32(uint256(1)),
            bytes32(uint256(uint160(address(new EnvelopeVerifier()))))
        );
        assembly { sstore(probe.slot, create(0, add(init, 32), mload(init))) }
        require(probe != address(0), "deploy");
        proof =
            abi.encode(uint256(1), uint256(2), uint256(3), uint256(4), uint256(5), uint256(6), uint256(7), uint256(8));
        _tx(2, uint160(probe));
        _tx(9, 4);
        _tx(10, 1);
        _tx(11, 1);
        _tx(14, 2);
        _tx(6, 100);
        _tx(15, uint256(keccak256(abi.encode(uint256(2), uint256(2), uint256(3)))));
        _store(0x8000, 0xa11ce);
        _store(0x8001, 1);
        _frame(0, 0, 0x8272);
        _frame(0, 1, 30000);
        _frame(0, 2, 1);
        _frame(0, 4, 72);
        _frame(0, 5, 1);
        _data(0, 0, uint256(keccak256(abi.encodePacked(probe, bytes32(0)))));
        _data(0, 32, 1 << 192);
        _data(0, 40, 1);
        _frame(1, 0, uint160(probe));
        _frame(1, 1, 320000);
        _frame(1, 2, 1);
        _frame(1, 3, 3);
        _frame(1, 4, 256);
        _frame(1, 9, 195840);
        _frame(2, 0, uint160(probe));
        _frame(2, 1, 1400000);
        _frame(2, 2, 2);
        _frame(2, 4, 388);
        _frame(2, 9, 550000);
        _data(2, 0, uint256(0x921fcac7) << 224);
        _data(2, 4, 1);
        _data(2, 36, 1);
        _data(2, 100, uint256(keccak256(abi.encode(TAG, block.chainid, uint256(uint160(probe))))) % P);
        _data(2, 132, 2);
        _data(2, 164, 3);
        _data(2, 196, 4);
        _data(2, 228, 5);
        _data(2, 260, 1);
        _data(2, 292, 100);
        _data(2, 324, RECIPIENT);
        _data(2, 356, 0xa11ce);
        _frame(3, 0, RECIPIENT);
        _frame(3, 1, 300000);
        _frame(3, 4, 4096);
        _frame(3, 9, 500000);
    }

    function _accepts(bool wanted) internal {
        _store(0x9000, 0);
        (bool ok,) = probe.call(proof);
        require(ok == wanted, "wrong acceptance");
        require(uint256(vm.load(probe, bytes32(uint256(0x9000)))) == (wanted ? 1 : 0), "approval mismatch");
    }

    function _claim() internal {
        _frame(3, 0, uint160(probe));
        _frame(3, 1, 100000);
        _frame(3, 4, 36);
        _frame(3, 9, 183600);
        _data(3, 0, uint256(uint32(bytes4(keccak256("claimWithdrawal(address)")))) << 224);
        _data(3, 4, RECIPIENT);
    }

    function test_supported_recipient_at_all_maxima() public {
        _accepts(true);
    }

    function test_exact_claim() public {
        _claim();
        _accepts(true);
    }

    function test_transfer_keeps_three_frames() public {
        _data(2, 260, 0);
        _data(2, 324, 0);
        _tx(9, 3);
        _accepts(true);
    }

    function test_rejects_transfer_with_tail() public {
        _data(2, 260, 0);
        _data(2, 324, 0);
        _accepts(false);
    }

    function test_rejects_missing_tail() public {
        _tx(9, 3);
        _accepts(false);
    }

    function test_rejects_fifth_frame() public {
        _tx(9, 5);
        _accepts(false);
    }

    function test_rejects_sender_tail() public {
        _frame(3, 2, 2);
        _accepts(false);
    }

    function test_rejects_verify_tail() public {
        _frame(3, 2, 1);
        _accepts(false);
    }

    function test_rejects_settlement_batch() public {
        _frame(2, 3, 4);
        _accepts(false);
    }

    function test_rejects_tail_flags() public {
        _frame(3, 3, 4);
        _accepts(false);
    }

    function test_rejects_tail_value() public {
        _frame(3, 8, 1);
        _accepts(false);
    }

    function test_rejects_other_recipient() public {
        _frame(3, 0, RECIPIENT + 1);
        _accepts(false);
    }

    function test_rejects_execution_one_over() public {
        _frame(3, 1, 300001);
        _accepts(false);
    }

    function test_rejects_state_one_over() public {
        _frame(3, 9, 500001);
        _accepts(false);
    }

    function test_rejects_data_one_over() public {
        _frame(3, 4, 4097);
        _accepts(false);
    }

    function test_rejects_claim_wrong_selector() public {
        _claim();
        _data(3, 0, uint256(0xdeadbeef) << 224);
        _accepts(false);
    }

    function test_rejects_claim_wrong_recipient() public {
        _claim();
        _data(3, 4, RECIPIENT + 1);
        _accepts(false);
    }

    function test_rejects_claim_extra_data() public {
        _claim();
        _frame(3, 4, 37);
        _accepts(false);
    }

    function test_rejects_claim_execution_one_below() public {
        _claim();
        _frame(3, 1, 99999);
        _accepts(false);
    }

    function test_rejects_claim_state_one_below() public {
        _claim();
        _frame(3, 9, 183599);
        _accepts(false);
    }

    function test_rejects_underpayment() public {
        _tx(6, 101);
        _accepts(false);
    }

    // Deliberately permitted: bounds protect payer, they do not make arbitrary account code work.
    function test_empty_zero_budget_account_call_is_admissible() public {
        _frame(3, 1, 0);
        _frame(3, 9, 0);
        _frame(3, 4, 0);
        _accepts(true);
    }

    function testFuzz_recipient_budget_bounds(uint32 execution, uint32 stateGas, uint16 dataLen) public {
        _frame(3, 1, execution);
        _frame(3, 9, stateGas);
        _frame(3, 4, dataLen);
        _accepts(execution <= 300000 && stateGas <= 500000 && dataLen <= 4096);
    }
}
