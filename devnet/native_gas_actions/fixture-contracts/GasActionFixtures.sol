// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.24;

contract GasActionNativeAccount {
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
        "GasAction(address pool,address target,uint256 value,bytes data,uint256 callGas,uint256 nonce,bytes32 settlementHash)"
    );
    uint256 private constant HALF_ORDER =
        0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0;

    address public immutable owner;
    address private immutable context;
    uint256 public nonce;
    bool private entered;

    error Unauthorized();
    error WrongNonce();
    error WrongFrame();
    error Reentrant();

    constructor(address owner_, address context_) {
        require(owner_ != address(0));
        owner = owner_;
        context = context_;
    }

    function digest(Action calldata action) public view returns (bytes32) {
        bytes32 domainSeparator = keccak256(
            abi.encode(
                DOMAIN_TYPEHASH,
                keccak256("GasActionNativeAccount"),
                keccak256("1"),
                block.chainid,
                address(this)
            )
        );
        bytes32 actionHash = keccak256(
            abi.encode(
                ACTION_TYPEHASH,
                action.pool,
                action.target,
                action.value,
                keccak256(action.data),
                action.callGas,
                action.nonce,
                action.settlementHash
            )
        );
        return keccak256(abi.encodePacked("\x19\x01", domainSeparator, actionHash));
    }

    function execute(Action calldata action, uint8 v, bytes32 r, bytes32 s) external {
        if (entered) revert Reentrant();
        if (msg.sender != address(0xAA)) revert WrongFrame();
        (bool contextOk, bytes memory report) = context.staticcall(abi.encode(action.pool));
        if (!contextOk || report.length != 32 || abi.decode(report, (bytes32)) != action.settlementHash) {
            revert WrongFrame();
        }
        if (action.nonce != nonce) revert WrongNonce();
        if (
            (v != 27 && v != 28) || uint256(s) > HALF_ORDER
                || ecrecover(digest(action), v, r, s) != owner
        ) revert Unauthorized();

        entered = true;
        nonce++;
        (bool ok, bytes memory ret) = action.target.call{value: action.value, gas: action.callGas}(action.data);
        if (!ok) assembly { revert(add(ret, 32), mload(ret)) }
        entered = false;
    }

    receive() external payable {}
}

contract TestAsset {
    mapping(address => uint256) public balanceOf;

    function mint(address who, uint256 amount) external {
        balanceOf[who] += amount;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        uint256 balance = balanceOf[msg.sender];
        require(balance >= amount, "balance");
        balanceOf[msg.sender] = balance - amount;
        balanceOf[to] += amount;
        return true;
    }
}

contract FailureTarget {
    mapping(uint256 => uint256) public words;

    error DeliberateFailure();

    function fail() external pure {
        revert DeliberateFailure();
    }

    function exhaustExecution() external pure {
        while (true) {}
    }

    function growState(uint256 count) external {
        for (uint256 i = 0; i < count; i++) words[i] = i + 1;
    }
}
