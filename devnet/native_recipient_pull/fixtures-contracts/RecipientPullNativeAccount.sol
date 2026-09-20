// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.24;

// Integration-test account. The immutable helper executes real native frame
// introspection; it never receives a simulated context or authorization oracle.
interface IPool {
    function withdrawalCredit(address who) external view returns (uint256);
    function claimWithdrawal(address payable who) external;
}
contract RecipientPullNativeAccount {
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
    address private immutable context;
    uint256 public nonce;
    bool private entered;

    error Unauthorized();
    error WrongNonce();
    error WrongFrame();
    error SettlementFailed();
    error Reentrant();

    constructor(address owner_, address context_) {
        require(owner_ != address(0));
        owner = owner_;
        context = context_;
    }

    function digest(Action calldata a) public view returns (bytes32) {
        bytes32 domainSeparator = keccak256(
            abi.encode(
                DOMAIN_TYPEHASH, keccak256("RecipientPullNativeTestAccount"), keccak256("1"), block.chainid, address(this)
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
        if (msg.sender != address(0xAA)) revert WrongFrame();
        (bool contextOk, bytes memory report) = context.staticcall(abi.encode(a.pool));
        if (!contextOk || report.length != 32 || abi.decode(report, (bytes32)) != a.settlementHash) {
            revert WrongFrame();
        }
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

    function recover(address pool) external {
        require(msg.sender == owner && !entered, "owner only");
        entered = true;
        if (IPool(pool).withdrawalCredit(address(this)) != 0) {
            IPool(pool).claimWithdrawal(payable(address(this)));
        }
        (bool ok,) = payable(owner).call{value: address(this).balance}("");
        require(ok, "recovery payout");
        entered = false;
    }

    receive() external payable {}
}
