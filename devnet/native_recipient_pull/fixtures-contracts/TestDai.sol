// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

// Local DAI-denominated fixture token, not mainnet DAI or a Maker deployment.
contract TestDai {
    string public constant name = "Local Test DAI";
    string public constant symbol = "DAI";
    uint8 public constant decimals = 18;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    uint256 public totalSupply;
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);
    function mint(address to, uint256 value) external {
        totalSupply += value; balanceOf[to] += value; emit Transfer(address(0), to, value);
    }
    function approve(address spender, uint256 value) external returns (bool) {
        allowance[msg.sender][spender] = value; emit Approval(msg.sender, spender, value); return true;
    }
    function transfer(address to, uint256 value) external returns (bool) {
        _transfer(msg.sender, to, value); return true;
    }
    function transferFrom(address from, address to, uint256 value) external returns (bool) {
        if (allowance[from][msg.sender] != type(uint256).max) allowance[from][msg.sender] -= value;
        _transfer(from, to, value); return true;
    }
    function _transfer(address from, address to, uint256 value) private {
        balanceOf[from] -= value; balanceOf[to] += value; emit Transfer(from, to, value);
    }
}

contract NativeFailureTarget {
    mapping(uint256 => uint256) public slots;
    function fail() external payable { revert("forced action failure"); }
    function exhaustExecution() external payable { assembly { for {} 1 {} {} } }
    function growState(uint256 count) external payable {
        for (uint256 i; i < count; ++i) slots[i] = i + 1;
    }
}
