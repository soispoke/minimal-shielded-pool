object "NativeFrameContext" {
  code { datacopy(0, dataoffset("runtime"), datasize("runtime")) return(0, datasize("runtime")) }
  object "runtime" { code {
    function require_(v) { if iszero(v) { revert(0,0) } }
    function txp(p) -> v { v := verbatim_1i_1o(hex"B0", p) }
    function fp(i,p) -> v { v := verbatim_2i_1o(hex"B3", i,p) }
    function fd(i,o) -> v { v := verbatim_2i_1o(hex"B1", o,i) }
    require_(eq(calldatasize(),32))
    let pool := calldataload(0)
    require_(and(iszero(shr(160,pool)),iszero(iszero(pool))))
    require_(eq(txp(0x09),4))
    require_(eq(txp(0x0A),3))
    require_(eq(txp(0x02),pool))
    require_(eq(fp(2,0x00),pool))
    require_(eq(fp(2,0x02),2))
    require_(iszero(fp(2,0x03)))
    require_(eq(fp(2,0x04),388))
    require_(eq(fp(2,0x05),1))
    require_(iszero(fp(2,0x08)))
    require_(eq(shr(224,fd(2,0)),0x921fcac7))
    require_(eq(fd(2,324),caller()))
    require_(eq(fp(3,0x00),caller()))
    require_(iszero(fp(3,0x02)))
    require_(iszero(fp(3,0x03)))
    require_(iszero(fp(3,0x08)))
    for { let o := 0 } lt(o,384) { o := add(o,32) } { mstore(o,fd(2,add(o,4))) }
    mstore(384,keccak256(0,384))
    return(384,32)
  } }
}
