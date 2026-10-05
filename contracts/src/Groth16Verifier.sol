// SPDX-License-Identifier: GPL-3.0
/*
    Copyright 2021 0KIMS association.

    This file is generated with [snarkJS](https://github.com/iden3/snarkjs).

    snarkJS is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    snarkJS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with snarkJS. If not, see <https://www.gnu.org/licenses/>.
*/

pragma solidity >=0.7.0 <0.9.0;

contract Groth16Verifier {
    // Scalar field size
    uint256 constant r = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    // Base field size
    uint256 constant q = 21888242871839275222246405745257275088696311157297823662689037894645226208583;

    // Verification Key data
    uint256 constant alphax = 19709469845062818453627837830734486665998591314994809489665599538394471518160;
    uint256 constant alphay = 10402150318463676996855120373732627540649911183815775441283645283912379430814;
    uint256 constant betax1 = 15407209047211646941761017343433313394761372880171848211564101058447174093774;
    uint256 constant betax2 = 5440303179606483886257058571725571142805222041136437054563890819903893460502;
    uint256 constant betay1 = 10369111136702264167065751841558821156529110188328609646583418558398086127946;
    uint256 constant betay2 = 10082620068342224614000147040622697345352951632862194787646323095125009758982;
    uint256 constant gammax1 = 11559732032986387107991004021392285783925812861821192530917403151452391805634;
    uint256 constant gammax2 = 10857046999023057135944570762232829481370756359578518086990519993285655852781;
    uint256 constant gammay1 = 4082367875863433681332203403145435568316851327593401208105741076214120093531;
    uint256 constant gammay2 = 8495653923123431417604973247489272438418190587263600148770280649306958101930;
    uint256 constant deltax1 = 10729515847469139183301074052819296582093398806792938816144205865118535295100;
    uint256 constant deltax2 = 2687166456426217680811242913357958724750987244418972253351140528149523144305;
    uint256 constant deltay1 = 14671215771899132545213625712865057771641909707772848656945869459536371995833;
    uint256 constant deltay2 = 9407001401585046038025011796443479232470926784730054538481373864980438871572;

    uint256 constant IC0x = 2919511224010239792167465245209595638885754386315242675808551326993223046254;
    uint256 constant IC0y = 4997741814090982764166485914952586028288822976046441650362377734107083883408;

    uint256 constant IC1x = 1511428093689815590996837167535530144130476046413388470373795537230566208970;
    uint256 constant IC1y = 8553316255969942159531603250527907058334379762110959052513379327189608683478;

    uint256 constant IC2x = 18730445920843886774308635405807364327816329613158960230875924097695143516537;
    uint256 constant IC2y = 14034321209184266354671229981392837710986229781248884969503499730178554982899;

    uint256 constant IC3x = 1031216783080542517588768903145288723147309299527004880473493704721692361368;
    uint256 constant IC3y = 1896887966029399501348520946474088632223314300664383165846604119140120665861;

    // Memory data
    uint16 constant pVk = 0;
    uint16 constant pPairing = 128;

    uint16 constant pLastMem = 896;

    function verifyProof(
        uint256[2] calldata _pA,
        uint256[2][2] calldata _pB,
        uint256[2] calldata _pC,
        uint256[3] calldata _pubSignals
    ) public view returns (bool) {
        assembly {
            function checkField(v) {
                if iszero(lt(v, r)) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }

            // G1 function to multiply a G1 value(x,y) to value in an address
            function g1_mulAccC(pR, x, y, s) {
                let success
                let mIn := mload(0x40)
                mstore(mIn, x)
                mstore(add(mIn, 32), y)
                mstore(add(mIn, 64), s)

                success := staticcall(500000, 7, mIn, 96, mIn, 64)

                if iszero(success) {
                    mstore(0, 0)
                    return(0, 0x20)
                }

                mstore(add(mIn, 64), mload(pR))
                mstore(add(mIn, 96), mload(add(pR, 32)))

                success := staticcall(500000, 6, mIn, 128, pR, 64)

                if iszero(success) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }

            function checkPairing(pA, pB, pC, pubSignals, pMem) -> isOk {
                let _pPairing := add(pMem, pPairing)
                let _pVk := add(pMem, pVk)

                mstore(_pVk, IC0x)
                mstore(add(_pVk, 32), IC0y)

                // Compute the linear combination vk_x

                g1_mulAccC(_pVk, IC1x, IC1y, calldataload(add(pubSignals, 0)))

                g1_mulAccC(_pVk, IC2x, IC2y, calldataload(add(pubSignals, 32)))

                g1_mulAccC(_pVk, IC3x, IC3y, calldataload(add(pubSignals, 64)))

                // -A
                mstore(_pPairing, calldataload(pA))
                mstore(add(_pPairing, 32), mod(sub(q, calldataload(add(pA, 32))), q))

                // B
                mstore(add(_pPairing, 64), calldataload(pB))
                mstore(add(_pPairing, 96), calldataload(add(pB, 32)))
                mstore(add(_pPairing, 128), calldataload(add(pB, 64)))
                mstore(add(_pPairing, 160), calldataload(add(pB, 96)))

                // alpha1
                mstore(add(_pPairing, 192), alphax)
                mstore(add(_pPairing, 224), alphay)

                // beta2
                mstore(add(_pPairing, 256), betax1)
                mstore(add(_pPairing, 288), betax2)
                mstore(add(_pPairing, 320), betay1)
                mstore(add(_pPairing, 352), betay2)

                // vk_x
                mstore(add(_pPairing, 384), mload(add(pMem, pVk)))
                mstore(add(_pPairing, 416), mload(add(pMem, add(pVk, 32))))

                // gamma2
                mstore(add(_pPairing, 448), gammax1)
                mstore(add(_pPairing, 480), gammax2)
                mstore(add(_pPairing, 512), gammay1)
                mstore(add(_pPairing, 544), gammay2)

                // C
                mstore(add(_pPairing, 576), calldataload(pC))
                mstore(add(_pPairing, 608), calldataload(add(pC, 32)))

                // delta2
                mstore(add(_pPairing, 640), deltax1)
                mstore(add(_pPairing, 672), deltax2)
                mstore(add(_pPairing, 704), deltay1)
                mstore(add(_pPairing, 736), deltay2)

                let success := staticcall(500000, 8, _pPairing, 768, _pPairing, 0x20)

                isOk := and(success, mload(_pPairing))
            }

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
            if iszero(or(ax, ay)) {
                mstore(0, 0)
                return(0, 0x20)
            }
            if iszero(or(or(bx0, bx1), or(by0, by1))) {
                mstore(0, 0)
                return(0, 0x20)
            }
            if iszero(or(cx, cy)) {
                mstore(0, 0)
                return(0, 0x20)
            }

            let pMem := mload(0x40)
            mstore(0x40, add(pMem, pLastMem))

            // Validate that all evaluations ∈ F

            checkField(calldataload(add(_pubSignals, 0)))

            checkField(calldataload(add(_pubSignals, 32)))

            checkField(calldataload(add(_pubSignals, 64)))

            // Validate all evaluations
            let isValid := checkPairing(_pA, _pB, _pC, _pubSignals, pMem)

            mstore(0, isValid)
            return(0, 0x20)
        }
    }
}
