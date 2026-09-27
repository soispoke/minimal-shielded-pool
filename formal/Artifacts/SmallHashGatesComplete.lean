import Artifacts.SmallHashGatesBinding
import Artifacts.SmallHashGatesAffineCertificates

/-! Every recorded small-hash interface follows from the full pinned R1CS.
All S-box triples, affine stages, and optimized/reference equivalences are checked. -/

namespace MSP.Artifacts.SmallHashGates

open BetaGates SmallHashGatesData SmallHashGatesAffineCertificates MSP.Poseidon

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

attribute [local irreducible] MSP.Poseidon.hash2 MSP.Poseidon.hash3

private theorem h2_reference (a b : F) : MSP.Poseidon.hash2 a b = H2 a b := by
  delta H2
  rfl

private theorem h3_reference (a b c : F) : MSP.Poseidon.hash3 a b c = H3 a b c := by
  delta H3
  rfl

/-- All 54 note, path and output hash bindings, with no hash or high-level relation premise. -/
theorem hash_bindings_of_system (w : Assignment) (h : Spend.system.Satisfied w) :
    ∀ i : Fin 54, HashBinding w i := by
  intro i
  fin_cases i
  · have hh := hash_of_affine instance0 scheme3 affine0
      (SmallHashGatesCertificates.signs 0) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance0.outputForm w = H2 (eval (inputAt instance0 0) w) (eval (inputAt instance0 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance1 scheme3 affine1
      (SmallHashGatesCertificates.signs 1) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance1.outputForm w = H2 (eval (inputAt instance1 0) w) (eval (inputAt instance1 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance2 scheme4 affine2
      (SmallHashGatesCertificates.signs 2) w h
    erw [scheme4_hash, Optimized4.hash3_eq_reference] at hh
    change eval instance2.outputForm w = H3 (eval (inputAt instance2 0) w) (eval (inputAt instance2 1) w) (eval (inputAt instance2 2) w)
    exact hh.trans (h3_reference _ _ _)
  · have hh := hash_of_affine instance3 scheme3 affine3
      (SmallHashGatesCertificates.signs 3) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance3.outputForm w = H2 (eval (inputAt instance3 0) w) (eval (inputAt instance3 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance4 scheme3 affine4
      (SmallHashGatesCertificates.signs 4) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance4.outputForm w = H2 (eval (inputAt instance4 0) w) (eval (inputAt instance4 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance5 scheme3 affine5
      (SmallHashGatesCertificates.signs 5) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance5.outputForm w = H2 (eval (inputAt instance5 0) w) (eval (inputAt instance5 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance6 scheme3 affine6
      (SmallHashGatesCertificates.signs 6) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance6.outputForm w = H2 (eval (inputAt instance6 0) w) (eval (inputAt instance6 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance7 scheme3 affine7
      (SmallHashGatesCertificates.signs 7) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance7.outputForm w = H2 (eval (inputAt instance7 0) w) (eval (inputAt instance7 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance8 scheme3 affine8
      (SmallHashGatesCertificates.signs 8) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance8.outputForm w = H2 (eval (inputAt instance8 0) w) (eval (inputAt instance8 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance9 scheme3 affine9
      (SmallHashGatesCertificates.signs 9) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance9.outputForm w = H2 (eval (inputAt instance9 0) w) (eval (inputAt instance9 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance10 scheme3 affine10
      (SmallHashGatesCertificates.signs 10) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance10.outputForm w = H2 (eval (inputAt instance10 0) w) (eval (inputAt instance10 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance11 scheme3 affine11
      (SmallHashGatesCertificates.signs 11) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance11.outputForm w = H2 (eval (inputAt instance11 0) w) (eval (inputAt instance11 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance12 scheme3 affine12
      (SmallHashGatesCertificates.signs 12) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance12.outputForm w = H2 (eval (inputAt instance12 0) w) (eval (inputAt instance12 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance13 scheme3 affine13
      (SmallHashGatesCertificates.signs 13) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance13.outputForm w = H2 (eval (inputAt instance13 0) w) (eval (inputAt instance13 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance14 scheme3 affine14
      (SmallHashGatesCertificates.signs 14) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance14.outputForm w = H2 (eval (inputAt instance14 0) w) (eval (inputAt instance14 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance15 scheme3 affine15
      (SmallHashGatesCertificates.signs 15) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance15.outputForm w = H2 (eval (inputAt instance15 0) w) (eval (inputAt instance15 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance16 scheme3 affine16
      (SmallHashGatesCertificates.signs 16) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance16.outputForm w = H2 (eval (inputAt instance16 0) w) (eval (inputAt instance16 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance17 scheme3 affine17
      (SmallHashGatesCertificates.signs 17) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance17.outputForm w = H2 (eval (inputAt instance17 0) w) (eval (inputAt instance17 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance18 scheme3 affine18
      (SmallHashGatesCertificates.signs 18) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance18.outputForm w = H2 (eval (inputAt instance18 0) w) (eval (inputAt instance18 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance19 scheme3 affine19
      (SmallHashGatesCertificates.signs 19) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance19.outputForm w = H2 (eval (inputAt instance19 0) w) (eval (inputAt instance19 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance20 scheme3 affine20
      (SmallHashGatesCertificates.signs 20) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance20.outputForm w = H2 (eval (inputAt instance20 0) w) (eval (inputAt instance20 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance21 scheme3 affine21
      (SmallHashGatesCertificates.signs 21) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance21.outputForm w = H2 (eval (inputAt instance21 0) w) (eval (inputAt instance21 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance22 scheme3 affine22
      (SmallHashGatesCertificates.signs 22) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance22.outputForm w = H2 (eval (inputAt instance22 0) w) (eval (inputAt instance22 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance23 scheme4 affine23
      (SmallHashGatesCertificates.signs 23) w h
    erw [scheme4_hash, Optimized4.hash3_eq_reference] at hh
    change eval instance23.outputForm w = H3 (eval (inputAt instance23 0) w) (eval (inputAt instance23 1) w) (eval (inputAt instance23 2) w)
    exact hh.trans (h3_reference _ _ _)
  · have hh := hash_of_affine instance24 scheme3 affine24
      (SmallHashGatesCertificates.signs 24) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance24.outputForm w = H2 (eval (inputAt instance24 0) w) (eval (inputAt instance24 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance25 scheme4 affine25
      (SmallHashGatesCertificates.signs 25) w h
    erw [scheme4_hash, Optimized4.hash3_eq_reference] at hh
    change eval instance25.outputForm w = H3 (eval (inputAt instance25 0) w) (eval (inputAt instance25 1) w) (eval (inputAt instance25 2) w)
    exact hh.trans (h3_reference _ _ _)
  · have hh := hash_of_affine instance26 scheme3 affine26
      (SmallHashGatesCertificates.signs 26) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance26.outputForm w = H2 (eval (inputAt instance26 0) w) (eval (inputAt instance26 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance27 scheme3 affine27
      (SmallHashGatesCertificates.signs 27) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance27.outputForm w = H2 (eval (inputAt instance27 0) w) (eval (inputAt instance27 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance28 scheme4 affine28
      (SmallHashGatesCertificates.signs 28) w h
    erw [scheme4_hash, Optimized4.hash3_eq_reference] at hh
    change eval instance28.outputForm w = H3 (eval (inputAt instance28 0) w) (eval (inputAt instance28 1) w) (eval (inputAt instance28 2) w)
    exact hh.trans (h3_reference _ _ _)
  · have hh := hash_of_affine instance29 scheme3 affine29
      (SmallHashGatesCertificates.signs 29) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance29.outputForm w = H2 (eval (inputAt instance29 0) w) (eval (inputAt instance29 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance30 scheme3 affine30
      (SmallHashGatesCertificates.signs 30) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance30.outputForm w = H2 (eval (inputAt instance30 0) w) (eval (inputAt instance30 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance31 scheme3 affine31
      (SmallHashGatesCertificates.signs 31) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance31.outputForm w = H2 (eval (inputAt instance31 0) w) (eval (inputAt instance31 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance32 scheme3 affine32
      (SmallHashGatesCertificates.signs 32) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance32.outputForm w = H2 (eval (inputAt instance32 0) w) (eval (inputAt instance32 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance33 scheme3 affine33
      (SmallHashGatesCertificates.signs 33) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance33.outputForm w = H2 (eval (inputAt instance33 0) w) (eval (inputAt instance33 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance34 scheme3 affine34
      (SmallHashGatesCertificates.signs 34) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance34.outputForm w = H2 (eval (inputAt instance34 0) w) (eval (inputAt instance34 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance35 scheme3 affine35
      (SmallHashGatesCertificates.signs 35) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance35.outputForm w = H2 (eval (inputAt instance35 0) w) (eval (inputAt instance35 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance36 scheme3 affine36
      (SmallHashGatesCertificates.signs 36) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance36.outputForm w = H2 (eval (inputAt instance36 0) w) (eval (inputAt instance36 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance37 scheme3 affine37
      (SmallHashGatesCertificates.signs 37) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance37.outputForm w = H2 (eval (inputAt instance37 0) w) (eval (inputAt instance37 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance38 scheme3 affine38
      (SmallHashGatesCertificates.signs 38) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance38.outputForm w = H2 (eval (inputAt instance38 0) w) (eval (inputAt instance38 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance39 scheme3 affine39
      (SmallHashGatesCertificates.signs 39) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance39.outputForm w = H2 (eval (inputAt instance39 0) w) (eval (inputAt instance39 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance40 scheme3 affine40
      (SmallHashGatesCertificates.signs 40) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance40.outputForm w = H2 (eval (inputAt instance40 0) w) (eval (inputAt instance40 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance41 scheme3 affine41
      (SmallHashGatesCertificates.signs 41) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance41.outputForm w = H2 (eval (inputAt instance41 0) w) (eval (inputAt instance41 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance42 scheme3 affine42
      (SmallHashGatesCertificates.signs 42) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance42.outputForm w = H2 (eval (inputAt instance42 0) w) (eval (inputAt instance42 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance43 scheme3 affine43
      (SmallHashGatesCertificates.signs 43) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance43.outputForm w = H2 (eval (inputAt instance43 0) w) (eval (inputAt instance43 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance44 scheme3 affine44
      (SmallHashGatesCertificates.signs 44) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance44.outputForm w = H2 (eval (inputAt instance44 0) w) (eval (inputAt instance44 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance45 scheme3 affine45
      (SmallHashGatesCertificates.signs 45) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance45.outputForm w = H2 (eval (inputAt instance45 0) w) (eval (inputAt instance45 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance46 scheme3 affine46
      (SmallHashGatesCertificates.signs 46) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance46.outputForm w = H2 (eval (inputAt instance46 0) w) (eval (inputAt instance46 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance47 scheme3 affine47
      (SmallHashGatesCertificates.signs 47) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance47.outputForm w = H2 (eval (inputAt instance47 0) w) (eval (inputAt instance47 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance48 scheme3 affine48
      (SmallHashGatesCertificates.signs 48) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance48.outputForm w = H2 (eval (inputAt instance48 0) w) (eval (inputAt instance48 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance49 scheme4 affine49
      (SmallHashGatesCertificates.signs 49) w h
    erw [scheme4_hash, Optimized4.hash3_eq_reference] at hh
    change eval instance49.outputForm w = H3 (eval (inputAt instance49 0) w) (eval (inputAt instance49 1) w) (eval (inputAt instance49 2) w)
    exact hh.trans (h3_reference _ _ _)
  · have hh := hash_of_affine instance50 scheme3 affine50
      (SmallHashGatesCertificates.signs 50) w h
    erw [scheme3_hash, Optimized3.hash2_eq_reference] at hh
    change eval instance50.outputForm w = H2 (eval (inputAt instance50 0) w) (eval (inputAt instance50 1) w)
    exact hh.trans (h2_reference _ _)
  · have hh := hash_of_affine instance51 scheme4 affine51
      (SmallHashGatesCertificates.signs 51) w h
    erw [scheme4_hash, Optimized4.hash3_eq_reference] at hh
    change eval instance51.outputForm w = H3 (eval (inputAt instance51 0) w) (eval (inputAt instance51 1) w) (eval (inputAt instance51 2) w)
    exact hh.trans (h3_reference _ _ _)
  · have hh := hash_of_affine instance52 scheme4 affine52
      (SmallHashGatesCertificates.signs 52) w h
    erw [scheme4_hash, Optimized4.hash3_eq_reference] at hh
    change eval instance52.outputForm w = H3 (eval (inputAt instance52 0) w) (eval (inputAt instance52 1) w) (eval (inputAt instance52 2) w)
    exact hh.trans (h3_reference _ _ _)
  · have hh := hash_of_affine instance53 scheme4 affine53
      (SmallHashGatesCertificates.signs 53) w h
    erw [scheme4_hash, Optimized4.hash3_eq_reference] at hh
    change eval instance53.outputForm w = H3 (eval (inputAt instance53 0) w) (eval (inputAt instance53 1) w) (eval (inputAt instance53 2) w)
    exact hh.trans (h3_reference _ _ _)

#print axioms hash_bindings_of_system

end MSP.Artifacts.SmallHashGates
