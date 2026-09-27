import Spec.Basic
import Mathlib.Tactic

/-! Exact coordinate equations needed by EIP-197. These are checks over the
base modulus, not a completed curve-group or pairing implementation. In
particular, `OnCurve` does not claim prime-order subgroup membership. -/

namespace MSP.Groth16

abbrev Fq := ZMod q
abbrev Fq2 := Fq × Fq

/-- Coordinates are `(real, imaginary)`, with `i² = -1`. -/
def fq2mul (a b : Fq2) : Fq2 :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def fq2sub (a b : Fq2) : Fq2 := (a.1 - b.1, a.2 - b.2)

/-- Inverse of `9+i`, certified below using only modular ring arithmetic. -/
def twistInverse : Fq2 :=
  (21087453498479301738505683583845423561061080261299122796980902361914303298513,
   14681138511599513868579906292550611339979233093309515871315818100066920017952)

def twistB : Fq2 := fq2mul (3, 0) twistInverse

theorem fq2mul_assoc (a b c : Fq2) :
    fq2mul (fq2mul a b) c = fq2mul a (fq2mul b c) := by
  apply Prod.ext <;> simp [fq2mul] <;> ring

theorem fq2mul_comm (a b : Fq2) : fq2mul a b = fq2mul b a := by
  apply Prod.ext <;> simp [fq2mul] <;> ring

theorem fq2mul_one (a : Fq2) : fq2mul a (1, 0) = a := by
  apply Prod.ext <;> simp [fq2mul]

theorem twistInverse_correct : fq2mul (9, 1) twistInverse = (1, 0) := by decide

theorem twistB_correct : fq2mul twistB (9, 1) = (3, 0) := by decide

structure G1Coordinates where
  x : ℕ
  y : ℕ
  deriving DecidableEq

structure G2Coordinates where
  xRe : ℕ
  xIm : ℕ
  yRe : ℕ
  yIm : ℕ
  deriving DecidableEq

def G1Coordinates.Canonical (a : G1Coordinates) : Prop := a.x < q ∧ a.y < q
def G1Coordinates.Nonzero (a : G1Coordinates) : Prop := a.x ≠ 0 ∨ a.y ≠ 0

def G2Coordinates.Canonical (b : G2Coordinates) : Prop :=
  b.xRe < q ∧ b.xIm < q ∧ b.yRe < q ∧ b.yIm < q

def G2Coordinates.Nonzero (b : G2Coordinates) : Prop :=
  b.xRe ≠ 0 ∨ b.xIm ≠ 0 ∨ b.yRe ≠ 0 ∨ b.yIm ≠ 0

def G1Coordinates.OnCurve (a : G1Coordinates) : Prop :=
  (a.y : Fq)^2 = (a.x : Fq)^3 + 3

/-- The twist equation multiplied by `9+i`: `(y²-x³)*(9+i)=3`.
This avoids introducing a field or division before base-field primality and
quadratic-extension field structure have been proved. -/
def G2Coordinates.OnCurve (b : G2Coordinates) : Prop :=
  let x : Fq2 := (b.xRe, b.xIm)
  let y : Fq2 := (b.yRe, b.yIm)
  fq2mul (fq2sub (fq2mul y y) (fq2mul (fq2mul x x) x)) (9, 1) = (3, 0)

/-- The multiplied check is exactly the twist equation with its uniquely
invertible denominator, even before introducing the extension's field instance. -/
theorem G2Coordinates.onCurve_iff (b : G2Coordinates) :
    b.OnCurve ↔
      fq2sub (fq2mul (b.yRe, b.yIm) (b.yRe, b.yIm))
        (fq2mul (fq2mul (b.xRe, b.xIm) (b.xRe, b.xIm)) (b.xRe, b.xIm)) = twistB := by
  unfold G2Coordinates.OnCurve
  dsimp only
  constructor
  · intro h
    have he := congrArg (fun z => fq2mul z twistInverse) h
    simpa only [fq2mul_assoc, twistInverse_correct, fq2mul_one, twistB] using he
  · intro h
    rw [h]
    exact twistB_correct

structure ProofCoordinates where
  a : G1Coordinates
  b : G2Coordinates
  c : G1Coordinates
  deriving DecidableEq

def ProofCoordinates.Canonical (π : ProofCoordinates) : Prop :=
  π.a.Canonical ∧ π.b.Canonical ∧ π.c.Canonical

def ProofCoordinates.Nonzero (π : ProofCoordinates) : Prop :=
  π.a.Nonzero ∧ π.b.Nonzero ∧ π.c.Nonzero

def ProofCoordinates.OnCurve (π : ProofCoordinates) : Prop :=
  π.a.OnCurve ∧ π.b.OnCurve ∧ π.c.OnCurve

instance (π : ProofCoordinates) : Decidable π.Canonical :=
  by unfold ProofCoordinates.Canonical G1Coordinates.Canonical G2Coordinates.Canonical; infer_instance
instance (π : ProofCoordinates) : Decidable π.Nonzero :=
  by unfold ProofCoordinates.Nonzero G1Coordinates.Nonzero G2Coordinates.Nonzero; infer_instance

structure VerificationKey where
  alpha1 : G1Coordinates
  beta2 : G2Coordinates
  gamma2 : G2Coordinates
  delta2 : G2Coordinates
  ic : Fin 4 → G1Coordinates

/-- Only coordinate/curve checks. The prime-order subgroup checks and pairing
relation are additional obligations and are deliberately absent from this predicate. -/
def VerificationKey.CoordinateChecks (vk : VerificationKey) : Prop :=
  (vk.alpha1.Canonical ∧ vk.alpha1.Nonzero ∧ vk.alpha1.OnCurve) ∧
  (∀ i, (vk.ic i).Canonical ∧ (vk.ic i).Nonzero ∧ (vk.ic i).OnCurve) ∧
  (vk.beta2.Canonical ∧ vk.beta2.Nonzero ∧ vk.beta2.OnCurve) ∧
  (vk.gamma2.Canonical ∧ vk.gamma2.Nonzero ∧ vk.gamma2.OnCurve) ∧
  (vk.delta2.Canonical ∧ vk.delta2.Nonzero ∧ vk.delta2.OnCurve)

end MSP.Groth16
