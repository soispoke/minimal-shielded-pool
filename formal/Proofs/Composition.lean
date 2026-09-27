import Proofs.Composes

/-! Compatibility import for the composition proof. `Composes.lean` contains
its canonical proof and the run invariant used below. -/

namespace MSP

/-- C5b excludes a repeated occurrence both within one spend and across spends.
This keeps the earlier public name for `run_nodup`. -/
theorem spent_nodup_of_c5b (P : Pool) (hC5b : C5b P) :
    ∀ evs s, Run P evs s → BadEvent P evs s ∨ s.spent.Nodup :=
  run_nodup P hC5b

#print axioms spent_nodup_of_c5b

end MSP
