import Spec.Evm

/-!
# §5: the main theorem, its chain-level meaning, and non-vacuity
-/

namespace MSP

noncomputable section

open Classical

/-- The model half: the circuit gives C3 to C5 and spendability for every run
of the model, every verifier and every extractor. -/
def ModelTheorem : Prop :=
  C1 → ∀ P : Pool,
    C3 P ∧ C4 P ∧ C5a P ∧ C5b P ∧ C5c P ∧ C5d P ∧ C5e P ∧ C5g P ∧ C5h P ∧ C5i P ∧
    C5j P ∧ C5k P ∧ C5l P ∧ C5m P ∧ C5n P ∧ StepFunctional P ∧ Spendable P

/-- The chain half: the deployed code behaves as the model, including fitting
its gas, and lets anyone publish roots and pay out credits. -/
def ChainTheorem : Prop := C2 ∧ C2c ∧ C6 ∧ C8 ∧ C9 ∧ C10 ∧ Refines

/-- §5. -/
def MainTheorem : Prop := C1 ∧ C1c ∧ ModelTheorem ∧ ChainTheorem

/-- What §5 means for the chain: along every chain run of an honest deployment,
for every extractor, the pool is solvent, no occurrence is consumed twice, and
every root under the source of an epoch `e < 2 ^ 64` is a real root of its tree, or some prefix
of the run has a bad event. A bad event, even among queries only the adversary
chose, voids the conclusion for every user from then on. -/
def ChainCorollary : Prop :=
  ∀ d ext, Honest d → ∀ h, ChainRun d h →
    (∃ pre e s, pre ++ [e] <+: modelEvents d h ∧ Run (poolOf d ext) pre s ∧
        BadEvent (poolOf d ext) (pre ++ [e]) s) ∨
    ∃ s, Run (poolOf d ext) (modelEvents d h) s ∧
      (BadEvent (poolOf d ext) (modelEvents d h) s ∨
        (Obs d (h.getLast?.getD default) s ∧ owed s ≤ s.balance ∧ s.spent.Nodup ∧
         ∀ r ∈ s.roots, ∀ e < 2 ^ 64, r.1 = sourceId (addrOf d) e →
           BadEventWith (poolOf d ext) (modelEvents d h) s [.keccak (addr20 (addrOf d) ++ u256 e)] ∨
           ∃ n ≤ (s.leaves e).length, r.2.2 = (TR ((s.leaves e).take n)).val))

/-- The main theorem implies its chain-level meaning. -/
def Composes : Prop := MainTheorem → ChainCorollary

/-- Model non-vacuity: with an extractor for a verifier that accepts exactly
the public signals of satisfying assignments, some run has an approved spend
whose settlement passes every check, with no bad event. With concrete hashes
this needs a symbolic lemma for membership in `treeQueries`, whose repeated
empty subtrees make about `2 ^ 20` entries per prefix, so about `2 ^ 40` pairs to
check for collisions. -/
def W1 : Prop :=
  ∃ (P : Pool) (evs : List Event) (s : PoolState) (tx : FrameTx) (g : ℕ) (s' : PoolState),
    IdealVerifier P ∧ (∀ π pub, P.verifies π pub ↔ ∃ a, Satisfied a ∧ publicOf a = pub) ∧
    Run P evs s ∧ Step P s (.spend tx g) s' ∧ SettlePre s P (settleData tx) ∧
    ¬ BadEvent P (evs ++ [.spend tx g]) s'

/-- Chain non-vacuity: some reachable state of an honest deployment shows a
leaf and a payout, the pool approves there a transaction valid up to frame 1
and then valid, and some caller other than the pool has a valid environment
there. -/
def W2 : Prop :=
  ∃ d st t, Honest d ∧ ReachableChain d st ∧ PreValid st t ∧ ValidTx st t ∧
    (1, 3) ∈ approvalsIn d st t ∧
    st.leafLogs (addrOf d) 0 ≠ [] ∧ (∃ r, st.sentTo (addrOf d) r ≠ 0) ∧
    ∃ caller env, caller ≠ addrOf d ∧ EnvValid st caller env

end

end MSP
