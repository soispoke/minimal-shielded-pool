# Circuit mutation proof handoff

`Check.lean` proves that the finite Boolean constraint checker implies the
same `Artifacts.Constraint.Holds` and `System.Satisfied` semantics used by C1.
It builds successfully. It does not yet certify a concrete mutant assignment.

The four required executable counterexamples are complete and preserved in
`../evidence/2026-09-27-0350/circuit-mutations/`, with reproduction commands,
full source/R1CS/WTNS/symbol/WASM archives and the exact trust boundary.

`MembershipValues.lean.pending` contains the actual decimal witness from
`/private/tmp/msp-circuit-mutations-ilgt9dwh/membership/decoded.json`.
`MembershipPilot.lean.pending` is a proposed certificate for its first 64
constraints. Both are parked outside the build because the large array reaches
Lean's default recursion limit while elaborating `MembershipValues`. There is
no checked concrete certificate yet. See `mutation-pilot-incomplete.log` in the
evidence directory for the exact failed command output.

To continue, raise or avoid the array elaboration recursion depth, test the
64-constraint kernel evaluation cost, then generate bounded blocks for every
actual constraint. Prove the full mutant system satisfied and the intended
canonical relation clause false on its actual symbol projections. Verify every
reused projection against that mutant's symbols. These steps are still open;
passing executable evaluations or the generic reflection theorem does not
close the required Lean mutation gates.
