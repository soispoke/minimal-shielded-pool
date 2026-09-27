# Direct continuation, September 27, 2026

Claude's reviewed specification through round 37 (`b1a15ef`) was merged in
`640c260`. Checkpoint `eecdead` proves full G1 cardinality, generation and
scalar-field correspondence. The attached baseline and G1 logs record those
checks.

The four complete circuit mutation certificates pass the final full build
(3,796 jobs). Their principal axiom outputs use only `propext`,
`Classical.choice` and `Quot.sound`. The negative control changes the first
coefficient of MembershipChunk0 from p−1 to p−2 while retaining the claimed
certificate; Lean correctly rejects it as false (exit 1). No production file
was changed by this check. Three exporter tests pass, covering all archived
cases, binary/digest mismatches and source-pin failure. All four generators
reproduce exactly, and the static gate reports 30 locked files, 12 pinned
artifacts and 649 admission-free Lean files. See `../../Mutations/README.md`
for reproduction and the external binary/source binding.

Remaining chain claims, W2, full G2 subgroup/pairing bindings and the other
semantic mutation rows are not discharged by this evidence. The scheduled
two-hour job remains paused at the user's request.
