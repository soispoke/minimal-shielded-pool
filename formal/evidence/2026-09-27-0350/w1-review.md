# W1 focused integration review

Reviewed by the coordinating Codex agent after the independent workers froze
their proofs, September 27, 2026. This is an integration review; the coordinator
also authored the generic byte/frame encoder and combined-table proof.

The exported theorem is exactly `MSP.w1 : W1`, without premises. The canonical
`Spec.Main.W1` statement is unchanged. Its verifier accepts exactly the public
triples of satisfying assignments for every proof byte string, and its
extractor satisfies `IdealVerifier` for all accepted triples. C1c supplies the
preferred actual assignment, with exact statement/witness/public projections.
The all-one proof bytes satisfy A6's encoding checks; they are not represented
as a valid Groth16 proof. This use of an ideal verifier is precisely W1's scope.

Checked the actual shield/publish/tick/spend transitions, prior-slot root,
nonzero distinct sorted nullifiers, all A1–A7 data/frame checks, fee and balance,
settlement preconditions, no inserted sink outputs, consumed occurrence and
one unit of credited withdrawal. No payout or W2 is inferred. Validation's two
gas limits are concrete, but the model proof is not a chain gas theorem.

Compact-tree pruning is proved equivalent for membership in the original
query multiset, independent of hash properties. Every actual trace query,
including both paths, tree prefixes, source, domain, nonce and storage hashes,
is covered by the finite table. Its 80 entries are checked together, including
cross-table output equality. Equal outputs require identical queries; numeric
bounds rule out every defined degenerate query. Exact preferred projections
rule out extraction and compression failures. No global hash-injectivity or
security assumption replaces any of these checks.

No substantive gap found in these boundaries. Full default `lake build`
passes 3,639 jobs. The automated axiom audit admits only standard Lean axioms;
`MSP.w1` reports `propext`, `Classical.choice`, `Quot.sound`. The separate
remaining chain/verifier/subgroup/pairing obligations are unchanged.

Reviewed file SHA-256 values:

- `Spec/Main.lean`: `fdc4015c706736c052d13b2363fde3aaf93176150e1e965f0e0ca026b149a330`
- `Spec/Hash.lean`: `a3e66bc20a289d75094655f75c5ee248bdb3e6db0623a6e6a73393b4bd2bce04`
- `Proofs/NonVacuityFixtureComplete.lean`: `6b82ff38a1370c83477965325f975b7a766c0ce53465cbf2a37496a30fc1feb5`
- `Proofs/NonVacuityFixtureVerified.lean`: `d2ac192f09b962f8e748b6a2af6df80f5770bd1e5dec6c290999ade48aa072bf`
- `Proofs/NonVacuityTrace.lean`: `c81b6907bba18d4147abc0f5397f6767327776f9f705078f118390d959984eb8`
- `Proofs/NonVacuityFixtureRun.lean`: `04cde24739e0bf8ff772b6b736b52331c04a681dfcf3e21334801bdc1fb7a46d`
- `Proofs/NonVacuityFixtureTableCombined.lean`: `fffe545b05f7260c349e7bb67f9990f63ce0e53f09d464d03103b9e7edd84a7e`
