import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! The axiom-audit command. It lives in a module that imports only core Lean,
so every name and instance its code uses is resolved before any project module
loads, and no project declaration can change what it checks. -/

elab "assert_standard_axioms " n:ident : command => do
  let name ← _root_.Lean.Elab.Command.liftCoreM <|
    _root_.Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← _root_.Lean.collectAxioms name
  let allowed : _root_.List _root_.Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let extra := axioms.filter fun ax => !allowed.contains ax
  unless extra.isEmpty do
    _root_.Lean.throwError m!"{n} depends on nonstandard axioms: {extra}"
