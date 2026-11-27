import Collatz

/-!
# Axiom audit

`#axiom_audit` fails if any declaration of a `Collatz.*` module depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound` (so in particular on `sorryAx`, or on the
compiler-trusting axioms behind `native_decide`). Run by `lake test` in CI.
-/

open Lean Elab Command

elab "#axiom_audit" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    unless (`Collatz).isPrefixOf mod do continue
    for n in env.header.moduleData[i]!.constNames do
      for a in ← collectAxioms n do
        unless allowed.contains a do
          throwError "{n} depends on the axiom {a}"
      count := count + 1
  if count < 500 then
    throwError "only {count} declarations found; is `Collatz` imported?"
  logInfo m!"axiom audit: {count} declarations from Collatz.* use only propext, Classical.choice, Quot.sound"

#axiom_audit
