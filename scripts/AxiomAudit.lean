/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import ArlibCommunity

/-!
# Axiom audit

Checks that declarations in `ArlibCommunity` depend only on the three axioms
used by Mathlib: `propext`, `Classical.choice`, and `Quot.sound`. Run with:

```bash
lake env lean scripts/AxiomAudit.lean
```
-/

open Lean Elab Command

namespace ArlibCommunity.AxiomAudit

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def communityDecls (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    if (`ArlibCommunity).isPrefixOf n then out := out.push n
  return out

def reachableAxioms (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  let mut stack : Array Name := roots
  while stack.size > 0 do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      if ci matches .axiomInfo _ then axioms := axioms.insert n
      stack := stack ++ ci.type.getUsedConstants
      if let some v := ci.value? then stack := stack ++ v.getUsedConstants
  return axioms

end ArlibCommunity.AxiomAudit

open ArlibCommunity.AxiomAudit in
run_cmd do
  let env ← getEnv
  let roots := communityDecls env
  let found := reachableAxioms env roots
  let offending := found.toList.filter fun a => !allowed.contains a
  if offending.isEmpty then
    logInfo m!"axiom audit: {roots.size} ArlibCommunity declarations, \
      axioms used = {found.toList}, all allowed."
  else
    let mut msg := m!"AXIOM AUDIT FAILED — disallowed axioms: {offending}\n"
    for ax in offending do
      let mut culprits : Array Name := #[]
      for r in roots do
        let used ← liftCoreM <| collectAxioms r
        if used.contains ax then culprits := culprits.push r
        if culprits.size ≥ 25 then break
      msg := msg ++ m!"\n  {ax} is used by {culprits.size}+ declarations, e.g.:\n"
      for c in culprits do
        msg := msg ++ m!"    {c}\n"
    throwError msg
