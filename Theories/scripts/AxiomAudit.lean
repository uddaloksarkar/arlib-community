/-
Copyright (c) 2026 the arlib-community contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity

/-! Fail when a community declaration reaches an axiom outside Mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound` foundations. In
particular, this detects `sorryAx` semantically. -/

open Lean Elab Command

namespace ArlibCommunity.AxiomAudit

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def communityDecls (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (name, _) in env.constants.toList do
    if name.isInternal then continue
    if (`ArlibCommunity).isPrefixOf name then out := out.push name
  return out

def reachableAxioms (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  let mut stack := roots
  while stack.size > 0 do
    let name := stack.back!
    stack := stack.pop
    if visited.contains name then continue
    visited := visited.insert name
    match env.find? name with
    | none => pure ()
    | some info =>
      if info matches .axiomInfo _ then axioms := axioms.insert name
      stack := stack ++ info.type.getUsedConstants
      if let some value := info.value? then stack := stack ++ value.getUsedConstants
  return axioms

end ArlibCommunity.AxiomAudit

open ArlibCommunity.AxiomAudit in
run_cmd do
  let env ← getEnv
  let roots := communityDecls env
  let found := reachableAxioms env roots
  let offending := found.toList.filter fun ax => !allowed.contains ax
  if offending.isEmpty then
    logInfo m!"axiom audit: {roots.size} ArlibCommunity declarations, axioms used = \
      {found.toList}, all allowed."
  else
    throwError m!"AXIOM AUDIT FAILED — disallowed axioms: {offending}"
