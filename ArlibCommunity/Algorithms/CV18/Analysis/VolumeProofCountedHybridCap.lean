/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGlobalQueryCap

/-! # Transferring a global query cutoff through a counted hybrid

The CV18 exact-chance replacements are an accuracy argument, not an
unrestricted-runtime argument.  A replacement error must therefore be
charged as probability mass before applying Markov's inequality to the
reference execution.  Charging it at a local syntactic proposal cap loses
the advertised rate.

This file supplies the generic counted-law interface for the paper-faithful
argument.  It deliberately compares full result-and-query-count laws.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

/-- If a counted execution law is dominated by a reference counted law up to
`delta`, global-cap exhaustion is bounded by the reference Markov term plus
`delta`.  In multiplicative form no division or finiteness side condition is
needed. -/
theorem MembershipOracleProgram.mul_runEstimate_withQueryCap_none_le_of_run_leUpTo
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result) (budget : ℕ)
    (hmeas : program.ExecutionMeasurable oracle)
    (reference : Measure (Result × ℕ)) {delta R : ENNReal}
    (hdom : MeasureLeUpTo (program.run oracle) reference delta)
    (href : ∫⁻ outcome, (outcome.2 : ENNReal) ∂reference ≤ R) :
    (budget + 1 : ENNReal) *
        (program.withQueryCap budget).runEstimate oracle {none} ≤
      R + (budget + 1 : ENNReal) * delta := by
  rw [program.runEstimate_withQueryCap_apply_none oracle budget hmeas]
  let expensive : Set (Result × ℕ) := {outcome | budget < outcome.2}
  have hevent := hdom.event_le expensive
  have hmarkov := mul_meas_ge_le_lintegral
    (show Measurable fun outcome : Result × ℕ =>
      (outcome.2 : ENNReal) by fun_prop)
    (budget + 1 : ENNReal) (μ := reference)
  have hexpensive : expensive = {outcome : Result × ℕ |
      (budget + 1 : ENNReal) ≤ (outcome.2 : ENNReal)} := by
    ext outcome
    simp only [expensive, Set.mem_setOf_eq]
    exact_mod_cast Nat.add_one_le_iff
  rw [← hexpensive] at hmarkov
  calc
    (budget + 1 : ENNReal) * (program.run oracle) expensive ≤
        (budget + 1 : ENNReal) * (reference expensive + delta) := by
      gcongr
    _ = (budget + 1 : ENNReal) * reference expensive +
        (budget + 1 : ENNReal) * delta := by ring
    _ ≤ (∫⁻ outcome, (outcome.2 : ENNReal) ∂reference) +
        (budget + 1 : ENNReal) * delta := by gcongr
    _ ≤ R + (budget + 1 : ENNReal) * delta := by gcongr

/-- Event form of the counted-hybrid cutoff estimate. -/
theorem MembershipOracleProgram.runEstimate_withQueryCap_none_le_reference_tail
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result) (budget : ℕ)
    (hmeas : program.ExecutionMeasurable oracle)
    (reference : Measure (Result × ℕ)) {delta : ENNReal}
    (hdom : MeasureLeUpTo (program.run oracle) reference delta) :
    (program.withQueryCap budget).runEstimate oracle {none} ≤
      reference {outcome | budget < outcome.2} + delta := by
  rw [program.runEstimate_withQueryCap_apply_none oracle budget hmeas]
  exact hdom.event_le _

#print axioms
  MembershipOracleProgram.mul_runEstimate_withQueryCap_none_le_of_run_leUpTo
#print axioms
  MembershipOracleProgram.runEstimate_withQueryCap_none_le_reference_tail

end ArlibCommunity.Algorithms.CV18
