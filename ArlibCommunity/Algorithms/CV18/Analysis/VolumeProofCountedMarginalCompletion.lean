/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import Mathlib.Probability.Kernel.Disintegration.Integral

/-! # Cost-preserving completion of an approximate endpoint marginal -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem compProd_mono_left_cv18
    {S C : Type*} [MeasurableSpace S] [MeasurableSpace C]
    {mu nu : Measure S} [SFinite mu] [SFinite nu]
    (h : mu ≤ nu) (K : Kernel S C) [IsSFiniteKernel K] :
    mu.compProd K ≤ nu.compProd K := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.compProd_apply hA, Measure.compProd_apply hA]
  exact lintegral_mono' h le_rfl

/-- A small additive error in the endpoint marginal of a counted law can be
lifted to the full counted law without paying a syntactic cost cap.

The reference keeps the largest sublaw needed from the original experiment,
and completes the missing endpoint mass at count zero.  Consequently its
endpoint marginal is exactly `target`, its expected count is no larger than
the original expected count, and the discarded joint mass is at most the
original marginal error. -/
theorem exists_countedReference_of_fst_leUpTo
    {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (joint : Measure (S × ℕ)) [IsFiniteMeasure joint]
    (target : Measure S) [IsFiniteMeasure target]
    {delta : ENNReal}
    (hmargin : MeasureLeUpTo joint.fst target delta) :
    ∃ reference : Measure (S × ℕ),
      MeasureLeUpTo joint reference delta ∧
      reference.fst = target ∧
      (∫⁻ outcome, (outcome.2 : ENNReal) ∂reference) ≤
        ∫⁻ outcome, (outcome.2 : ENNReal) ∂joint := by
  let marginal := joint.fst
  let badMarginal := marginal - target
  let conditional : Kernel S ℕ := joint.condKernel
  let badJoint := badMarginal.compProd conditional
  let goodJoint := joint - badJoint
  have hbadMarginal : badMarginal ≤ marginal := by
    exact Measure.sub_le
  have hbadJoint : badJoint ≤ joint := by
    calc
      badJoint ≤ marginal.compProd conditional :=
        compProd_mono_left_cv18 hbadMarginal conditional
      _ = joint := by
        exact joint.disintegrate conditional
  have hsplit : goodJoint + badJoint = joint := by
    exact Measure.sub_add_cancel_of_le hbadJoint
  have hmarginalLe : marginal ≤ badMarginal + target := by
    exact (Measure.sub_le_iff_le_add (μ := marginal) (ν := target)
      (ξ := badMarginal)).mp le_rfl
  have hjointLe : joint ≤ target.compProd conditional + badJoint := by
    calc
      joint = marginal.compProd conditional :=
        (joint.disintegrate conditional).symm
      _ ≤ (badMarginal + target).compProd conditional :=
        compProd_mono_left_cv18 hmarginalLe conditional
      _ = badJoint + target.compProd conditional := by
        rw [Measure.compProd_add_left]
      _ = target.compProd conditional + badJoint := add_comm _ _
  have hgoodJoint : goodJoint ≤ target.compProd conditional := by
    exact Measure.sub_le_of_le_add (by simpa [add_comm] using hjointLe)
  have hgoodMargin : goodJoint.fst ≤ target := by
    calc
      goodJoint.fst ≤ (target.compProd conditional).fst := by
        exact Measure.map_mono hgoodJoint measurable_fst
      _ = target := Measure.fst_compProd target conditional
  let missing := target - goodJoint.fst
  let zeroCount : S → S × ℕ := fun state => (state, 0)
  let reference := goodJoint + missing.map zeroCount
  refine ⟨reference, ?_, ?_, ?_⟩
  · obtain ⟨error, hle, herror⟩ := hmargin
    have hbadMarginalError : badMarginal ≤ error := by
      apply Measure.sub_le_of_le_add
      simpa [add_comm] using hle
    have hbadMass : badMarginal Set.univ ≤ delta := by
      exact (Measure.le_iff'.mp hbadMarginalError Set.univ).trans herror
    refine ⟨badJoint, ?_, ?_⟩
    · rw [← hsplit]
      change goodJoint + badJoint ≤
        (goodJoint + missing.map zeroCount) + badJoint
      exact add_le_add (Measure.le_add_right le_rfl) le_rfl
    · simpa [badJoint] using hbadMass
  · have hmissingSplit : missing + goodJoint.fst = target := by
      exact Measure.sub_add_cancel_of_le hgoodMargin
    change (goodJoint + missing.map zeroCount).map Prod.fst = target
    rw [Measure.map_add goodJoint (missing.map zeroCount) measurable_fst]
    change goodJoint.fst + (missing.map zeroCount).map Prod.fst = target
    rw [Measure.map_map measurable_fst (by fun_prop)]
    have hcomp : Prod.fst ∘ zeroCount = id := by
      funext state
      rfl
    rw [hcomp, Measure.map_id]
    simpa [add_comm] using hmissingSplit
  · have hgoodLe : goodJoint ≤ joint := Measure.sub_le
    calc
      (∫⁻ outcome, (outcome.2 : ENNReal) ∂reference) =
          (∫⁻ outcome, (outcome.2 : ENNReal) ∂goodJoint) +
            ∫⁻ outcome, (outcome.2 : ENNReal) ∂missing.map zeroCount := by
        rw [lintegral_add_measure]
      _ = (∫⁻ outcome, (outcome.2 : ENNReal) ∂goodJoint) + 0 := by
        congr 1
        rw [lintegral_map (by fun_prop) (by fun_prop)]
        simp
      _ = ∫⁻ outcome, (outcome.2 : ENNReal) ∂goodJoint := add_zero _
      _ ≤ ∫⁻ outcome, (outcome.2 : ENNReal) ∂joint :=
        lintegral_mono' hgoodLe le_rfl

#print axioms exists_countedReference_of_fst_leUpTo

end ArlibCommunity.Algorithms.CV18
