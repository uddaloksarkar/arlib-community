/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledIdealPhase
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCountedHybridCap

/-! # The cheap initial-abort branch and the final global query cap

The failed initial rejection branch performs exactly one query.  It is
therefore absent from the event that the global query budget is exceeded.
This file starts the chronological counted reference from the exact ideal
phase-zero law, and transfers only that expensive-count event from the actual
initializer.  No initial-tail probability is charged to runtime.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Exact ideal phase-zero state paired with the one query already spent by
the executable initializer. -/
noncomputable def figureOneFinalScheduledIdealCountedInitial
    (q : VolumeParams) (I : VolumeInput q.n) :
    Measure (Option (AmbientSpace q.n) × ℕ) :=
  (figureOneFinalScheduledIdealPhaseStart q I 0).map fun state => (state, 1)

theorem figureOneFinalScheduledIdealCountedInitial_fst
    (q : VolumeParams) (I : VolumeInput q.n) :
    (figureOneFinalScheduledIdealCountedInitial q I).fst =
      figureOneFinalScheduledIdealPhaseStart q I 0 := by
  unfold figureOneFinalScheduledIdealCountedInitial Measure.fst
  rw [Measure.map_map measurable_fst (by fun_prop)]
  have hcomp : (Prod.fst ∘ fun state : Option (AmbientSpace q.n) =>
      (state, 1)) = id := by
    funext state
    rfl
  rw [hcomp, Measure.map_id]

theorem figureOneFinalScheduledIdealCountedInitial_cost
    (q : VolumeParams) (I : VolumeInput q.n) :
    countedQueryCost (figureOneFinalScheduledIdealCountedInitial q I) = 1 := by
  unfold countedQueryCost figureOneFinalScheduledIdealCountedInitial
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  let _ : IsProbabilityMeasure
      (figureOneFinalScheduledIdealPhaseStart q I 0) :=
    figureOneFinalScheduledIdealPhaseStart_isProbabilityMeasure q I 0
  simp

/-- Chronological counted reference started from the exact ideal phase-zero
law.  Its only discrepancy is the sum of phase exact-chance errors. -/
theorem exists_figureOneFinalScheduledIdealGaussianCountedReference
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (steps : ℕ) :
    ∃ reference : Measure (Option (AmbientSpace q.n) × ℕ),
      MeasureLeUpTo
        (iteratedKernelLaw
          (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
          (figureOneFinalScheduledIdealCountedInitial q I) steps)
        reference
        (∑ phase ∈ Finset.range steps,
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q) ∧
      reference.fst = figureOneFinalScheduledIdealPhaseStart q I steps ∧
      countedQueryCost reference ≤
        1 + ∑ phase ∈ Finset.range steps,
          ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q phase) *
            figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q phase)) : ℕ) : ENNReal) := by
  let ideal := figureOneFinalScheduledIdealPhaseStart q I
  let phaseCost : ℕ → ENNReal := fun phase =>
    ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
      figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase) *
      figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase)) : ℕ) : ENNReal)
  let _ : IsProbabilityMeasure
      (figureOneFinalScheduledIdealCountedInitial q I) := by
    unfold figureOneFinalScheduledIdealCountedInitial
    let _ : IsProbabilityMeasure
        (figureOneFinalScheduledIdealPhaseStart q I 0) :=
      figureOneFinalScheduledIdealPhaseStart_isProbabilityMeasure q I 0
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hreference := exists_countedReference_iteratedKernelLaw
    (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
    (figureOneFinalScheduledIdealCountedInitial q I) ideal
    (initialError := 0)
    (fun phase => figureOnePhaseSampleCount q (scheduleValue q phase) •
      figureOneCorrectedTransitionBudget q)
    phaseCost
    (fun phase => by
      let _ : IsProbabilityMeasure (ideal phase) :=
        figureOneFinalScheduledIdealPhaseStart_isProbabilityMeasure q I phase
      infer_instance)
    (by
      rw [figureOneFinalScheduledIdealCountedInitial_fst]
      exact MeasureLeUpTo.refl (ideal 0))
    (fun phase => by
      unfold figureOneFinalScheduledGaussianCountedKernel
      exact measurable_countedContinuation oracle.query _
        (figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase).1
        (figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase).2)
    (fun phase state => by
      unfold figureOneFinalScheduledGaussianCountedKernel countedContinuation
      let _ : IsProbabilityMeasure
          ((figureOneFinalScheduledRetainedGaussianPhaseProgram
            q phase state.1).run oracle.query) :=
        MembershipOracleProgram.run_isProbabilityMeasure oracle.query _
          ((figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
            q I oracle phase).2 state.1).executionMeasurable
      exact Measure.isProbabilityMeasure_map (by fun_prop))
    (fun phase rho _hrho hmarginal => by
      have hprogram :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase
      have hnext : ideal (phase + 1) =
          (figureOneScheduledAcceptedTargetAt q I phase).map some := by
        simp [ideal, figureOneFinalScheduledIdealPhaseStart]
      apply MembershipOracleProgram.countedContinuation_step oracle.query rho
        (ideal phase) (ideal (phase + 1))
        (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase)
        hprogram.1 hprogram.2 hmarginal
      · rw [hnext]
        exact figureOneFinalScheduledGaussianIdealPhaseEndpoint_leUpTo
          q I oracle phase
      · exact figureOneFinalScheduledGaussianIdealPhaseExpectedCost_le
          q I oracle phase)
    steps
  obtain ⟨reference, hdom, hmarginal, hcost⟩ := hreference
  refine ⟨reference, ?_, hmarginal, ?_⟩
  · simpa using hdom
  · change countedQueryCost reference ≤
      countedQueryCost (figureOneFinalScheduledIdealCountedInitial q I) +
        ∑ phase ∈ Finset.range steps, phaseCost phase at hcost
    rw [figureOneFinalScheduledIdealCountedInitial_cost] at hcost
    exact hcost

end ArlibCommunity.Algorithms.CV18
