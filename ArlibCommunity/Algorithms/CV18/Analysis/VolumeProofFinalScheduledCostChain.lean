/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledPhaseCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCostComposition

/-! # A retained-state interpreter for final scheduled cost accounting -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- One Gaussian phase, retaining only the endpoint needed by the next phase.
This erases only query-free estimator coordinates. -/
noncomputable def figureOneFinalScheduledRetainedGaussianPhaseProgram
    (q : VolumeParams) (phase : ℕ) :
    Option (AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  | none => .pure none
  | some point =>
      (scheduledBalancedAccuracyRetryCollect q (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOneFinalScheduledBalancedParameters.proposalCap q
          (scheduleValue q phase))
        (figureOneFinalScheduledBalancedParameters.properStride q
          (scheduleValue q phase))
        (figureOneFinalScheduledBalancedParameters.retryLimit q
          (scheduleValue q phase))
        (figureOnePhaseSampleCount q (scheduleValue q phase))
        (accuracyScaleFactor q • point)).bind fun result =>
          .pure (optionSnd result)

theorem figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) :
    (Measurable fun state =>
      (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).run
        oracle.query) ∧
    ∀ state,
      (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).CountedStronglyMeasurable
        oracle.query := by
  let collect (point : AmbientSpace q.n) :=
    scheduledBalancedAccuracyRetryCollect q (scheduleValue q phase)
      (gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase))
      (figureOnePhaseSampleCount q (scheduleValue q phase))
      (accuracyScaleFactor q • point)
  have hscale : Measurable fun point : AmbientSpace q.n =>
      accuracyScaleFactor q • point := by fun_prop
  have hcollectBase := scheduledBalancedAccuracyRetryCollect_countedMeasurable
    q I oracle (scheduleValue_pos q phase)
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase))
      (figureOnePhaseSampleCount q (scheduleValue q phase))
  have hcollectMeas : Measurable fun point => (collect point).run oracle.query :=
    hcollectBase.1.comp hscale
  have hcollect : ∀ point, (collect point).CountedStronglyMeasurable oracle.query :=
    fun point => hcollectBase.2 (accuracyScaleFactor q • point)
  have hsome := MembershipOracleProgram.countedMeasurable_bind_pure
    oracle.query collect (fun z : AmbientSpace q.n ×
      Option (ℝ × AmbientSpace q.n) => optionSnd z.2)
      hcollectMeas hcollect (measurable_optionSnd.comp measurable_snd)
  constructor
  · convert Measurable.optionElim
      (Measure.dirac ((none : Option (AmbientSpace q.n)), 0)) hsome.1 using 1
    funext state
    cases state <;> rfl
  · intro state
    cases state with
    | none => trivial
    | some point => exact hsome.2 point

theorem figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) (state : Option (AmbientSpace q.n)) :
    countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).run
          oracle.query) =
      match state with
      | none => 0
      | some point => countedQueryCost
          ((scheduledBalancedAccuracyRetryCollect q (scheduleValue q phase)
            (gaussianRatioWeight (scheduleValue q phase)
              (scheduleValue q (phase + 1)))
            (figureOneFinalScheduledBalancedParameters.proposalCap q
              (scheduleValue q phase))
            (figureOneFinalScheduledBalancedParameters.properStride q
              (scheduleValue q phase))
            (figureOneFinalScheduledBalancedParameters.retryLimit q
              (scheduleValue q phase))
            (figureOnePhaseSampleCount q (scheduleValue q phase))
            (accuracyScaleFactor q • point)).run oracle.query) := by
  cases state with
  | none =>
      exact MembershipOracleProgram.countedQueryCost_pure oracle.query none
  | some point =>
      unfold figureOneFinalScheduledRetainedGaussianPhaseProgram
      exact MembershipOracleProgram.countedQueryCost_bind_pure_eq
        oracle.query _ optionSnd measurable_optionSnd
          ((scheduledBalancedAccuracyRetryCollect_countedMeasurable
            q I oracle (scheduleValue_pos q phase)
              (measurable_gaussianRatioWeight (scheduleValue q phase)
                (scheduleValue q (phase + 1)))
              (figureOneFinalScheduledBalancedParameters.proposalCap q
                (scheduleValue q phase))
              (figureOneFinalScheduledBalancedParameters.properStride q
                (scheduleValue q phase))
              (figureOneFinalScheduledBalancedParameters.retryLimit q
                (scheduleValue q phase))
              (figureOnePhaseSampleCount q (scheduleValue q phase))).2 _)

theorem figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) (state : Option (AmbientSpace q.n)) :
    (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).runEstimate
        oracle.query =
      figureOneFinalScheduledCompleteRetainedKernel q I
        (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1) state := by
  cases state with
  | none => rfl
  | some point =>
      have hcollect := (scheduledBalancedAccuracyRetryCollect_countedMeasurable
        q I oracle (scheduleValue_pos q phase)
          (measurable_gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q phase))
          (figureOnePhaseSampleCount q (scheduleValue q phase))).2
            (accuracyScaleFactor q • point)
      unfold figureOneFinalScheduledRetainedGaussianPhaseProgram
      have hcount : 0 < figureOnePhaseSampleCount q (scheduleValue q phase) := by
        unfold figureOnePhaseSampleCount
        split_ifs
        · exact figureOneFixedSampleCount_pos q
        · exact figureOneSampleCount_pos q
      rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
        hcollect.stronglyMeasurable]
      · rw [scheduledBalancedAccuracyRetryCollect_runEstimate_eq_transitionCollectLaw
          q I oracle (scheduleValue_pos q phase)
            (measurable_gaussianRatioWeight (scheduleValue q phase)
              (scheduleValue q (phase + 1)))]
        simp only [MembershipOracleProgram.runEstimate]
        rw [Measure.bind_dirac_eq_map _ measurable_optionSnd]
        unfold figureOneFinalScheduledCompleteRetainedKernel
        rw [Nat.sub_add_cancel hcount]
        rw [scheduledBalancedAccuracyTransitionCollectLaw_eq_chronological]
      · intro result
        trivial
      · simp only [MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp measurable_optionSnd

#print axioms figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
#print axioms figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate

end ArlibCommunity.Algorithms.CV18
