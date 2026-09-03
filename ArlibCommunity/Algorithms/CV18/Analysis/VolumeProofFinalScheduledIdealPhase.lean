/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCountedChronologicalContinuation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledCostChain

/-! # Exact ideal-prefix inputs for counted scheduled phases -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib _root_.Arlib.MarkovChains

/-- The exact retained endpoint marginal from which chronological phase
`phase` is charged.  Phase zero starts from target zero; every later phase
starts from the preceding accepted target. -/
noncomputable def figureOneFinalScheduledIdealPhaseStart
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measure (Option (AmbientSpace q.n)) :=
  if phase = 0 then (figureOneScheduledAcceptedTargetAt q I 0).map some
  else (figureOneScheduledAcceptedTargetAt q I (phase - 1)).map some

theorem figureOneFinalScheduledIdealPhaseStart_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    IsProbabilityMeasure (figureOneFinalScheduledIdealPhaseStart q I phase) := by
  unfold figureOneFinalScheduledIdealPhaseStart
  split_ifs
  · let _ : IsProbabilityMeasure (figureOneScheduledAcceptedTargetAt q I 0) :=
      figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
    exact Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  · let _ : IsProbabilityMeasure
        (figureOneScheduledAcceptedTargetAt q I (phase - 1)) :=
      figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I (phase - 1)
    exact Measure.isProbabilityMeasure_map measurable_some.aemeasurable

private theorem finalIdealWarmConstant_le_ninetySix (q : VolumeParams) :
    8 * ENNReal.ofReal (speedyAdjacentWarmConstant q) ≤ 96 := by
  calc
    8 * ENNReal.ofReal (speedyAdjacentWarmConstant q) ≤ 8 * 12 := by
      gcongr
      rw [← ENNReal.ofReal_ofNat 12]
      exact ENNReal.ofReal_le_ofReal (speedyAdjacentWarmConstant_le_twelve q)
    _ = 96 := by norm_num

/-- The contracted live part of every exact ideal phase start has the one
constant warmness used by the cap-independent phase-cost estimate. -/
theorem figureOneFinalScheduledIdealPhaseStart_scaled_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    let target : Measure (AmbientSpace q.n) :=
      if phase = 0 then figureOneScheduledAcceptedTargetAt q I 0
      else figureOneScheduledAcceptedTargetAt q I (phase - 1)
    IsWarm (8 * ENNReal.ofReal (speedyAdjacentWarmConstant q))
      (target.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I phase) := by
  dsimp only
  by_cases hzero : phase = 0
  · subst phase
    simp only [if_pos]
    have hwarm8 := initialContractedAcceptedTarget_isWarm_eight q I
    apply hwarm8.mono
    have hC : (1 : ENNReal) ≤ ENNReal.ofReal (speedyAdjacentWarmConstant q) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (speedyAdjacentWarmConstant_one_le q)
    calc
      (8 : ENNReal) = 8 * 1 := by norm_num
      _ ≤ 8 * ENNReal.ofReal (speedyAdjacentWarmConstant q) := by gcongr
  · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    simpa [figureOneScheduledAcceptedTargetAt,
      figureOneScheduledSpeedyPiAt] using
      map_scheduledBalancedAcceptedTarget_scale_adjacent_isWarm q I previous

/-- A Gaussian phase run from its exact chronological ideal marginal incurs
only the warm-start term.  In particular there is no local-cap multiple of a
retained approximation error. -/
theorem figureOneFinalScheduledGaussianIdealPhaseExpectedCost_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) :
    (∫⁻ state, countedQueryCost
      ((figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).run
        oracle.query) ∂figureOneFinalScheduledIdealPhaseStart q I phase) ≤
      ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
        figureOneFinalScheduledBalancedParameters.retryLimit q
          (scheduleValue q phase) *
        figureOneFinalScheduledBalancedParameters.properStride q
          (scheduleValue q phase)) : ℕ) : ENNReal) := by
  let target : Measure (AmbientSpace q.n) :=
    if phase = 0 then figureOneScheduledAcceptedTargetAt q I 0
    else figureOneScheduledAcceptedTargetAt q I (phase - 1)
  let _ : IsProbabilityMeasure target := by
    dsimp only [target]
    split_ifs
    · exact figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
    · exact figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I (phase - 1)
  have hideal : figureOneFinalScheduledIdealPhaseStart q I phase =
      target.map some := by
    unfold figureOneFinalScheduledIdealPhaseStart target
    split_ifs <;> rfl
  have hwarm := figureOneFinalScheduledIdealPhaseStart_scaled_isWarm q I phase
  have hbound :=
    lintegral_optional_scheduledCollector_cost_le_finalEnvelope_of_leUpTo
      q I oracle (scheduleValue_pos q phase)
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledIdealPhaseStart q I phase) target
      (by rw [hideal]; exact MeasureLeUpTo.refl (target.map some))
      hwarm (finalIdealWarmConstant_le_ninetySix q)
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase))
      (figureOnePhaseSampleCount q (scheduleValue q phase))
      (figureOneScheduledCorrectedProperStride_pos q (scheduleValue q phase)
        (figureOneSafeRetryCount q - 1))
  have hcost : (∫⁻ state, countedQueryCost
      ((figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).run
        oracle.query) ∂figureOneFinalScheduledIdealPhaseStart q I phase) =
      ∫⁻ state, match state with
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
              (accuracyScaleFactor q • point)).run oracle.query)
        ∂figureOneFinalScheduledIdealPhaseStart q I phase := by
    apply lintegral_congr
    intro state
    exact figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
      q I oracle phase state
  rw [hcost]
  exact hbound.trans (by push_cast; simp [mul_comm, mul_left_comm, mul_assoc])

/-- One exact ideal start followed by the executable retained phase has the
next accepted-target marginal up to exactly the per-sample transition loss. -/
theorem figureOneFinalScheduledGaussianIdealPhaseEndpoint_leUpTo
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase : ℕ) :
    MeasureLeUpTo
      ((figureOneFinalScheduledIdealPhaseStart q I phase).bind fun state =>
        (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).runEstimate
          oracle.query)
      ((figureOneScheduledAcceptedTargetAt q I phase).map some)
      (figureOnePhaseSampleCount q (scheduleValue q phase) •
        figureOneCorrectedTransitionBudget q) := by
  let target : Measure (AmbientSpace q.n) :=
    if phase = 0 then figureOneScheduledAcceptedTargetAt q I 0
    else figureOneScheduledAcceptedTargetAt q I (phase - 1)
  let _ : IsProbabilityMeasure target := by
    dsimp only [target]
    split_ifs
    · exact figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I 0
    · exact figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I (phase - 1)
  have hideal : figureOneFinalScheduledIdealPhaseStart q I phase =
      target.map some := by
    unfold figureOneFinalScheduledIdealPhaseStart target
    split_ifs <;> rfl
  have hwarm := figureOneFinalScheduledIdealPhaseStart_scaled_isWarm q I phase
  have hwarm' : IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (target.map fun point => accuracyScaleFactor q • point)
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I (scheduleValue q phase))
        (figureOneScheduledProposalRadius q (scheduleValue q phase))
        (scheduleValue q phase)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    simpa [figureOneScheduledSpeedyPiAt] using hwarm
  have hcount : 0 < figureOnePhaseSampleCount q (scheduleValue q phase) := by
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  have hphase := bind_figureOneFinalScheduledCompleteRetainedKernel_leUpTo
    q I (scheduleValue_pos q phase)
    (measurable_gaussianRatioWeight (scheduleValue q phase)
      (scheduleValue q (phase + 1)))
    (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
    (figureOneFinalScheduledIdealPhaseStart q I phase) target
    (priorError := 0)
    (by rw [hideal]; exact MeasureLeUpTo.refl (target.map some)) hwarm'
  have hrun : (fun state =>
      (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).runEstimate
        oracle.query) =
      figureOneFinalScheduledCompleteRetainedKernel q I
        (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1) := by
    funext state
    exact figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
      q I oracle phase state
  rw [hrun]
  simpa [figureOneScheduledAcceptedTargetAt,
    figureOneScheduledSpeedyPiAt, Nat.sub_add_cancel hcount] using hphase

#print axioms figureOneFinalScheduledGaussianIdealPhaseExpectedCost_le
#print axioms figureOneFinalScheduledGaussianIdealPhaseEndpoint_leUpTo

end ArlibCommunity.Algorithms.CV18
