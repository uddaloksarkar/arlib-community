/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCountedChronologicalContinuation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledCostChain
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledAbortAccuracy

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

/-- The paper-faithful aborting initial sample differs from the normalized
truncated Gaussian retained law only by the rejected Gaussian tail mass. -/
theorem figureOneAbortInitialRetained_leUpTo_truncated
    (q : VolumeParams) (I : VolumeInput q.n) :
    MeasureLeUpTo
      ((initialGaussianSamplingMeasure q).map (initialTruncatedOption q I))
      ((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).map some)
      (ENNReal.ofReal (q.eps / 64)) := by
  let actual := (initialGaussianSamplingMeasure q).map
    (initialTruncatedOption q I)
  let target := (truncatedGaussianProbability q I (initialVariance q)
    (initialVariance_pos q) : Measure (AmbientSpace q.n)).map some
  let _ : IsProbabilityMeasure actual :=
    Measure.isProbabilityMeasure_map
      (measurable_initialTruncatedOption q I).aemeasurable
  let _ : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  apply MeasureLeUpTo.of_tvLe
  apply Arlib.tvLe_of_forall_le
  intro event hevent
  have h := initialTruncatedOption_bind_apply_le q I
    (Measure.dirac (none : Option (AmbientSpace q.n))) inferInstance
    (fun point => Measure.dirac (some point))
    (Measure.measurable_dirac.comp measurable_some)
    (fun _ => inferInstance) event hevent
  have hleft :
      ((initialGaussianSamplingMeasure q).map
        (initialTruncatedOption q I)).bind (fun initialPoint =>
          match initialPoint with
          | none => Measure.dirac none
          | some point => Measure.dirac (some point)) = actual := by
    have hkernel : (fun initialPoint : Option (AmbientSpace q.n) =>
        match initialPoint with
        | none => Measure.dirac none
        | some point => Measure.dirac (some point)) = Measure.dirac := by
      funext initialPoint
      cases initialPoint <;> rfl
    rw [hkernel, Measure.bind_dirac]
  have hright :
      (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          (fun point => Measure.dirac (some point)) = target := by
    rw [Measure.bind_dirac_eq_map _ measurable_some]
  change actual event ≤ target event + ENNReal.ofReal (q.eps / 64)
  calc
    actual event =
        (((initialGaussianSamplingMeasure q).map
          (initialTruncatedOption q I)).bind (fun initialPoint =>
            match initialPoint with
            | none => Measure.dirac none
            | some point => Measure.dirac (some point))) event := by
      rw [hleft]
    _ ≤ ((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
            (fun point => Measure.dirac (some point))) event +
          ENNReal.ofReal (q.eps / 64) := h
    _ = target event + ENNReal.ofReal (q.eps / 64) := by
      rw [hright]

/-- The counted aborting initial sampler has the exact first ideal marginal
up to the one truncation-tail loss and one stationary-target loss. -/
theorem figureOneAbortInitialRun_fst_leUpTo_idealPhaseStart
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    MeasureLeUpTo ((figureOneAbortInitialSample q).run oracle.query).fst
      (figureOneFinalScheduledIdealPhaseStart q I 0)
      (ENNReal.ofReal (q.eps / 64) +
        scheduledBalancedStationaryTargetError q) := by
  have habort := figureOneAbortInitialRetained_leUpTo_truncated q I
  have hstationary := scheduledBalancedInitialRetained_leUpTo_target q I
  rw [map_scheduledBalancedInitialTrace_retainedOption] at hstationary
  have hrun : ((figureOneAbortInitialSample q).run oracle.query).fst =
      (figureOneAbortInitialSample q).runEstimate oracle.query := by
    exact ((figureOneAbortInitialSample q).runEstimate_eq_map_fst_run
      oracle.query
      (figureOneAbortInitialSample_countedStronglyMeasurable
        q I oracle).executionMeasurable).symm
  rw [hrun, runEstimate_figureOneAbortInitialSample q I oracle]
  simpa [figureOneFinalScheduledIdealPhaseStart] using
    habort.trans hstationary

/-- The counted transition kernel for chronological retained Gaussian
phases. -/
noncomputable def figureOneFinalScheduledGaussianCountedKernel
    (q : VolumeParams) (oracle : AmbientSpace q.n → Bool) (phase : ℕ) :=
  countedContinuation oracle
    (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase)

/-- Finite chronological reference for every prefix of Gaussian phases.
The reference has the exact ideal retained-point marginal, additive
exact-chance loss, and only the sum of warm expected phase costs. -/
theorem exists_figureOneFinalScheduledGaussianCountedReference
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (steps : ℕ) :
    ∃ reference : Measure (Option (AmbientSpace q.n) × ℕ),
      MeasureLeUpTo
        (iteratedKernelLaw
          (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
          ((figureOneAbortInitialSample q).run oracle.query) steps)
        reference
        ((ENNReal.ofReal (q.eps / 64) +
            scheduledBalancedStationaryTargetError q) +
          ∑ phase ∈ Finset.range steps,
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
  have hinitialStrong :=
    figureOneAbortInitialSample_countedStronglyMeasurable q I oracle
  let _ : IsProbabilityMeasure
      ((figureOneAbortInitialSample q).run oracle.query) :=
    MembershipOracleProgram.run_isProbabilityMeasure oracle.query _
      hinitialStrong.executionMeasurable
  let ideal := figureOneFinalScheduledIdealPhaseStart q I
  let phaseCost : ℕ → ENNReal := fun phase =>
    ((384 * (figureOnePhaseSampleCount q (scheduleValue q phase) *
      figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase) *
      figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase)) : ℕ) : ENNReal)
  have hreference := exists_countedReference_iteratedKernelLaw
    (figureOneFinalScheduledGaussianCountedKernel q oracle.query)
    ((figureOneAbortInitialSample q).run oracle.query) ideal
    (fun phase => figureOnePhaseSampleCount q (scheduleValue q phase) •
      figureOneCorrectedTransitionBudget q)
    phaseCost
    (fun phase => by
      let _ : IsProbabilityMeasure (ideal phase) := by
        exact figureOneFinalScheduledIdealPhaseStart_isProbabilityMeasure q I phase
      infer_instance)
    (figureOneAbortInitialRun_fst_leUpTo_idealPhaseStart q I oracle)
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
  refine ⟨reference, hdom, hmarginal, ?_⟩
  apply hcost.trans
  gcongr
  simpa only [countedQueryCost, Nat.cast_one] using
    (figureOneAbortInitialSample_queryBound q).lintegral_queryCount_le
      hinitialStrong

#print axioms figureOneFinalScheduledGaussianIdealPhaseExpectedCost_le
#print axioms figureOneFinalScheduledGaussianIdealPhaseEndpoint_leUpTo
#print axioms figureOneAbortInitialRun_fst_leUpTo_idealPhaseStart
#print axioms exists_figureOneFinalScheduledGaussianCountedReference

end ArlibCommunity.Algorithms.CV18
