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

/-- Execute a consecutive block of Gaussian phases while retaining only the
optional endpoint. -/
noncomputable def figureOneFinalScheduledRetainedGaussianChain
    (q : VolumeParams) : ℕ → ℕ → Option (AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  | _, 0, state => .pure state
  | phase, steps + 1, state =>
      (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).bind
        (figureOneFinalScheduledRetainedGaussianChain q (phase + 1) steps)

theorem figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ phase steps,
      (Measurable fun state =>
        (figureOneFinalScheduledRetainedGaussianChain q phase steps state).run
          oracle.query) ∧
      ∀ state,
        (figureOneFinalScheduledRetainedGaussianChain q phase steps state).CountedStronglyMeasurable
          oracle.query := by
  intro phase steps
  induction steps generalizing phase with
  | zero =>
      constructor
      · simp only [figureOneFinalScheduledRetainedGaussianChain,
          MembershipOracleProgram.run]
        exact Measure.measurable_dirac.comp (measurable_id.prodMk measurable_const)
      · intro state
        trivial
  | succ steps ih =>
      have hphase :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase
      have htail := ih (phase + 1)
      simp only [figureOneFinalScheduledRetainedGaussianChain]
      constructor
      · exact MembershipOracleProgram.measurable_run_bind_param oracle.query
          (figureOneFinalScheduledRetainedGaussianPhaseProgram q phase)
          (fun z => figureOneFinalScheduledRetainedGaussianChain q
            (phase + 1) steps z.2)
          hphase.1 hphase.2 (htail.1.comp measurable_snd)
          (fun z => htail.2 z.2)
      · intro state
        exact (hphase.2 state).bind htail.2 htail.1

/-- Recursive chronological sum of the Gaussian phase costs. -/
noncomputable def figureOneFinalScheduledGaussianPhaseCostTail
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ℕ → ℕ → ENNReal
  | _, 0 => 0
  | phase, steps + 1 =>
      figureOneFinalScheduledGaussianPhaseExpectedCost q I oracle phase +
        figureOneFinalScheduledGaussianPhaseCostTail q I oracle
          (phase + 1) steps

/-- One front step of the retained chain contributes its local expected cost,
then transports the remaining cost through the exact retained endpoint
kernel. -/
theorem lintegral_figureOneFinalScheduledRetainedGaussianChain_succ
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (phase steps : ℕ) (mu : Measure (Option (AmbientSpace q.n))) :
    (∫⁻ state, countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianChain q phase (steps + 1)
          state).run oracle.query) ∂mu) =
      (∫⁻ state, countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianPhaseProgram q phase state).run
          oracle.query) ∂mu) +
      ∫⁻ state, countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianChain q (phase + 1) steps
          state).run oracle.query)
        ∂(mu.bind (figureOneFinalScheduledCompleteRetainedKernel q I
          (scheduleValue q phase)
          (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOnePhaseSampleCount q (scheduleValue q phase) - 1))) := by
  let phaseProgram := figureOneFinalScheduledRetainedGaussianPhaseProgram q phase
  let tailProgram := figureOneFinalScheduledRetainedGaussianChain q (phase + 1) steps
  let retainedKernel := figureOneFinalScheduledCompleteRetainedKernel q I
    (scheduleValue q phase)
    (gaussianRatioWeight (scheduleValue q phase) (scheduleValue q (phase + 1)))
    (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
  have hphase :=
    figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
      q I oracle phase
  have htail := figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
    q I oracle (phase + 1) steps
  have hphaseCost : Measurable fun state =>
      countedQueryCost ((phaseProgram state).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hphase.1
  have htailCost : Measurable fun state =>
      countedQueryCost ((tailProgram state).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      htail.1
  have hpoint : ∀ state,
      countedQueryCost
          (((phaseProgram state).bind tailProgram).run oracle.query) =
        countedQueryCost ((phaseProgram state).run oracle.query) +
          ∫⁻ next, countedQueryCost ((tailProgram next).run oracle.query)
            ∂((phaseProgram state).runEstimate oracle.query) := by
    intro state
    exact MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
      (phaseProgram state) tailProgram (hphase.2 state) htail.2 htail.1
  simp only [figureOneFinalScheduledRetainedGaussianChain]
  rw [lintegral_congr hpoint, lintegral_add_left hphaseCost]
  rw [Measure.lintegral_bind]
  · congr 1
    apply lintegral_congr
    intro state
    rw [show (phaseProgram state).runEstimate oracle.query =
        retainedKernel state from
      figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
        q I oracle phase state]
  · exact (figureOneFinalScheduledCompleteRetainedKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
        (measurable_gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)).1.aemeasurable
  · exact htailCost.aemeasurable

/-- The retained law after one more Gaussian phase is exactly the next trace
marginal. -/
theorem figureOneFinalScheduledTraceRetained_succ
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    ((scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I phase).map
        scheduledBalancedTraceRetainedOption).bind
      (figureOneFinalScheduledCompleteRetainedKernel q I
        (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)) =
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I (phase + 1)).map
          scheduledBalancedTraceRetainedOption := by
  rw [show scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (phase + 1) =
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I phase).bind
            (scheduledBalancedTracePhaseKernel
              figureOneFinalScheduledBalancedParameters q I phase) by rfl]
  exact (map_bind_scheduledBalancedTracePhaseKernel_retainedOption
    q I phase hphase _).symm

/-- Exact additive accounting for any suffix of the chronological Gaussian
schedule, started from its true optional retained-state marginal. -/
theorem lintegral_figureOneFinalScheduledRetainedGaussianChain_eq_costTail
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ phase steps, phase + steps ≤ terminalPhaseSteps q →
    (∫⁻ state, countedQueryCost
        ((figureOneFinalScheduledRetainedGaussianChain q phase steps state).run
          oracle.query)
      ∂((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I phase).map
          scheduledBalancedTraceRetainedOption)) =
      figureOneFinalScheduledGaussianPhaseCostTail q I oracle phase steps := by
  intro phase steps
  induction steps generalizing phase with
  | zero =>
      intro _
      simp only [figureOneFinalScheduledRetainedGaussianChain,
        figureOneFinalScheduledGaussianPhaseCostTail,
        MembershipOracleProgram.countedQueryCost_pure]
      simp
  | succ steps ih =>
      intro hbound
      have hphase : phase < terminalPhaseSteps q := by omega
      rw [lintegral_figureOneFinalScheduledRetainedGaussianChain_succ]
      rw [figureOneFinalScheduledTraceRetained_succ q I phase hphase]
      rw [ih (phase + 1) (by omega)]
      rw [figureOneFinalScheduledGaussianPhaseCostTail]
      congr 1
      unfold figureOneFinalScheduledGaussianPhaseExpectedCost
      apply lintegral_congr
      intro state
      exact figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
        q I oracle phase state

#print axioms figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
#print axioms figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
#print axioms lintegral_figureOneFinalScheduledRetainedGaussianChain_eq_costTail

end ArlibCommunity.Algorithms.CV18
