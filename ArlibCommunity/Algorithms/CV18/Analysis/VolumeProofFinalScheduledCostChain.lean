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

/-- Averaging the retained Gaussian chain over its true phase-start marginal
produces exactly the later chronological retained marginal. -/
theorem bind_figureOneFinalScheduledRetainedGaussianChain_runEstimate_eq_trace
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ phase steps, phase + steps ≤ terminalPhaseSteps q →
    ((scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I phase).map
        scheduledBalancedTraceRetainedOption).bind (fun state =>
      (figureOneFinalScheduledRetainedGaussianChain q phase steps state).runEstimate
        oracle.query) =
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I (phase + steps)).map
          scheduledBalancedTraceRetainedOption := by
  intro phase steps
  induction steps generalizing phase with
  | zero =>
      intro _
      simp only [figureOneFinalScheduledRetainedGaussianChain,
        MembershipOracleProgram.runEstimate, add_zero]
      simp
  | succ steps ih =>
      intro hbound
      have hphaseLt : phase < terminalPhaseSteps q := by omega
      let mu := (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I phase).map
          scheduledBalancedTraceRetainedOption
      let phaseProgram :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram q phase
      let tailProgram :=
        figureOneFinalScheduledRetainedGaussianChain q (phase + 1) steps
      let retainedKernel := figureOneFinalScheduledCompleteRetainedKernel q I
        (scheduleValue q phase)
        (gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1)))
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)
      have hphase :=
        figureOneFinalScheduledRetainedGaussianPhaseProgram_countedMeasurable
          q I oracle phase
      have htail := figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
        q I oracle (phase + 1) steps
      have hphaseEstimate : Measurable fun state =>
          (phaseProgram state).runEstimate oracle.query := by
        rw [show (fun state => (phaseProgram state).runEstimate oracle.query) =
            fun state => ((phaseProgram state).run oracle.query).map Prod.fst by
          funext state
          exact (phaseProgram state).runEstimate_eq_map_fst_run oracle.query
            (hphase.2 state).executionMeasurable]
        exact measurable_measure_map_param_variable hphase.1
          (fun state => MembershipOracleProgram.run_isProbabilityMeasure
            oracle.query (phaseProgram state)
              (hphase.2 state).executionMeasurable)
          (measurable_fst.comp measurable_snd)
      have htailEstimate : Measurable fun state =>
          (tailProgram state).runEstimate oracle.query := by
        rw [show (fun state => (tailProgram state).runEstimate oracle.query) =
            fun state => ((tailProgram state).run oracle.query).map Prod.fst by
          funext state
          exact (tailProgram state).runEstimate_eq_map_fst_run oracle.query
            (htail.2 state).executionMeasurable]
        exact measurable_measure_map_param_variable htail.1
          (fun state => MembershipOracleProgram.run_isProbabilityMeasure
            oracle.query (tailProgram state)
              (htail.2 state).executionMeasurable)
          (measurable_fst.comp measurable_snd)
      have hrun : ∀ state,
          ((phaseProgram state).bind tailProgram).runEstimate oracle.query =
            ((phaseProgram state).runEstimate oracle.query).bind fun next =>
              (tailProgram next).runEstimate oracle.query := by
        intro state
        exact MembershipOracleProgram.runEstimate_bind oracle.query
          (phaseProgram state) tailProgram (hphase.2 state).stronglyMeasurable
            (fun next => (htail.2 next).stronglyMeasurable) htailEstimate
      simp only [figureOneFinalScheduledRetainedGaussianChain]
      rw [show (fun state =>
          (((phaseProgram state).bind tailProgram).runEstimate oracle.query)) =
          fun state => ((phaseProgram state).runEstimate oracle.query).bind
            (fun next => (tailProgram next).runEstimate oracle.query) by
        funext state
        exact hrun state]
      have hphaseLaw : (fun state =>
          (phaseProgram state).runEstimate oracle.query) = retainedKernel := by
        funext state
        exact figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
          q I oracle phase state
      change mu.bind (fun state =>
          ((phaseProgram state).runEstimate oracle.query).bind
            (fun next => (tailProgram next).runEstimate oracle.query)) = _
      calc
        _ = (mu.bind fun state =>
              (phaseProgram state).runEstimate oracle.query).bind
                (fun next => (tailProgram next).runEstimate oracle.query) :=
          (Measure.bind_bind hphaseEstimate.aemeasurable
            htailEstimate.aemeasurable).symm
        _ = (mu.bind retainedKernel).bind
                (fun next => (tailProgram next).runEstimate oracle.query) := by
          rw [hphaseLaw]
        _ = ((scheduledBalancedForwardTraceLaw
              figureOneFinalScheduledBalancedParameters q I (phase + 1)).map
                scheduledBalancedTraceRetainedOption).bind
                  (fun next => (tailProgram next).runEstimate oracle.query) := by
          rw [show mu.bind retainedKernel =
              (scheduledBalancedForwardTraceLaw
                figureOneFinalScheduledBalancedParameters q I (phase + 1)).map
                  scheduledBalancedTraceRetainedOption from
            figureOneFinalScheduledTraceRetained_succ q I phase hphaseLt]
        _ = _ := by
          simpa only [tailProgram, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (phase + 1) (by omega)

/-- Terminal uniform collector retaining only its endpoint. -/
noncomputable def figureOneFinalScheduledRetainedTerminalProgram
    (q : VolumeParams) : Option (AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  | none => .pure none
  | some point =>
      (scheduledBalancedAccuracyRetryCollect q (terminalVariance q)
        (uniformRatioWeight (terminalVariance q))
        (figureOneFinalScheduledBalancedParameters.proposalCap q
          (terminalVariance q))
        (figureOneFinalScheduledBalancedParameters.properStride q
          (terminalVariance q))
        (figureOneFinalScheduledBalancedParameters.retryLimit q
          (terminalVariance q))
        (figureOneSampleCount q) (accuracyScaleFactor q • point)).bind
          fun result => .pure (optionSnd result)

theorem figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (Measurable fun state =>
      (figureOneFinalScheduledRetainedTerminalProgram q state).run oracle.query) ∧
    ∀ state,
      (figureOneFinalScheduledRetainedTerminalProgram q state).CountedStronglyMeasurable
        oracle.query := by
  let collect (point : AmbientSpace q.n) :=
    scheduledBalancedAccuracyRetryCollect q (terminalVariance q)
      (uniformRatioWeight (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q))
      (figureOneSampleCount q) (accuracyScaleFactor q • point)
  have hbase := scheduledBalancedAccuracyRetryCollect_countedMeasurable
    q I oracle (terminalVariance_pos' q)
      (measurable_uniformRatioWeight (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (terminalVariance q))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (terminalVariance q)) (figureOneSampleCount q)
  have hscale : Measurable fun point : AmbientSpace q.n =>
      accuracyScaleFactor q • point := by fun_prop
  have hcollectMeas : Measurable fun point => (collect point).run oracle.query :=
    hbase.1.comp hscale
  have hcollect : ∀ point, (collect point).CountedStronglyMeasurable oracle.query :=
    fun point => hbase.2 (accuracyScaleFactor q • point)
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

theorem figureOneFinalScheduledRetainedTerminalProgram_cost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (state : Option (AmbientSpace q.n)) :
    countedQueryCost
        ((figureOneFinalScheduledRetainedTerminalProgram q state).run
          oracle.query) =
      match state with
      | none => 0
      | some point => countedQueryCost
          ((scheduledBalancedAccuracyRetryCollect q (terminalVariance q)
            (uniformRatioWeight (terminalVariance q))
            (figureOneFinalScheduledBalancedParameters.proposalCap q
              (terminalVariance q))
            (figureOneFinalScheduledBalancedParameters.properStride q
              (terminalVariance q))
            (figureOneFinalScheduledBalancedParameters.retryLimit q
              (terminalVariance q))
            (figureOneSampleCount q) (accuracyScaleFactor q • point)).run
              oracle.query) := by
  cases state with
  | none =>
      exact MembershipOracleProgram.countedQueryCost_pure oracle.query none
  | some point =>
      unfold figureOneFinalScheduledRetainedTerminalProgram
      exact MembershipOracleProgram.countedQueryCost_bind_pure_eq
        oracle.query _ optionSnd measurable_optionSnd
          ((scheduledBalancedAccuracyRetryCollect_countedMeasurable
            q I oracle (terminalVariance_pos' q)
              (measurable_uniformRatioWeight (terminalVariance q))
              (figureOneFinalScheduledBalancedParameters.proposalCap q
                (terminalVariance q))
              (figureOneFinalScheduledBalancedParameters.properStride q
                (terminalVariance q))
              (figureOneFinalScheduledBalancedParameters.retryLimit q
                (terminalVariance q)) (figureOneSampleCount q)).2 _)

/-- Retained-state cost interpreter for all Gaussian phases followed by the
terminal uniform phase. -/
noncomputable def figureOneFinalScheduledRetainedFullCostProgram
    (q : VolumeParams) (state : Option (AmbientSpace q.n)) :
    MembershipOracleProgram q.n (Option (AmbientSpace q.n)) :=
  (figureOneFinalScheduledRetainedGaussianChain q 0
    (terminalPhaseSteps q) state).bind
      (figureOneFinalScheduledRetainedTerminalProgram q)

theorem figureOneFinalScheduledRetainedFullCostProgram_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (Measurable fun state =>
      (figureOneFinalScheduledRetainedFullCostProgram q state).run oracle.query) ∧
    ∀ state,
      (figureOneFinalScheduledRetainedFullCostProgram q state).CountedStronglyMeasurable
        oracle.query := by
  have hgaussian :=
    figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
      q I oracle 0 (terminalPhaseSteps q)
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable q I oracle
  unfold figureOneFinalScheduledRetainedFullCostProgram
  constructor
  · exact MembershipOracleProgram.measurable_run_bind_param oracle.query
      (figureOneFinalScheduledRetainedGaussianChain q 0 (terminalPhaseSteps q))
      (fun z => figureOneFinalScheduledRetainedTerminalProgram q z.2)
      hgaussian.1 hgaussian.2 (hterminal.1.comp measurable_snd)
        (fun z => hterminal.2 z.2)
  · intro state
    exact (hgaussian.2 state).bind hterminal.2 hterminal.1

/-- Exact whole-run expected cost of the retained interpreter: the recursive
sum of all Gaussian phase costs plus the terminal phase cost. -/
theorem lintegral_figureOneFinalScheduledRetainedFullCostProgram_eq
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    (∫⁻ state, countedQueryCost
        ((figureOneFinalScheduledRetainedFullCostProgram q state).run
          oracle.query)
      ∂((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I 0).map
          scheduledBalancedTraceRetainedOption)) =
      figureOneFinalScheduledGaussianPhaseCostTail q I oracle 0
          (terminalPhaseSteps q) +
        figureOneFinalScheduledTerminalExpectedCost q I oracle := by
  let mu0 := (scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I 0).map
      scheduledBalancedTraceRetainedOption
  let gaussian := figureOneFinalScheduledRetainedGaussianChain q 0
    (terminalPhaseSteps q)
  let terminal := figureOneFinalScheduledRetainedTerminalProgram q
  have hgaussian :=
    figureOneFinalScheduledRetainedGaussianChain_countedMeasurable
      q I oracle 0 (terminalPhaseSteps q)
  have hterminal :=
    figureOneFinalScheduledRetainedTerminalProgram_countedMeasurable q I oracle
  have hgaussianCost : Measurable fun state =>
      countedQueryCost ((gaussian state).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hgaussian.1
  have hterminalCost : Measurable fun state =>
      countedQueryCost ((terminal state).run oracle.query) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hterminal.1
  have hpoint : ∀ state,
      countedQueryCost (((gaussian state).bind terminal).run oracle.query) =
        countedQueryCost ((gaussian state).run oracle.query) +
          ∫⁻ next, countedQueryCost ((terminal next).run oracle.query)
            ∂((gaussian state).runEstimate oracle.query) := by
    intro state
    exact MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
      (gaussian state) terminal (hgaussian.2 state) hterminal.2 hterminal.1
  unfold figureOneFinalScheduledRetainedFullCostProgram
  change (∫⁻ state, countedQueryCost
      (((gaussian state).bind terminal).run oracle.query) ∂mu0) = _
  rw [lintegral_congr hpoint, lintegral_add_left hgaussianCost]
  have hgaussianEstimate : Measurable fun state =>
      (gaussian state).runEstimate oracle.query := by
    rw [show (fun state => (gaussian state).runEstimate oracle.query) =
        fun state => ((gaussian state).run oracle.query).map Prod.fst by
      funext state
      exact (gaussian state).runEstimate_eq_map_fst_run oracle.query
        (hgaussian.2 state).executionMeasurable]
    exact measurable_measure_map_param_variable hgaussian.1
      (fun state => MembershipOracleProgram.run_isProbabilityMeasure
        oracle.query (gaussian state) (hgaussian.2 state).executionMeasurable)
      (measurable_fst.comp measurable_snd)
  rw [← Measure.lintegral_bind hgaussianEstimate.aemeasurable
    hterminalCost.aemeasurable]
  rw [lintegral_figureOneFinalScheduledRetainedGaussianChain_eq_costTail
    q I oracle 0 (terminalPhaseSteps q) (by omega)]
  have hout :=
    bind_figureOneFinalScheduledRetainedGaussianChain_runEstimate_eq_trace
      q I oracle 0 (terminalPhaseSteps q) (by omega)
  have hout' : mu0.bind (fun state =>
      (gaussian state).runEstimate oracle.query) =
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
            (terminalPhaseSteps q)).map
              scheduledBalancedTraceRetainedOption := by
    simpa only [mu0, gaussian, zero_add] using hout
  rw [hout']
  congr 1
  unfold figureOneFinalScheduledTerminalExpectedCost
  apply lintegral_congr
  intro state
  exact figureOneFinalScheduledRetainedTerminalProgram_cost q I oracle state

#print axioms figureOneFinalScheduledRetainedGaussianPhaseProgram_cost
#print axioms figureOneFinalScheduledRetainedGaussianPhaseProgram_runEstimate
#print axioms lintegral_figureOneFinalScheduledRetainedGaussianChain_eq_costTail
#print axioms bind_figureOneFinalScheduledRetainedGaussianChain_runEstimate_eq_trace
#print axioms figureOneFinalScheduledRetainedTerminalProgram_cost
#print axioms lintegral_figureOneFinalScheduledRetainedFullCostProgram_eq

end ArlibCommunity.Algorithms.CV18
