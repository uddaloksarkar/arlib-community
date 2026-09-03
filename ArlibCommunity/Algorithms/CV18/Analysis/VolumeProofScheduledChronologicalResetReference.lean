/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.FiniteReferenceSequence
import ArlibCommunity.Algorithms.CV18.Analysis.Background.HistoryPreservingReset
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofResetReferenceBaseCapstone
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianResetJoint
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTerminalResetJoint
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledOuterPhaseIndependence

/-!
# A chronological reset reference for the scheduled trace

This file performs the outer, phase-by-phase exact-chance construction used
in CV18.  A first reset supplies the equation-(6) law of the empirical phase
average.  A second history-preserving reset changes only the retained endpoint
to the accepted stationary law from which the following scheduled phase is
run.  Thus old phase scores and the new score marginal are preserved exactly.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib
open scoped ENNReal

noncomputable section

/-- Forget the failure wrapper while retaining both the live scalar output
and optional endpoint.  On the reference laws below the endpoint is almost
surely present. -/
def scheduledResetPairOutput
    (result : Option (ℝ × AmbientSpace n)) : ℝ × Option (AmbientSpace n) :=
  (figureOneScheduledTraceLiveRawOutput result, optionSnd result)

theorem measurable_scheduledResetPairOutput :
    Measurable (scheduledResetPairOutput (n := n)) :=
  measurable_figureOneScheduledTraceLiveRawOutput.prodMk measurable_optionSnd

/-- Reassemble a phase result after resetting its optional endpoint. -/
def scheduledResetPairToResult
    (result : ℝ × Option (AmbientSpace n)) :
    Option (ℝ × AmbientSpace n) :=
  result.2.map fun point => (result.1, point)

theorem measurable_scheduledResetPairToResult :
    Measurable (scheduledResetPairToResult (n := n)) := by
  unfold scheduledResetPairToResult
  convert Measurable.optionCases
    (0 : AmbientSpace n)
    (noneValue := fun _ : ℝ => (none : Option (ℝ × AmbientSpace n)))
    (someValue := fun result : ℝ × AmbientSpace n =>
      some (result.1, result.2))
    measurable_const
    (measurable_some.comp (measurable_fst.prodMk measurable_snd)) using 1
  funext result
  cases result.2 <;> rfl

@[simp] theorem optionSnd_scheduledResetPairToResult
    (result : ℝ × Option (AmbientSpace n)) :
    optionSnd (scheduledResetPairToResult result) = result.2 := by
  unfold scheduledResetPairToResult
  cases result.2 <;> rfl

@[simp] theorem liveRaw_scheduledResetPairToResult
    (result : ℝ × Option (AmbientSpace n)) :
    figureOneScheduledTraceLiveRawOutput
        (scheduledResetPairToResult result) =
      if result.2 = none then 0 else max 0 result.1 := by
  unfold scheduledResetPairToResult
  cases result.2 <;> rfl

theorem ae_fst_nonnegative_of_map_eq_liveRaw
    (joint : Measure (Option (ℝ × AmbientSpace n)))
    (target : Measure (ℝ × Option (AmbientSpace n)))
    (hscore : target.map Prod.fst =
      joint.map figureOneScheduledTraceLiveRawOutput) :
    ∀ᵐ result ∂target, 0 ≤ result.1 := by
  have hlive : ∀ᵐ result ∂joint,
      0 ≤ figureOneScheduledTraceLiveRawOutput result :=
    ae_of_all _ fun result => by
      cases result <;> simp [figureOneScheduledTraceLiveRawOutput]
  have hmapped : ∀ᵐ value
      ∂(joint.map figureOneScheduledTraceLiveRawOutput), 0 ≤ value :=
    (ae_map_iff
      measurable_figureOneScheduledTraceLiveRawOutput.aemeasurable
      measurableSet_Ici).2 hlive
  rw [← hscore] at hmapped
  exact (ae_map_iff measurable_fst.aemeasurable measurableSet_Ici).1 hmapped

/-- Append the score/optional-endpoint pair used by the outer reset to the
public loss-preserving trace. -/
noncomputable def scheduledResetTraceAppend
    (state : ScheduledBalancedCoolingTrace n ×
      (ℝ × Option (AmbientSpace n))) : ScheduledBalancedCoolingTrace n :=
  scheduledBalancedCoolingTraceAppend state.1
    (scheduledResetPairToResult state.2)

theorem measurable_scheduledResetTraceAppend :
    Measurable (scheduledResetTraceAppend (n := n)) := by
  unfold scheduledResetTraceAppend
  exact measurable_scheduledBalancedCoolingTraceAppend.comp <|
    measurable_fst.prodMk
      (measurable_scheduledResetPairToResult.comp measurable_snd)

theorem scheduledResetPairToResult_pairOutput_eq
    (result : Option (ℝ × AmbientSpace n))
    (hresult : ScheduledCollectedTotalNonnegative result) :
    scheduledResetPairToResult (scheduledResetPairOutput result) = result := by
  cases result with
  | none => rfl
  | some result =>
      rcases result with ⟨score, point⟩
      simp only [ScheduledCollectedTotalNonnegative] at hresult
      simp [scheduledResetPairToResult, scheduledResetPairOutput,
        figureOneScheduledTraceLiveRawOutput, optionSnd, max_eq_right hresult]

/-- Pairing an executable phase result with its nonnegative score and then
reassembling it does not change the executable trace-step law. -/
theorem map_sequentialPairLaw_scheduledResetTraceAppend_eq_bind
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (source : Measure (ScheduledBalancedCoolingTrace q.n)) :
    (sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)).map
      (fun state => scheduledResetTraceAppend
        (state.1, scheduledResetPairOutput state.2)) =
      source.bind (scheduledBalancedTracePhaseKernel
        figureOneFinalScheduledBalancedParameters q I phase) := by
  let K := scheduledBalancedTracePhaseObservationLaw
    figureOneFinalScheduledBalancedParameters q I phase
  have hK := scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I phase
  have hlift : Measurable fun trace : ScheduledBalancedCoolingTrace q.n =>
      (K trace).map fun result => (trace, result) :=
    measurable_sequentialPairKernel (rho := source) hK.1 hK.2
  have hout : Measurable fun state : ScheduledBalancedCoolingTrace q.n ×
      Option (ℝ × AmbientSpace q.n) =>
      scheduledResetTraceAppend
        (state.1, scheduledResetPairOutput state.2) :=
    measurable_scheduledResetTraceAppend.comp <|
      measurable_fst.prodMk
        (measurable_scheduledResetPairOutput.comp measurable_snd)
  unfold sequentialPairLaw
  rw [map_bind_eq_bind_map_of_measurable source hlift hout]
  apply Measure.bind_congr_right
  filter_upwards with trace
  unfold scheduledBalancedTracePhaseKernel
  have hpair : Measurable fun result : Option (ℝ × AmbientSpace q.n) =>
      (trace, result) := measurable_const.prodMk measurable_id
  rw [Measure.map_map hout hpair]
  apply Measure.map_congr
  filter_upwards [scheduledBalancedTracePhaseObservationLaw_ae_total_nonnegative
    figureOneFinalScheduledBalancedParameters q I phase trace]
      with result hresult
  unfold scheduledResetTraceAppend
  simp only [Function.comp_apply, Prod.fst, Prod.snd]
  rw [scheduledResetPairToResult_pairOutput_eq result hresult]

/-- A retained-option marginal supported on `some` forces the trace to be
live almost surely.  This is the support fact needed when a reset phase is
recorded back into the public loss-preserving trace. -/
theorem ae_trace_live_of_map_retainedOption_eq_map_some
    (source : Measure (ScheduledBalancedCoolingTrace n))
    (retained : Measure (AmbientSpace n))
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      retained.map some) :
    ∀ᵐ trace ∂source, trace.2 = true := by
  have hsome : ∀ᵐ value ∂retained.map some, value ≠ none :=
    (ae_map_iff measurable_some.aemeasurable
      measurableSet_option_none.compl).2 <|
      ae_of_all _ fun point => by simp
  rw [← hretained] at hsome
  have hoption : ∀ᵐ trace ∂source,
      scheduledBalancedTraceRetainedOption trace ≠ none :=
    (ae_map_iff measurable_scheduledBalancedTraceRetainedOption.aemeasurable
      measurableSet_option_none.compl).1 hsome
  filter_upwards [hoption] with trace htrace
  unfold scheduledBalancedTraceRetainedOption at htrace
  cases hlive : trace.2 with
  | false => simp [hlive] at htrace
  | true => rfl

/-- On a live valid prefix, a nonnegative reset score with a present endpoint
is exactly the newly appended public trace coordinate. -/
theorem scheduledBalancedTracePhaseVariable_resetAppend_eq_fst
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (trace : ScheduledBalancedCoolingTrace q.n)
    (hvalid : ScheduledBalancedCoolingTraceValid phase trace)
    (hlive : trace.2 = true)
    (result : ℝ × Option (AmbientSpace q.n))
    (hscore : 0 ≤ result.1) (hpoint : result.2 ≠ none) :
    scheduledBalancedTracePhaseVariable q (phase + 1)
        (scheduledResetTraceAppend (trace, result)) = result.1 := by
  unfold scheduledResetTraceAppend
  rw [scheduledBalancedTracePhaseVariable_append_eq_rawOutput q phase hphase
    trace hvalid]
  simp only [hlive, if_true]
  rw [liveRaw_scheduledResetPairToResult]
  simp [hpoint, max_eq_right hscore]

/-- The endpoint of a live reset append is precisely the reset endpoint. -/
theorem scheduledBalancedTraceRetainedOption_resetAppend
    (trace : ScheduledBalancedCoolingTrace n)
    (hlive : trace.2 = true)
    (result : ℝ × Option (AmbientSpace n)) :
    scheduledBalancedTraceRetainedOption
        (scheduledResetTraceAppend (trace, result)) = result.2 := by
  unfold scheduledResetTraceAppend
  rw [scheduledBalancedTraceRetainedOption_append]
  simp [hlive]

/-- The exact Gaussian and normalized accepted endpoint laws differ by the
single stationary-target error already allocated in the scheduled boundary
budget. -/
theorem scheduledRetainedExactSome_tvLe_acceptedSome
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    TVLe (scheduledRetainedExactSome q I phase)
      ((figureOneScheduledAcceptedTargetAt q I phase).map some)
      (scheduledBalancedStationaryTargetError q) := by
  have htv := scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
    q I (scheduleValue_pos q phase)
  have hmapped := htv.symm.map measurable_some
  simpa [scheduledRetainedExactSome, figureOneScheduledAcceptedTargetAt,
    figureOneScheduledSpeedyPiAt] using hmapped

/-- Reset only the endpoint of a joint score/endpoint law.  The score
marginal is preserved, while the new endpoint is exactly the accepted target
used by the next scheduled phase. -/
theorem exists_acceptedEndpointResetJoint
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (joint : Measure (Option (ℝ × AmbientSpace q.n)))
    [IsProbabilityMeasure joint]
    (hstate : joint.map optionSnd = scheduledRetainedExactSome q I phase) :
    ∃ target : Measure (ℝ × Option (AmbientSpace q.n)),
      IsProbabilityMeasure target ∧
      MeasureLeUpTo (joint.map scheduledResetPairOutput) target
        (scheduledBalancedStationaryTargetError q) ∧
      target.map Prod.fst =
        joint.map figureOneScheduledTraceLiveRawOutput ∧
      target.map Prod.snd =
        (figureOneScheduledAcceptedTargetAt q I phase).map some := by
  let paired := joint.map (scheduledResetPairOutput (n := q.n))
  let accepted := (figureOneScheduledAcceptedTargetAt q I phase).map some
  let _ : IsProbabilityMeasure paired :=
    Measure.isProbabilityMeasure_map
      (measurable_scheduledResetPairOutput (n := q.n)).aemeasurable
  let _ : IsProbabilityMeasure accepted :=
    let _ := figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I phase
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hpairedState : paired.map Prod.snd =
      scheduledRetainedExactSome q I phase := by
    calc
      paired.map Prod.snd = joint.map optionSnd := by
        rw [Measure.map_map measurable_snd
          (measurable_scheduledResetPairOutput (n := q.n))]
        rfl
      _ = _ := hstate
  have htv : TVLe (paired.map Prod.snd) accepted
      (scheduledBalancedStationaryTargetError q) := by
    rw [hpairedState]
    exact scheduledRetainedExactSome_tvLe_acceptedSome q I phase
  obtain ⟨target, htargetProb, hscore, htargetState, htargetTV⟩ :=
    exists_historyPreservingReset_of_tvLe paired accepted htv
  refine ⟨target, htargetProb, MeasureLeUpTo.of_tvLe htargetTV, ?_,
    htargetState⟩
  calc
    target.map Prod.fst = paired.map Prod.fst := hscore
    _ = joint.map figureOneScheduledTraceLiveRawOutput := by
      rw [Measure.map_map measurable_fst
        (measurable_scheduledResetPairOutput (n := q.n))]
      rfl

/-- Compose a phase's equation-(6) reset with the endpoint reset.  The
result is expressed on the pair carrier consumed by the chronological trace
append operation. -/
theorem exists_acceptedEndpointResetJoint_of_joint
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (source joint : Measure (Option (ℝ × AmbientSpace q.n)))
    [IsProbabilityMeasure source] [IsProbabilityMeasure joint]
    {resetError : ENNReal}
    (hjoint : MeasureLeUpTo source joint resetError)
    (hstate : joint.map optionSnd = scheduledRetainedExactSome q I phase)
    (hmem : MemLp figureOneScheduledTraceLiveRawOutput 2 joint)
    {mean secondBound : ℝ}
    (hmean : (∫ result, figureOneScheduledTraceLiveRawOutput result
        ∂joint) = mean)
    (hsecond : (∫ result,
        figureOneScheduledTraceLiveRawOutput result ^ 2 ∂joint) ≤
      secondBound) :
    ∃ target : Measure (ℝ × Option (AmbientSpace q.n)),
      IsProbabilityMeasure target ∧
      MeasureLeUpTo (source.map scheduledResetPairOutput) target
        (resetError + scheduledBalancedStationaryTargetError q) ∧
      target.map Prod.snd =
        (figureOneScheduledAcceptedTargetAt q I phase).map some ∧
      (∀ᵐ result ∂target, 0 ≤ result.1) ∧
      MemLp Prod.fst 2 target ∧
      (∫ result, result.1 ∂target) = mean ∧
      (∫ result, result.1 ^ 2 ∂target) ≤ secondBound := by
  obtain ⟨target, htargetProb, hendpoint, hscore, htargetState⟩ :=
    exists_acceptedEndpointResetJoint q I phase joint hstate
  let _ : IsProbabilityMeasure target := htargetProb
  have hsourcePair := hjoint.map
    (measurable_scheduledResetPairOutput (n := q.n))
  have hcomparison := hsourcePair.trans hendpoint
  have hmemId : MemLp id 2
      (joint.map figureOneScheduledTraceLiveRawOutput) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      measurable_figureOneScheduledTraceLiveRawOutput.aemeasurable).2
    convert hmem using 1 <;> rfl
  rw [← hscore] at hmemId
  have hmemFst : MemLp Prod.fst 2 target := by
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).1
        (by convert hmemId using 1 <;> rfl)
  have hnonneg : ∀ᵐ result ∂target, 0 ≤ result.1 :=
    ae_fst_nonnegative_of_map_eq_liveRaw joint target hscore
  have hmeanTarget : (∫ result, result.1 ∂target) = mean := by
    calc
      (∫ result, result.1 ∂target) =
          ∫ value, value ∂(target.map Prod.fst) := by
        exact (integral_map measurable_fst.aemeasurable
          measurable_id.aestronglyMeasurable).symm
      _ = ∫ value, value
          ∂(joint.map figureOneScheduledTraceLiveRawOutput) := by rw [hscore]
      _ = ∫ result, figureOneScheduledTraceLiveRawOutput result
          ∂joint := by
        exact integral_map
          measurable_figureOneScheduledTraceLiveRawOutput.aemeasurable
          measurable_id.aestronglyMeasurable
      _ = mean := hmean
  have hsecondTarget : (∫ result, result.1 ^ 2 ∂target) ≤
      secondBound := by
    calc
      (∫ result, result.1 ^ 2 ∂target) =
          ∫ value, value ^ 2 ∂(target.map Prod.fst) := by
        exact (integral_map measurable_fst.aemeasurable
          (measurable_id.pow_const 2).aestronglyMeasurable).symm
      _ = ∫ value, value ^ 2
          ∂(joint.map figureOneScheduledTraceLiveRawOutput) := by rw [hscore]
      _ = ∫ result, figureOneScheduledTraceLiveRawOutput result ^ 2
          ∂joint := by
        exact integral_map
          measurable_figureOneScheduledTraceLiveRawOutput.aemeasurable
          (measurable_id.pow_const 2).aestronglyMeasurable
      _ ≤ secondBound := hsecond
  exact ⟨target, htargetProb, hcomparison, htargetState, hnonneg, hmemFst,
    hmeanTarget, hsecondTarget⟩

/-- Fully instantiated Gaussian phase target on the accepted-endpoint pair
carrier.  It has the exact chronological mean and the reset-reference
equation-(6) second moment. -/
theorem exists_scheduledGaussianAcceptedPairTarget
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    ∃ target : Measure (ℝ × Option (AmbientSpace q.n)),
      IsProbabilityMeasure target ∧
      MeasureLeUpTo
        ((figureOneScheduledGaussianPhaseTarget q I phase).map
          scheduledResetPairOutput)
        target
        (scheduledResetReferenceError q
            (figureOnePhaseSampleCount q (scheduleValue q phase) - 1) +
          scheduledBalancedStationaryTargetError q) ∧
      target.map Prod.snd =
        (figureOneScheduledAcceptedTargetAt q I phase).map some ∧
      (∀ᵐ result ∂target, 0 ≤ result.1) ∧
      MemLp Prod.fst 2 target ∧
      (∫ result, result.1 ∂target) =
        figureOneChronologicalRawMean q I (phase + 1) ∧
      (∫ result, result.1 ^ 2 ∂target) ≤
        (figureOneChronologicalMomentFactor q (phase + 1) +
            figureOneExecutableMomentSlack q / 8) *
          figureOneChronologicalRawMean q I (phase + 1) ^ 2 := by
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let mean :=
    ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1)) x
      ∂(truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
  let factor := if scheduleValue q phase ≤ 1 then
    1 + 2 / (q.n : ℝ)
  else
    1 + scheduleValue q phase / terminalVariance q
  have hcount : 0 < count := by
    simpa [count] using
      figureOnePhaseSampleCount_pos q (scheduleValue q phase)
  have hcountMax : count ≤ figureOneDependentMaxSampleCount q := by
    simpa [count] using
      figureOnePhaseSampleCount_le_dependentMax q (scheduleValue q phase)
  have hmeanPos : 0 < mean := by
    rw [show mean =
        gaussianIntegral (truncatedBody q I) (scheduleValue q (phase + 1)) /
          gaussianIntegral (truncatedBody q I) (scheduleValue q phase) by
      simpa [mean] using
        gaussianRatioWeight_mean_eq q I (scheduleValue_pos q phase)]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q (phase + 1)))
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q phase))
  have hcoordinateSecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        factor * mean ^ 2 := by
    apply (div_le_iff₀ (pow_pos hmeanPos 2)).mp
    simpa [factor, mean] using
      scheduleValue_gaussian_relativeSecondMoment_le_branchFactor
        q I phase hphase
  have hcoordinateThird :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        ((129 / 64 : ℝ) * mean) ^ 3 := by
    simpa [mean] using
      scheduleValue_gaussian_thirdMoment_le_rational_mean_cube q I phase
  obtain ⟨joint, hjointProb, hjoint, hstate, hmem, hmean, hsecond⟩ :=
    exists_figureOneScheduledGaussianResetJointTarget q I phase count
      (by rfl) hcount hcountMax
      (mul_pos (by norm_num) hmeanPos) hmeanPos.le le_rfl
      hcoordinateSecond hcoordinateThird
  let _ : IsProbabilityMeasure joint := hjointProb
  have hbudget :=
    scheduledGaussianResetReference_equationSix_budget_chronological
      q I phase hphase
  have hsecond' :
      (∫ result, figureOneScheduledTraceLiveRawOutput result ^ 2
          ∂joint) ≤
        (figureOneChronologicalMomentFactor q (phase + 1) +
            figureOneExecutableMomentSlack q / 8) * mean ^ 2 := by
    exact hsecond.trans (by simpa [count, mean, factor] using hbudget)
  let _ : IsProbabilityMeasure
      (figureOneScheduledGaussianPhaseTarget q I phase) :=
    figureOneScheduledGaussianPhaseTarget_isProbabilityMeasure q I phase
  obtain ⟨target, htargetProb, hcomparison, htargetState, htargetNonneg, htargetMem,
      htargetMean, htargetSecond⟩ :=
    exists_acceptedEndpointResetJoint_of_joint q I phase
      (figureOneScheduledGaussianPhaseTarget q I phase) joint hjoint
        hstate hmem hmean hsecond'
  have hmeanChronological : mean =
      figureOneChronologicalRawMean q I (phase + 1) := by
    have hphaseDependent : phase < figureOneDependentPhaseCount q := by
      rw [figureOneDependentPhaseCount]
      omega
    have horder :
        figureOneChronologicalPhaseOrder q ⟨phase, hphaseDependent⟩ =
          if hs : scheduleValue q phase ≤ 1 then
            FigureOneIdealPhase.fixed ⟨⟨phase, hphase⟩, hs⟩
          else
            FigureOneIdealPhase.accelerated ⟨⟨phase, hphase⟩, hs⟩ := by
      simpa using figureOneChronologicalPhaseOrder_apply_transition q
        (⟨phase, hphase⟩ : Fin (terminalPhaseSteps q))
    rw [figureOneChronologicalRawMean,
      figureOneChronologicalPhaseAt_succ q phase hphaseDependent, horder]
    by_cases hs : scheduleValue q phase ≤ 1
    · simp [hs, figureOneIdealPhaseMean, mean,
        gaussianRatioWeight_mean_eq q I (scheduleValue_pos q phase)]
    · simp [hs, figureOneIdealPhaseMean, mean,
        gaussianRatioWeight_mean_eq q I (scheduleValue_pos q phase)]
  refine ⟨target, htargetProb, ?_, htargetState, htargetNonneg,
    htargetMem, ?_, ?_⟩
  · simpa [count] using hcomparison
  · exact htargetMean.trans hmeanChronological
  · rw [← hmeanChronological]
    exact htargetSecond

/-- The exact-endpoint form used for the *first* outer reset.  Keeping this
separate from `exists_scheduledGaussianAcceptedPairTarget` is essential: the
public-to-equation-(6) reset is the only reset charged to the new-coordinate
independence coefficient. -/
theorem exists_scheduledGaussianExactPairTarget
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    ∃ target : Measure (ℝ × Option (AmbientSpace q.n)),
      IsProbabilityMeasure target ∧
      MeasureLeUpTo
        ((figureOneScheduledGaussianPhaseTarget q I phase).map
          scheduledResetPairOutput)
        target
        (scheduledResetReferenceError q
          (figureOnePhaseSampleCount q (scheduleValue q phase) - 1)) ∧
      target.map Prod.snd = scheduledRetainedExactSome q I phase ∧
      (∀ᵐ result ∂target, 0 ≤ result.1) ∧
      MemLp Prod.fst 2 target ∧
      (∫ result, result.1 ∂target) =
        figureOneChronologicalRawMean q I (phase + 1) ∧
      (∫ result, result.1 ^ 2 ∂target) ≤
        (figureOneChronologicalMomentFactor q (phase + 1) +
            figureOneExecutableMomentSlack q / 8) *
          figureOneChronologicalRawMean q I (phase + 1) ^ 2 := by
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let mean :=
    ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1)) x
      ∂(truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
  let factor := if scheduleValue q phase ≤ 1 then
    1 + 2 / (q.n : ℝ)
  else
    1 + scheduleValue q phase / terminalVariance q
  have hcount : 0 < count := by
    simpa [count] using
      figureOnePhaseSampleCount_pos q (scheduleValue q phase)
  have hcountMax : count ≤ figureOneDependentMaxSampleCount q := by
    simpa [count] using
      figureOnePhaseSampleCount_le_dependentMax q (scheduleValue q phase)
  have hmeanPos : 0 < mean := by
    rw [show mean =
        gaussianIntegral (truncatedBody q I) (scheduleValue q (phase + 1)) /
          gaussianIntegral (truncatedBody q I) (scheduleValue q phase) by
      simpa [mean] using
        gaussianRatioWeight_mean_eq q I (scheduleValue_pos q phase)]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q (phase + 1)))
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q phase))
  have hcoordinateSecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        factor * mean ^ 2 := by
    apply (div_le_iff₀ (pow_pos hmeanPos 2)).mp
    simpa [factor, mean] using
      scheduleValue_gaussian_relativeSecondMoment_le_branchFactor
        q I phase hphase
  have hcoordinateThird :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        ((129 / 64 : ℝ) * mean) ^ 3 := by
    simpa [mean] using
      scheduleValue_gaussian_thirdMoment_le_rational_mean_cube q I phase
  obtain ⟨joint, hjointProb, hjoint, hstate, hmem, hmean, hsecond⟩ :=
    exists_figureOneScheduledGaussianResetJointTarget q I phase count
      (by rfl) hcount hcountMax
      (mul_pos (by norm_num) hmeanPos) hmeanPos.le le_rfl
      hcoordinateSecond hcoordinateThird
  let _ : IsProbabilityMeasure joint := hjointProb
  have hbudget :=
    scheduledGaussianResetReference_equationSix_budget_chronological
      q I phase hphase
  have hsecond' :
      (∫ result, figureOneScheduledTraceLiveRawOutput result ^ 2
          ∂joint) ≤
        (figureOneChronologicalMomentFactor q (phase + 1) +
            figureOneExecutableMomentSlack q / 8) * mean ^ 2 :=
    hsecond.trans (by simpa [count, mean, factor] using hbudget)
  let target := joint.map (scheduledResetPairOutput (n := q.n))
  have houtput := measurable_scheduledResetPairOutput (n := q.n)
  have htargetProb : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map houtput.aemeasurable
  have hstateTarget : target.map Prod.snd =
      scheduledRetainedExactSome q I phase := by
    calc
      target.map Prod.snd = joint.map optionSnd := by
        rw [Measure.map_map measurable_snd houtput]
        rfl
      _ = _ := hstate
  have hmemTarget : MemLp Prod.fst 2 target := by
    apply (memLp_map_measure_iff measurable_fst.aestronglyMeasurable
      houtput.aemeasurable).2
    convert hmem using 1 <;> rfl
  have hnonnegTarget : ∀ᵐ result ∂target, 0 ≤ result.1 := by
    apply ae_fst_nonnegative_of_map_eq_liveRaw joint target
    rw [Measure.map_map measurable_fst houtput]
    rfl
  have hmeanTarget : (∫ result, result.1 ∂target) = mean := by
    rw [show target = joint.map scheduledResetPairOutput by rfl,
      integral_map houtput.aemeasurable measurable_fst.aestronglyMeasurable]
    exact hmean
  have hsecondTarget : (∫ result, result.1 ^ 2 ∂target) ≤
      (figureOneChronologicalMomentFactor q (phase + 1) +
          figureOneExecutableMomentSlack q / 8) * mean ^ 2 := by
    rw [show target = joint.map scheduledResetPairOutput by rfl,
      integral_map houtput.aemeasurable
        (measurable_fst.pow_const 2).aestronglyMeasurable]
    exact hsecond'
  have hphaseDependent : phase < figureOneDependentPhaseCount q := by
    rw [figureOneDependentPhaseCount]
    omega
  have horder :
      figureOneChronologicalPhaseOrder q ⟨phase, hphaseDependent⟩ =
        if hs : scheduleValue q phase ≤ 1 then
          FigureOneIdealPhase.fixed ⟨⟨phase, hphase⟩, hs⟩
        else
          FigureOneIdealPhase.accelerated ⟨⟨phase, hphase⟩, hs⟩ := by
    simpa using figureOneChronologicalPhaseOrder_apply_transition q
      (⟨phase, hphase⟩ : Fin (terminalPhaseSteps q))
  have hmeanChronological : mean =
      figureOneChronologicalRawMean q I (phase + 1) := by
    rw [figureOneChronologicalRawMean,
      figureOneChronologicalPhaseAt_succ q phase hphaseDependent, horder]
    by_cases hs : scheduleValue q phase ≤ 1
    · simp [hs, figureOneIdealPhaseMean, mean,
        gaussianRatioWeight_mean_eq q I (scheduleValue_pos q phase)]
    · simp [hs, figureOneIdealPhaseMean, mean,
        gaussianRatioWeight_mean_eq q I (scheduleValue_pos q phase)]
  refine ⟨target, htargetProb, ?_, hstateTarget, hnonnegTarget,
    hmemTarget, ?_, ?_⟩
  · simpa [target, count] using hjoint.map houtput
  · exact hmeanTarget.trans hmeanChronological
  · rw [← hmeanChronological]
    exact hsecondTarget

/-- The terminal uniform-ratio analogue.  No accepted-endpoint reset is
needed after the last coordinate, so only the collector reset is charged. -/
theorem exists_scheduledTerminalPairTarget
    (q : VolumeParams) (I : VolumeInput q.n) :
    ∃ target : Measure (ℝ × Option (AmbientSpace q.n)),
      IsProbabilityMeasure target ∧
      MeasureLeUpTo
        ((figureOneScheduledTerminalPhaseTarget q I).map
          scheduledResetPairOutput)
        target
        (scheduledResetReferenceError q (figureOneSampleCount q - 1)) ∧
      target.map Prod.snd =
        scheduledRetainedExactSome q I (terminalPhaseSteps q) ∧
      (∀ᵐ result ∂target, 0 ≤ result.1) ∧
      MemLp Prod.fst 2 target ∧
      (∫ result, result.1 ∂target) =
        figureOneChronologicalRawMean q I (terminalPhaseSteps q + 1) ∧
      (∫ result, result.1 ^ 2 ∂target) ≤
        (figureOneChronologicalMomentFactor q (terminalPhaseSteps q + 1) +
            figureOneExecutableMomentSlack q / 8) *
          figureOneChronologicalRawMean q I
            (terminalPhaseSteps q + 1) ^ 2 := by
  obtain ⟨joint, hjointProb, hjoint, hstate, hmem, hmean, hsecond⟩ :=
    exists_terminalScheduledResetJointTarget q I
  let _ : IsProbabilityMeasure joint := hjointProb
  let target := joint.map (scheduledResetPairOutput (n := q.n))
  have houtput := measurable_scheduledResetPairOutput (n := q.n)
  have htargetProb : IsProbabilityMeasure target :=
    Measure.isProbabilityMeasure_map houtput.aemeasurable
  have hstateTarget : target.map Prod.snd =
      scheduledRetainedExactSome q I (terminalPhaseSteps q) := by
    calc
      target.map Prod.snd = joint.map optionSnd := by
        rw [Measure.map_map measurable_snd houtput]
        rfl
      _ = _ := hstate
  have hmemTarget : MemLp Prod.fst 2 target := by
    apply (memLp_map_measure_iff measurable_fst.aestronglyMeasurable
      houtput.aemeasurable).2
    convert hmem using 1 <;> rfl
  have hnonnegTarget : ∀ᵐ result ∂target, 0 ≤ result.1 := by
    apply ae_fst_nonnegative_of_map_eq_liveRaw joint target
    rw [Measure.map_map measurable_fst houtput]
    rfl
  have hmeanTarget : (∫ result, result.1 ∂target) =
      figureOneIdealPhaseMean q I .terminal := by
    rw [show target = joint.map scheduledResetPairOutput by rfl,
      integral_map houtput.aemeasurable measurable_fst.aestronglyMeasurable]
    exact hmean
  have hsecondTarget : (∫ result, result.1 ^ 2 ∂target) ≤
      (1 + (Real.exp (1 / 2) - 1) / (figureOneSampleCount q : ℝ) +
          figureOneExecutableMomentSlack q / 8) *
        (figureOneIdealPhaseMean q I .terminal) ^ 2 := by
    rw [show target = joint.map scheduledResetPairOutput by rfl,
      integral_map houtput.aemeasurable
        (measurable_fst.pow_const 2).aestronglyMeasurable]
    exact hsecond
  have hphaseDependent : terminalPhaseSteps q <
      figureOneDependentPhaseCount q := by
    rw [figureOneDependentPhaseCount]
    omega
  have hterminal : figureOneChronologicalPhaseAt q
      (terminalPhaseSteps q + 1) = .terminal := by
    rw [figureOneChronologicalPhaseAt_succ q (terminalPhaseSteps q)
      hphaseDependent]
    exact figureOneChronologicalPhaseOrder_apply_terminal q
  have hmeanChronological : figureOneChronologicalRawMean q I
      (terminalPhaseSteps q + 1) =
        figureOneIdealPhaseMean q I .terminal := by
    rw [figureOneChronologicalRawMean, hterminal]
  have hfactorChronological : figureOneChronologicalMomentFactor q
      (terminalPhaseSteps q + 1) =
        1 + (Real.exp (1 / 2) - 1) / (figureOneSampleCount q : ℝ) := by
    rw [figureOneChronologicalMomentFactor, hterminal]
    rfl
  refine ⟨target, htargetProb, ?_, hstateTarget, hnonnegTarget,
    hmemTarget, ?_, ?_⟩
  · simpa [target] using hjoint.map houtput
  · simpa [hmeanChronological] using hmeanTarget
  · simpa [hmeanChronological, hfactorChronological, add_assoc] using
      hsecondTarget

#print axioms scheduledRetainedExactSome_tvLe_acceptedSome
#print axioms scheduledResetPairToResult_pairOutput_eq
#print axioms map_sequentialPairLaw_scheduledResetTraceAppend_eq_bind
#print axioms ae_trace_live_of_map_retainedOption_eq_map_some
#print axioms scheduledBalancedTracePhaseVariable_resetAppend_eq_fst
#print axioms scheduledBalancedTraceRetainedOption_resetAppend
#print axioms exists_acceptedEndpointResetJoint
#print axioms exists_acceptedEndpointResetJoint_of_joint
#print axioms exists_scheduledGaussianAcceptedPairTarget
#print axioms exists_scheduledGaussianExactPairTarget
#print axioms exists_scheduledTerminalPairTarget

end

end ArlibCommunity.Algorithms.CV18
