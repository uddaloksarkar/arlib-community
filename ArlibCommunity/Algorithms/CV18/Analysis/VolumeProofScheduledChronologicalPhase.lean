/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofChronologicalBalancedPrefixes
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryKernel

/-!
# Chronological complete-phase law at the schedule-targeted geometry

This isolates the probabilistic part of CV18 Lemma 7.17(c).  Once the first
retained transition is replaced, every remaining retained transition is
common postprocessing, so the one-step `MeasureLeUpTo` error is paid once for
the whole phase.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

theorem figureOneIdealPhaseSampleCount_pos
    (q : VolumeParams) (phase : FigureOneIdealPhase q) :
    0 < figureOneIdealPhaseSampleCount q phase := by
  cases phase with
  | fixed k =>
      exact figureOneFixedSampleCount_pos q
  | accelerated k =>
      exact figureOneSampleCount_pos q
  | terminal =>
      exact figureOneSampleCount_pos q

/-- A canonical retained target point from a nonempty ideal phase block. -/
noncomputable def figureOneIdealPhaseRetainedPoint
    (q : VolumeParams) (phase : FigureOneIdealPhase q) :
    FigureOneIdealPhaseSampleSpace q phase → AmbientSpace q.n :=
  fun samples => samples ⟨0, figureOneIdealPhaseSampleCount_pos q phase⟩

theorem measurable_figureOneIdealPhaseRetainedPoint
    (q : VolumeParams) (phase : FigureOneIdealPhase q) :
    Measurable (figureOneIdealPhaseRetainedPoint q phase) :=
  measurable_pi_apply _

theorem figureOneChronologicalPhaseAt_succ
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q) :
    figureOneChronologicalPhaseAt q (phase + 1) =
      figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩ := by
  simp [figureOneChronologicalPhaseAt, Nat.mod_eq_of_lt hphase]

/-- Deterministically append the ideal average for chronological `phase`,
while retaining one stationary point from that same ideal block. -/
noncomputable def figureOneIdealChronologicalAppend
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q) :
    FigureOneIdealExperimentSpace q × Option (BalancedCoolingHistory q.n) →
      FigureOneIdealExperimentSpace q × Option (BalancedCoolingHistory q.n) :=
  let p := figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩
  fun state =>
    (state.1, match state.2 with
      | none => none
      | some history =>
          balancedCoolingHistorySnocTerminal history <| some
            (figureOneIdealPhaseEstimator q p (state.1 p),
              figureOneIdealPhaseRetainedPoint q p (state.1 p)))

theorem measurable_figureOneIdealChronologicalAppend
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q) :
    Measurable (figureOneIdealChronologicalAppend q phase hphase) := by
  let p := figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩
  have hsample : Measurable fun state :
      FigureOneIdealExperimentSpace q × BalancedCoolingHistory q.n =>
      state.1 p := (measurable_pi_apply p).comp measurable_fst
  have hresult : Measurable fun state :
      FigureOneIdealExperimentSpace q × BalancedCoolingHistory q.n =>
        (figureOneIdealPhaseEstimator q p (state.1 p),
          figureOneIdealPhaseRetainedPoint q p (state.1 p)) :=
    ((figureOneIdealPhaseEstimator_measurable q p).comp hsample).prodMk
      ((measurable_figureOneIdealPhaseRetainedPoint q p).comp hsample)
  have hsome : Measurable fun state :
      FigureOneIdealExperimentSpace q × BalancedCoolingHistory q.n =>
      balancedCoolingHistorySnocTerminal state.2 (some
        (figureOneIdealPhaseEstimator q p (state.1 p),
          figureOneIdealPhaseRetainedPoint q p (state.1 p))) :=
    measurable_balancedCoolingHistorySnocTerminal.comp
      (measurable_snd.prodMk (measurable_some.comp hresult))
  have hoption : Measurable fun state :
      FigureOneIdealExperimentSpace q × Option (BalancedCoolingHistory q.n) =>
      match state.2 with
      | none => none
      | some history => balancedCoolingHistorySnocTerminal history (some
          (figureOneIdealPhaseEstimator q p (state.1 p),
            figureOneIdealPhaseRetainedPoint q p (state.1 p))) := by
    convert Measurable.optionCases
      ((fun _ => 0), 0, (1 : ℝ), (0 : AmbientSpace q.n))
      (noneValue := fun _ : FigureOneIdealExperimentSpace q =>
        (none : Option (BalancedCoolingHistory q.n)))
      (someValue := fun state =>
        balancedCoolingHistorySnocTerminal state.2 (some
          (figureOneIdealPhaseEstimator q p (state.1 p),
            figureOneIdealPhaseRetainedPoint q p (state.1 p))))
      measurable_const hsome using 1
    funext state
    cases state.2 <;> rfl
  exact measurable_fst.prodMk hoption

theorem figureOneIdealChronologicalAppend_coordinate
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (samples : FigureOneIdealExperimentSpace q)
    (history : BalancedCoolingHistory q.n)
    (hcount : history.2.1 = phase) :
    balancedCoolingChronologicalPhaseVariable q (phase + 1)
        (figureOneIdealChronologicalAppend q phase hphase
          (samples, some history)).2 =
      figureOneChronologicalIdealCoordinate q (phase + 1) samples := by
  rw [show figureOneIdealChronologicalAppend q phase hphase
      (samples, some history) =
      (samples, balancedCoolingHistorySnocTerminal history (some
        (figureOneIdealPhaseEstimator q
            (figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩)
            (samples (figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩)),
          figureOneIdealPhaseRetainedPoint q
            (figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩)
            (samples (figureOneChronologicalPhaseOrder q ⟨phase, hphase⟩))))) by
    rfl]
  rw [balancedCoolingHistorySnocTerminal_coordinate q phase history hcount _ hphase]
  unfold figureOneChronologicalIdealCoordinate figureOneIdealCoordinate
  rw [figureOneChronologicalPhaseAt_succ q phase hphase]

/-- Iterate the schedule-targeted endpoint transition while accumulating one
phase observable.  The carried state is speedy-space and the returned state
is converted back to target coordinates. -/
noncomputable def scheduledBalancedTransitionCollectLaw
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ℕ → ℝ → AmbientSpace q.n →
      Measure (Option (ℝ × AmbientSpace q.n))
  | 0, total, current =>
      Measure.dirac (some (total, (accuracyScaleFactor q)⁻¹ • current))
  | samples + 1, total, current =>
      (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride retryLimit current).bind fun result =>
          match result with
          | none => Measure.dirac none
          | some target =>
              scheduledBalancedTransitionCollectLaw q I sigma2 weight
                proposalCap properStride retryLimit samples
                (total + weight target) (accuracyScaleFactor q • target)

theorem scheduledBalancedTransitionCollectLaw_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ samples,
      Measurable (fun state : ℝ × AmbientSpace q.n =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples state.1 state.2) ∧
      ∀ total current, IsProbabilityMeasure
        (scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples total current) := by
  have htransition :=
    scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2 proposalCap properStride retryLimit
  intro samples
  induction samples with
  | zero =>
      constructor
      · exact Measure.measurable_dirac.comp <|
          measurable_some.comp <| measurable_fst.prodMk <|
            (measurable_const : Measurable fun _ :
              ℝ × AmbientSpace q.n => (accuracyScaleFactor q)⁻¹).smul
                measurable_snd
      · intro total current
        change IsProbabilityMeasure
          (Measure.dirac
            (some (total, (accuracyScaleFactor q)⁻¹ • current)))
        infer_instance
  | succ samples ih =>
      let tail : (ℝ × AmbientSpace q.n) × Option (AmbientSpace q.n) →
          Measure (Option (ℝ × AmbientSpace q.n)) := fun value =>
        match value.2 with
        | none => Measure.dirac none
        | some target =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
              properStride retryLimit samples
              (value.1.1 + weight target) (accuracyScaleFactor q • target)
      have hsome : Measurable fun value :
          (ℝ × AmbientSpace q.n) × AmbientSpace q.n =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
              properStride retryLimit samples
              (value.1.1 + weight value.2)
              (accuracyScaleFactor q • value.2) := by
        exact ih.1.comp <|
          ((measurable_fst.comp measurable_fst).add
            (hweight.comp measurable_snd)).prodMk <|
              (measurable_const : Measurable fun _ :
                (ℝ × AmbientSpace q.n) × AmbientSpace q.n =>
                  accuracyScaleFactor q).smul measurable_snd
      have htail : Measurable tail := by
        dsimp only [tail]
        convert Measurable.optionElimParam
          (noneValue := fun _ : ℝ × AmbientSpace q.n =>
            Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
          (someValue := fun value =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
              properStride retryLimit samples
              (value.1.1 + weight value.2)
              (accuracyScaleFactor q • value.2))
          (Measure.measurable_dirac.comp measurable_const) hsome using 1
        ext value
        cases value.2 <;> rfl
      have hlaw : (fun state : ℝ × AmbientSpace q.n =>
          scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
            properStride retryLimit (samples + 1) state.1 state.2) =
          fun state =>
            (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
              properStride retryLimit state.2).bind
                (fun result => tail (state, result)) := by
        funext state
        simp only [scheduledBalancedTransitionCollectLaw]
        apply Measure.bind_congr_right
        filter_upwards with result
        cases result <;> simp [tail]
      constructor
      · rw [hlaw]
        exact measurable_measure_bind_param_variable
          (htransition.1.comp measurable_snd)
          (fun state => htransition.2 state.2) htail
      · intro total current
        rw [congrFun hlaw (total, current)]
        let _ : IsProbabilityMeasure
            (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
              properStride retryLimit current) := htransition.2 current
        apply MeasureTheory.isProbabilityMeasure_bind
          (htail.comp (measurable_const.prodMk measurable_id)).aemeasurable
        filter_upwards with result
        cases result with
        | none =>
            change IsProbabilityMeasure
              (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
            infer_instance
        | some target => exact ih.2 _ _

/-- Measure-level scheduled Gaussian phase, expressed through the endpoint
transition recursion used by the coupling argument. -/
noncomputable def scheduledBalancedCoolingRatioTransitionLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 tau2 : ℝ)
    (current : AmbientSpace q.n) :
    Measure (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedTransitionCollectLaw q I sigma2
      (gaussianRatioWeight sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2) 0
      (accuracyScaleFactor q • current)).map
    (balancedCoolingAverage (figureOnePhaseSampleCount q sigma2))

theorem scheduledBalancedCoolingRatioTransitionLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (tau2 : ℝ) :
    Measurable
      (scheduledBalancedCoolingRatioTransitionLaw parameters q I sigma2 tau2) ∧
    ∀ current, IsProbabilityMeasure
      (scheduledBalancedCoolingRatioTransitionLaw parameters q I sigma2 tau2
        current) := by
  let cap := parameters.proposalCap q sigma2
  let stride := parameters.properStride q sigma2
  let retries := parameters.retryLimit q sigma2
  let samples := figureOnePhaseSampleCount q sigma2
  let weight : AmbientSpace q.n → ℝ := gaussianRatioWeight sigma2 tau2
  have hcollect :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I hsigma2 (measurable_gaussianRatioWeight sigma2 tau2)
        cap stride retries samples
  have hscale : Measurable fun current : AmbientSpace q.n =>
      accuracyScaleFactor q • current :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hsource : Measurable fun current =>
      scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride retries
        samples 0 (accuracyScaleFactor q • current) :=
    hcollect.1.comp (measurable_const.prodMk hscale)
  have havg := measurable_balancedCoolingAverage (n := q.n) samples
  constructor
  · unfold scheduledBalancedCoolingRatioTransitionLaw
    exact (Measure.measurable_map _ havg).comp hsource
  · intro current
    unfold scheduledBalancedCoolingRatioTransitionLaw
    let _ : IsProbabilityMeasure
        (scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
          retries samples 0 (accuracyScaleFactor q • current)) :=
      hcollect.2 0 (accuracyScaleFactor q • current)
    exact Measure.isProbabilityMeasure_map havg.aemeasurable

/-- Scheduled terminal phase at the measure level. -/
noncomputable def scheduledBalancedCoolingUniformTransitionLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) :
    Measure (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedTransitionCollectLaw q I sigma2
      (uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q) 0
      (accuracyScaleFactor q • current)).map
    (balancedCoolingAverage (figureOneSampleCount q))

theorem scheduledBalancedCoolingUniformTransitionLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    Measurable
      (scheduledBalancedCoolingUniformTransitionLaw parameters q I sigma2) ∧
    ∀ current, IsProbabilityMeasure
      (scheduledBalancedCoolingUniformTransitionLaw parameters q I sigma2
        current) := by
  let cap := parameters.proposalCap q sigma2
  let stride := parameters.properStride q sigma2
  let retries := parameters.retryLimit q sigma2
  let samples := figureOneSampleCount q
  let weight : AmbientSpace q.n → ℝ := uniformRatioWeight sigma2
  have hcollect :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I hsigma2 (measurable_uniformRatioWeight sigma2)
        cap stride retries samples
  have hscale : Measurable fun current : AmbientSpace q.n =>
      accuracyScaleFactor q • current :=
    (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id
  have hsource : Measurable fun current =>
      scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride retries
        samples 0 (accuracyScaleFactor q • current) :=
    hcollect.1.comp (measurable_const.prodMk hscale)
  have havg := measurable_balancedCoolingAverage (n := q.n) samples
  constructor
  · unfold scheduledBalancedCoolingUniformTransitionLaw
    exact (Measure.measurable_map _ havg).comp hsource
  · intro current
    unfold scheduledBalancedCoolingUniformTransitionLaw
    let _ : IsProbabilityMeasure
        (scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
          retries samples 0 (accuracyScaleFactor q • current)) :=
      hcollect.2 0 (accuracyScaleFactor q • current)
    exact Measure.isProbabilityMeasure_map havg.aemeasurable

/-- One schedule-targeted phase appended to a chronological history. -/
noncomputable def scheduledBalancedForwardPhaseKernel
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n)) := fun history =>
  match history with
  | none => Measure.dirac none
  | some history =>
      if phase < terminalPhaseSteps q then
        (scheduledBalancedCoolingRatioTransitionLaw parameters q I
          (scheduleValue q phase) (scheduleValue q (phase + 1))
          history.2.2.2).map (balancedCoolingHistorySnocTerminal history)
      else
        (scheduledBalancedCoolingUniformTransitionLaw parameters q I
          (terminalVariance q) history.2.2.2).map
            (balancedCoolingHistorySnocTerminal history)

theorem scheduledBalancedForwardPhaseKernel_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    Measurable (scheduledBalancedForwardPhaseKernel parameters q I phase) ∧
    ∀ history, IsProbabilityMeasure
      (scheduledBalancedForwardPhaseKernel parameters q I phase history) := by
  have hgaussian :=
    scheduledBalancedCoolingRatioTransitionLaw_measurable_and_probability
      parameters q I (scheduleValue_pos q phase) (scheduleValue q (phase + 1))
  have hterminal :=
    scheduledBalancedCoolingUniformTransitionLaw_measurable_and_probability
      parameters q I (terminalVariance_pos' q)
  have hsome : Measurable fun history : BalancedCoolingHistory q.n =>
      if phase < terminalPhaseSteps q then
        (scheduledBalancedCoolingRatioTransitionLaw parameters q I
          (scheduleValue q phase) (scheduleValue q (phase + 1))
          history.2.2.2).map (balancedCoolingHistorySnocTerminal history)
      else
        (scheduledBalancedCoolingUniformTransitionLaw parameters q I
          (terminalVariance q) history.2.2.2).map
            (balancedCoolingHistorySnocTerminal history) := by
    split_ifs
    · apply measurable_measure_map_param_variable
      · exact hgaussian.1.comp <|
          measurable_snd.comp
            (measurable_snd.comp (measurable_snd.comp measurable_id))
      · intro history
        exact hgaussian.2 history.2.2.2
      · exact measurable_balancedCoolingHistorySnocTerminal.comp
          (measurable_fst.prodMk measurable_snd)
    · apply measurable_measure_map_param_variable
      · exact hterminal.1.comp <|
          measurable_snd.comp
            (measurable_snd.comp (measurable_snd.comp measurable_id))
      · intro history
        exact hterminal.2 history.2.2.2
      · exact measurable_balancedCoolingHistorySnocTerminal.comp
          (measurable_fst.prodMk measurable_snd)
  constructor
  · convert Measurable.optionElim
      (Measure.dirac (none : Option (BalancedCoolingHistory q.n))) hsome using 1
    funext history
    cases history <;> rfl
  · intro history
    cases history with
    | none =>
        change IsProbabilityMeasure
          (Measure.dirac (none : Option (BalancedCoolingHistory q.n)))
        infer_instance
    | some history =>
        unfold scheduledBalancedForwardPhaseKernel
        split_ifs
        · let _ : IsProbabilityMeasure
              (scheduledBalancedCoolingRatioTransitionLaw parameters q I
                (scheduleValue q phase) (scheduleValue q (phase + 1))
                history.2.2.2) := hgaussian.2 _
          exact Measure.isProbabilityMeasure_map
            ((measurable_balancedCoolingHistorySnocTerminal (n := q.n)).comp
              (measurable_const.prodMk measurable_id)).aemeasurable
        · let _ : IsProbabilityMeasure
              (scheduledBalancedCoolingUniformTransitionLaw parameters q I
                (terminalVariance q) history.2.2.2) := hterminal.2 _
          exact Measure.isProbabilityMeasure_map
            ((measurable_balancedCoolingHistorySnocTerminal (n := q.n)).comp
              (measurable_const.prodMk measurable_id)).aemeasurable

/-- The chronological post-initial history law of the schedule-targeted
transition model. -/
noncomputable def scheduledBalancedForwardHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phases : ℕ) :
    Measure (Option (BalancedCoolingHistory q.n)) :=
  iteratedKernelLaw (scheduledBalancedForwardPhaseKernel parameters q I)
    ((truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        balancedCoolingInitialHistory) phases

theorem scheduledBalancedForwardHistoryLaw_isProbabilityMeasure
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phases : ℕ) :
    IsProbabilityMeasure
      (scheduledBalancedForwardHistoryLaw parameters q I phases) := by
  unfold scheduledBalancedForwardHistoryLaw
  apply iteratedKernelLaw_isProbabilityMeasure
  · exact Measure.isProbabilityMeasure_map
      measurable_balancedCoolingInitialHistory.aemeasurable
  · intro i
    exact (scheduledBalancedForwardPhaseKernel_measurable_and_probability
      parameters q I i).1
  · intro i history
    exact (scheduledBalancedForwardPhaseKernel_measurable_and_probability
      parameters q I i).2 history

theorem scheduledBalancedForwardPhaseKernel_ae_hasProduct
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase m : ℕ)
    (history : Option (BalancedCoolingHistory q.n))
    (hproduct : BalancedCoolingHistoryHasProduct m history) :
    ∀ᵐ next ∂scheduledBalancedForwardPhaseKernel parameters q I phase history,
      BalancedCoolingHistoryHasProduct (m + 1) next := by
  cases history with
  | none =>
      unfold scheduledBalancedForwardPhaseKernel
      apply (ae_dirac_iff
        (measurableSet_balancedCoolingHistoryHasProduct _)).2
      simp [BalancedCoolingHistoryHasProduct]
  | some history =>
      unfold scheduledBalancedForwardPhaseKernel
      split_ifs
      · apply (ae_map_iff
          ((measurable_balancedCoolingHistorySnocTerminal (n := q.n)).comp
            (measurable_const.prodMk measurable_id)).aemeasurable
          (measurableSet_balancedCoolingHistoryHasProduct _)).2
        filter_upwards with result
        exact hproduct.snocTerminal result
      · apply (ae_map_iff
          ((measurable_balancedCoolingHistorySnocTerminal (n := q.n)).comp
            (measurable_const.prodMk measurable_id)).aemeasurable
          (measurableSet_balancedCoolingHistoryHasProduct _)).2
        filter_upwards with result
        exact hproduct.snocTerminal result

theorem scheduledBalancedForwardHistoryLaw_ae_hasProduct
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) : ∀ phases,
    ∀ᵐ history ∂scheduledBalancedForwardHistoryLaw parameters q I phases,
      BalancedCoolingHistoryHasProduct phases history := by
  intro phases
  induction phases with
  | zero =>
      unfold scheduledBalancedForwardHistoryLaw
      apply (ae_map_iff measurable_balancedCoolingInitialHistory.aemeasurable
        (measurableSet_balancedCoolingHistoryHasProduct 0)).2
      filter_upwards with point
      simp [balancedCoolingInitialHistory, BalancedCoolingHistoryHasProduct]
  | succ phases ih =>
      let prefixLaw :=
        scheduledBalancedForwardHistoryLaw parameters q I phases
      let kernel := scheduledBalancedForwardPhaseKernel parameters q I phases
      let good : Set (Option (BalancedCoolingHistory q.n)) :=
        {history | BalancedCoolingHistoryHasProduct (phases + 1) history}
      have hgood : MeasurableSet good :=
        measurableSet_balancedCoolingHistoryHasProduct _
      have hkernel : Measurable kernel :=
        (scheduledBalancedForwardPhaseKernel_measurable_and_probability
          parameters q I phases).1
      change ∀ᵐ history ∂prefixLaw.bind kernel,
        BalancedCoolingHistoryHasProduct (phases + 1) history
      apply MeasureTheory.mem_ae_iff.mpr
      change (prefixLaw.bind kernel) goodᶜ = 0
      rw [Measure.bind_apply hgood.compl hkernel.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ih] with history hhistory
      exact MeasureTheory.mem_ae_iff.mp
        (scheduledBalancedForwardPhaseKernel_ae_hasProduct
          parameters q I phases phases history hhistory)

/-! ## Common state for outer phase replacement -/

/-- Carry an auxiliary ideal experiment unchanged while a history kernel
updates the chronological executable component. -/
noncomputable def carryHistoryKernel
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (K : ℕ → B → Measure B) : ℕ → A × B → Measure (A × B) :=
  fun phase state => (K phase state.2).map fun next => (state.1, next)

theorem carryHistoryKernel_measurable_and_probability
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (K : ℕ → B → Measure B)
    (hKmeas : ∀ phase, Measurable (K phase))
    (hKprob : ∀ phase state, IsProbabilityMeasure (K phase state))
    (phase : ℕ) :
    Measurable (carryHistoryKernel (A := A) K phase) ∧
    ∀ state, IsProbabilityMeasure (carryHistoryKernel (A := A) K phase state) := by
  constructor
  · unfold carryHistoryKernel
    apply measurable_measure_map_param_variable
    · exact (hKmeas phase).comp measurable_snd
    · intro state
      exact hKprob phase state.2
    · exact (measurable_fst.comp measurable_fst).prodMk measurable_snd
  · intro state
    unfold carryHistoryKernel
    let _ : IsProbabilityMeasure (K phase state.2) := hKprob phase state.2
    exact Measure.isProbabilityMeasure_map
      (measurable_const.prodMk measurable_id).aemeasurable

theorem map_snd_bind_carryHistoryKernel
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (K : ℕ → B → Measure B)
    (hKmeas : ∀ phase, Measurable (K phase))
    (hKprob : ∀ phase state, IsProbabilityMeasure (K phase state))
    (mu : Measure (A × B)) (phase : ℕ) :
    (mu.bind (carryHistoryKernel (A := A) K phase)).map Prod.snd =
      (mu.map Prod.snd).bind (K phase) := by
  have hcarry := carryHistoryKernel_measurable_and_probability
    (A := A) K hKmeas hKprob phase
  calc
    (mu.bind (carryHistoryKernel (A := A) K phase)).map Prod.snd =
        mu.bind fun state =>
          (carryHistoryKernel (A := A) K phase state).map Prod.snd :=
      map_bind_eq_bind_map_of_measurable _ hcarry.1 measurable_snd
    _ = mu.bind (K phase ∘ Prod.snd) := by
      apply Measure.bind_congr_right
      filter_upwards with state
      unfold carryHistoryKernel
      have hpair : Measurable (fun next : B => (state.1, next)) :=
        measurable_const.prodMk measurable_id
      rw [Measure.map_map
        (show Measurable (Prod.snd : A × B → B) from measurable_snd) hpair]
      change Measure.map (Prod.snd ∘ fun next : B => (state.1, next))
          (K phase state.2) = K phase state.2
      calc
        _ = Measure.map id (K phase state.2) := by
          apply Measure.map_congr
          filter_upwards with next
          rfl
        _ = _ := Measure.map_id
    _ = (mu.map Prod.snd).bind (K phase) :=
      (map_bind_eq_bind_comp _ Prod.snd measurable_snd (K phase)
        (hKmeas phase)).symm

theorem map_snd_iteratedKernelLaw_carryHistoryKernel
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (K : ℕ → B → Measure B)
    (hKmeas : ∀ phase, Measurable (K phase))
    (hKprob : ∀ phase state, IsProbabilityMeasure (K phase state))
    (initial : Measure (A × B)) : ∀ phases,
    (iteratedKernelLaw (carryHistoryKernel (A := A) K) initial phases).map
        Prod.snd =
      iteratedKernelLaw K (initial.map Prod.snd) phases := by
  intro phases
  induction phases with
  | zero => rfl
  | succ phases ih =>
      rw [iteratedKernelLaw_succ, iteratedKernelLaw_succ,
        map_snd_bind_carryHistoryKernel K hKmeas hKprob, ih]

/-- Common initial state: an independent ideal experiment is carried beside
the exact restricted-Gaussian starting history. -/
noncomputable def scheduledChronologicalCommonInitial
    (q : VolumeParams) (I : VolumeInput q.n) :
    Measure (FigureOneIdealExperimentSpace q ×
      Option (BalancedCoolingHistory q.n)) :=
  (figureOneIdealExperimentLaw q I).prod
    ((truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        balancedCoolingInitialHistory)

theorem scheduledChronologicalCommonInitial_map_snd
    (q : VolumeParams) (I : VolumeInput q.n) :
    (scheduledChronologicalCommonInitial q I).map Prod.snd =
      (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
          balancedCoolingInitialHistory := by
  unfold scheduledChronologicalCommonInitial
  let _ : IsProbabilityMeasure (figureOneIdealExperimentLaw q I) :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  simpa using Measure.map_snd_prod

theorem scheduledChronologicalActualIteration_map_snd
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phases : ℕ) :
    (iteratedKernelLaw
        (carryHistoryKernel (A := FigureOneIdealExperimentSpace q)
          (scheduledBalancedForwardPhaseKernel parameters q I))
        (scheduledChronologicalCommonInitial q I) phases).map Prod.snd =
      scheduledBalancedForwardHistoryLaw parameters q I phases := by
  rw [map_snd_iteratedKernelLaw_carryHistoryKernel
    (scheduledBalancedForwardPhaseKernel parameters q I)
    (fun phase =>
      (scheduledBalancedForwardPhaseKernel_measurable_and_probability
        parameters q I phase).1)
    (fun phase history =>
      (scheduledBalancedForwardPhaseKernel_measurable_and_probability
        parameters q I phase).2 history),
    scheduledChronologicalCommonInitial_map_snd]
  rfl

/-- Ideal outer-phase kernel on the common state.  It reads the next
independent phase block already present in the ideal experiment and appends
its average and a retained stationary point deterministically. -/
noncomputable def figureOneIdealChronologicalPhaseKernel
    (q : VolumeParams) : ℕ →
    FigureOneIdealExperimentSpace q × Option (BalancedCoolingHistory q.n) →
      Measure (FigureOneIdealExperimentSpace q ×
        Option (BalancedCoolingHistory q.n)) := fun phase state =>
  if hphase : phase < figureOneDependentPhaseCount q then
    Measure.dirac (figureOneIdealChronologicalAppend q phase hphase state)
  else Measure.dirac state

theorem figureOneIdealChronologicalPhaseKernel_measurable_and_probability
    (q : VolumeParams) (phase : ℕ) :
    Measurable (figureOneIdealChronologicalPhaseKernel q phase) ∧
    ∀ state, IsProbabilityMeasure
      (figureOneIdealChronologicalPhaseKernel q phase state) := by
  constructor
  · unfold figureOneIdealChronologicalPhaseKernel
    split_ifs with hphase
    · exact Measure.measurable_dirac.comp
        (measurable_figureOneIdealChronologicalAppend q phase hphase)
    · exact Measure.measurable_dirac
  · intro state
    unfold figureOneIdealChronologicalPhaseKernel
    split_ifs <;> infer_instance

/-- The actual outer-phase kernel on the common state carries the independent
ideal experiment untouched and updates only the scheduled history. -/
noncomputable def figureOneScheduledActualChronologicalPhaseKernel
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :=
  carryHistoryKernel (A := FigureOneIdealExperimentSpace q)
    (scheduledBalancedForwardPhaseKernel parameters q I)

theorem figureOneScheduledActualChronologicalPhaseKernel_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    Measurable
      (figureOneScheduledActualChronologicalPhaseKernel parameters q I phase) ∧
    ∀ state, IsProbabilityMeasure
      (figureOneScheduledActualChronologicalPhaseKernel parameters q I phase
        state) :=
  carryHistoryKernel_measurable_and_probability
    (scheduledBalancedForwardPhaseKernel parameters q I)
    (fun i =>
      (scheduledBalancedForwardPhaseKernel_measurable_and_probability
        parameters q I i).1)
    (fun i history =>
      (scheduledBalancedForwardPhaseKernel_measurable_and_probability
        parameters q I i).2 history) phase

/-- Deterministic state transformer underlying the ideal chronological
kernel. -/
noncomputable def figureOneIdealChronologicalState
    (q : VolumeParams) : ℕ →
    FigureOneIdealExperimentSpace q × Option (BalancedCoolingHistory q.n) →
      FigureOneIdealExperimentSpace q × Option (BalancedCoolingHistory q.n)
  | 0, state => state
  | phases + 1, state =>
      let previous := figureOneIdealChronologicalState q phases state
      if hphase : phases < figureOneDependentPhaseCount q then
        figureOneIdealChronologicalAppend q phases hphase previous
      else previous

theorem measurable_figureOneIdealChronologicalState
    (q : VolumeParams) : ∀ phases,
    Measurable (figureOneIdealChronologicalState q phases) := by
  intro phases
  induction phases with
  | zero => exact measurable_id
  | succ phases ih =>
      simp only [figureOneIdealChronologicalState]
      split_ifs with hphase
      · exact (measurable_figureOneIdealChronologicalAppend q phases hphase).comp ih
      · exact ih

theorem figureOneIdealChronologicalState_fst
    (q : VolumeParams) (phases : ℕ)
    (state : FigureOneIdealExperimentSpace q ×
      Option (BalancedCoolingHistory q.n)) :
    (figureOneIdealChronologicalState q phases state).1 = state.1 := by
  induction phases with
  | zero => rfl
  | succ phases ih =>
      simp only [figureOneIdealChronologicalState]
      split_ifs <;>
        simp [figureOneIdealChronologicalAppend, ih]

/-- Through the finite horizon, deterministic ideal appends build exactly
the chronological product of ideal phase averages. -/
theorem figureOneIdealChronologicalState_product
    (q : VolumeParams) (samples : FigureOneIdealExperimentSpace q)
    (initialHistory : BalancedCoolingHistory q.n)
    (hinitialCount : initialHistory.2.1 = 0)
    (hinitialProduct : initialHistory.2.2.1 = 1) :
    ∀ phases, phases ≤ figureOneDependentPhaseCount q →
      ∃ history,
        (figureOneIdealChronologicalState q phases
          (samples, some initialHistory)).2 = some history ∧
        history.2.1 = phases ∧
        history.2.2.1 =
          dependentPhaseSampleProduct
            (figureOneChronologicalIdealCoordinate q) phases samples := by
  intro phases hphases
  induction phases with
  | zero =>
      refine ⟨initialHistory, rfl, hinitialCount, ?_⟩
      simpa [dependentPhaseSampleProduct_zero] using hinitialProduct
  | succ phases ih =>
      have hphase : phases < figureOneDependentPhaseCount q := by omega
      obtain ⟨history, hstate, hcount, hproduct⟩ :=
        ih (Nat.le_of_succ_le hphases)
      let next := balancedCoolingHistorySnocTerminal history <| some
        (figureOneIdealPhaseEstimator q
            (figureOneChronologicalPhaseOrder q ⟨phases, hphase⟩)
            (samples (figureOneChronologicalPhaseOrder q ⟨phases, hphase⟩)),
          figureOneIdealPhaseRetainedPoint q
            (figureOneChronologicalPhaseOrder q ⟨phases, hphase⟩)
            (samples (figureOneChronologicalPhaseOrder q ⟨phases, hphase⟩)))
      have hnext : (figureOneIdealChronologicalState q (phases + 1)
          (samples, some initialHistory)).2 = next := by
        simp only [figureOneIdealChronologicalState]
        rw [dif_pos hphase]
        rw [show figureOneIdealChronologicalState q phases
            (samples, some initialHistory) = (samples, some history) by
          apply Prod.ext
          · exact (figureOneIdealChronologicalState_fst q phases _).trans rfl
          · exact hstate]
        rfl
      let nextHistory : BalancedCoolingHistory q.n :=
        (fun k => if k = history.2.1 then
            figureOneIdealPhaseEstimator q
              (figureOneChronologicalPhaseOrder q ⟨phases, hphase⟩)
              (samples (figureOneChronologicalPhaseOrder q ⟨phases, hphase⟩))
            else history.1 k,
          history.2.1 + 1,
          history.2.2.1 * figureOneIdealPhaseEstimator q
            (figureOneChronologicalPhaseOrder q ⟨phases, hphase⟩)
            (samples (figureOneChronologicalPhaseOrder q ⟨phases, hphase⟩)),
          figureOneIdealPhaseRetainedPoint q
            (figureOneChronologicalPhaseOrder q ⟨phases, hphase⟩)
            (samples (figureOneChronologicalPhaseOrder q ⟨phases, hphase⟩)))
      have hnextSome : next = some nextHistory := by
        rfl
      refine ⟨nextHistory, hnext.trans hnextSome, ?_, ?_⟩
      · simp [nextHistory, hcount]
      · dsimp only [nextHistory]
        rw [hproduct, dependentPhaseSampleProduct_succ]
        congr 1
        unfold figureOneChronologicalIdealCoordinate figureOneIdealCoordinate
        rw [figureOneChronologicalPhaseAt_succ q phases hphase]

theorem iteratedKernelLaw_figureOneIdealChronologicalPhaseKernel
    (q : VolumeParams)
    (initial : Measure (FigureOneIdealExperimentSpace q ×
      Option (BalancedCoolingHistory q.n))) : ∀ phases,
    iteratedKernelLaw (figureOneIdealChronologicalPhaseKernel q)
        initial phases =
      initial.map (figureOneIdealChronologicalState q phases) := by
  intro phases
  induction phases with
  | zero =>
      symm
      exact Measure.map_id
  | succ phases ih =>
      rw [iteratedKernelLaw_succ, ih]
      rw [map_bind_eq_bind_comp initial
        (figureOneIdealChronologicalState q phases)
        (measurable_figureOneIdealChronologicalState q phases)
        (figureOneIdealChronologicalPhaseKernel q phases)
        (figureOneIdealChronologicalPhaseKernel_measurable_and_probability
          q phases).1]
      have hkernel :
          figureOneIdealChronologicalPhaseKernel q phases ∘
              figureOneIdealChronologicalState q phases =
            fun state => Measure.dirac
              (figureOneIdealChronologicalState q (phases + 1) state) := by
        funext state
        simp only [figureOneIdealChronologicalPhaseKernel,
          figureOneIdealChronologicalState, Function.comp_apply]
        split_ifs <;> rfl
      rw [hkernel]
      exact Measure.bind_dirac_eq_map _
        (measurable_figureOneIdealChronologicalState q (phases + 1))

/-- A first scheduled endpoint replacement lifts through the whole remaining
phase without increasing the error. -/
theorem MeasureLeUpTo.bind_scheduledBalancedTransitionCollectLaw_of_first
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ)
    (mu : Measure (AmbientSpace q.n))
    (target : Measure (Option (AmbientSpace q.n)))
    {delta : ENNReal}
    (hfirst : MeasureLeUpTo
      (mu.bind (scheduledBalancedAccuracyTransitionLawAux q I sigma2
        proposalCap properStride retryLimit)) target delta) :
    MeasureLeUpTo
      (mu.bind fun current =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit (samples + 1) 0 current)
      (target.bind fun result =>
        match result with
        | none => Measure.dirac none
        | some point =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
              properStride retryLimit samples (weight point)
                (accuracyScaleFactor q • point))
      delta := by
  let tail : Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
    match result with
    | none => Measure.dirac none
    | some point =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples (weight point)
            (accuracyScaleFactor q • point)
  have hcollect :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I hsigma2 hweight proposalCap properStride retryLimit samples
  have htail : Measurable tail := by
    have hsome : Measurable fun point : AmbientSpace q.n =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples (weight point)
            (accuracyScaleFactor q • point) := by
      exact hcollect.1.comp <| hweight.prodMk <|
        (measurable_const : Measurable fun _ : AmbientSpace q.n =>
          accuracyScaleFactor q).smul measurable_id
    convert Measurable.optionElim
      (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
    funext result
    cases result <;> rfl
  have htailProb : ∀ result, IsProbabilityMeasure (tail result) := by
    intro result
    cases result with
    | none => infer_instance
    | some point => exact hcollect.2 _ _
  have htransition :=
    scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2 proposalCap properStride retryLimit
  have hsource :
      (mu.bind fun current =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit (samples + 1) 0 current) =
        (mu.bind (scheduledBalancedAccuracyTransitionLawAux q I sigma2
          proposalCap properStride retryLimit)).bind tail := by
    calc
      _ = mu.bind fun current =>
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride retryLimit current).bind tail := by
        apply Measure.bind_congr_right
        filter_upwards with current
        simp only [scheduledBalancedTransitionCollectLaw]
        apply Measure.bind_congr_right
        filter_upwards with result
        cases result <;> simp [tail]
      _ = _ :=
        (Measure.bind_bind htransition.1.aemeasurable htail.aemeasurable).symm
  change MeasureLeUpTo _ (target.bind tail) delta
  rw [hsource]
  exact hfirst.bind_same htail htailProb

/-- Scheduled complete-phase form of Lemma 7.17(c), reduced to the uniform
warm-start bound for its first retained transition. -/
theorem approxIndepFun_scheduledBalancedCompletePhase_of_warm_first
    {H : Type*} [MeasurableSpace H]
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (proposalCap properStride retryLimit samples : ℕ)
    (history : Measure H) [IsProbabilityMeasure history]
    (state : H → AmbientSpace q.n) (hstate : Measurable state)
    (target : Measure (Option (AmbientSpace q.n)))
    [IsProbabilityMeasure target]
    {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (hfirst : ∀ mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu →
      Arlib.IsWarm 2 mu (history.map state) →
      MeasureLeUpTo
        (mu.bind (scheduledBalancedAccuracyTransitionLawAux q I sigma2
          proposalCap properStride retryLimit)) target delta)
    (pastProduct : H → ℝ)
    (nextEstimator : Option (ℝ × AmbientSpace q.n) → ℝ)
    (hpastProduct : Measurable pastProduct)
    (hnextEstimator : Measurable nextEstimator)
    (k m : ℕ) (nu : ℝ)
    (hbudget : (delta + delta).toReal ≤
      3 * (k : ℝ) * (m : ℝ) * nu) :
    let phaseTarget := target.bind fun result =>
      match result with
      | none => Measure.dirac none
      | some point =>
          scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
            properStride retryLimit samples (weight point)
              (accuracyScaleFactor q • point)
    ApproxIndepFun (3 * (k : ℝ) * (m : ℝ) * nu)
      (pastProduct ∘ Prod.fst) (nextEstimator ∘ Prod.snd)
      (sequentialPairLaw history
        ((fun current =>
          scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
            properStride retryLimit (samples + 1) 0 current) ∘ state)) := by
  dsimp only
  let phaseKernel : AmbientSpace q.n →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun current =>
    scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
      properStride retryLimit (samples + 1) 0 current
  let phaseTarget : Measure (Option (ℝ × AmbientSpace q.n)) :=
    target.bind fun result =>
      match result with
      | none => Measure.dirac none
      | some point =>
          scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
            properStride retryLimit samples (weight point)
              (accuracyScaleFactor q • point)
  have hphase :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I hsigma2 hweight proposalCap properStride retryLimit (samples + 1)
  have htail :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I hsigma2 hweight proposalCap properStride retryLimit samples
  let tail : Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
    match result with
    | none => Measure.dirac none
    | some point =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples (weight point)
            (accuracyScaleFactor q • point)
  have htailMeas : Measurable tail := by
    have hsome : Measurable fun point : AmbientSpace q.n =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
          properStride retryLimit samples (weight point)
            (accuracyScaleFactor q • point) := by
      exact htail.1.comp <| hweight.prodMk <|
        (measurable_const : Measurable fun _ : AmbientSpace q.n =>
          accuracyScaleFactor q).smul measurable_id
    convert Measurable.optionElim
      (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
    funext result
    cases result <;> rfl
  have htailProb : ∀ result, IsProbabilityMeasure (tail result) := by
    intro result
    cases result with
    | none => infer_instance
    | some point => exact htail.2 _ _
  let _ : IsProbabilityMeasure phaseTarget :=
    MeasureTheory.isProbabilityMeasure_bind htailMeas.aemeasurable
      (ae_of_all _ htailProb)
  apply approxIndepFun_accumulatedProduct_nextEstimator_of_state_warm_leUpTo
    history state hstate
      (hphase.1.comp (measurable_const.prodMk measurable_id))
      (fun current => hphase.2 0 current) phaseTarget hdelta ?_
      (pastProduct := pastProduct) (nextEstimator := nextEstimator)
      hpastProduct hnextEstimator k m nu hbudget
  intro mu hmu hwarm
  let _ : IsProbabilityMeasure mu := hmu
  exact MeasureLeUpTo.bind_scheduledBalancedTransitionCollectLaw_of_first
    q I hsigma2 hweight proposalCap properStride retryLimit samples mu target
      (hfirst mu hmu hwarm)

#print axioms scheduledBalancedTransitionCollectLaw_measurable_and_probability
#print axioms MeasureLeUpTo.bind_scheduledBalancedTransitionCollectLaw_of_first
#print axioms approxIndepFun_scheduledBalancedCompletePhase_of_warm_first
#print axioms measurable_figureOneIdealChronologicalAppend
#print axioms figureOneIdealChronologicalAppend_coordinate
#print axioms scheduledBalancedForwardPhaseKernel_measurable_and_probability
#print axioms scheduledBalancedForwardHistoryLaw_isProbabilityMeasure
#print axioms map_snd_iteratedKernelLaw_carryHistoryKernel
#print axioms scheduledChronologicalActualIteration_map_snd

end

end ArlibCommunity.Algorithms.CV18
