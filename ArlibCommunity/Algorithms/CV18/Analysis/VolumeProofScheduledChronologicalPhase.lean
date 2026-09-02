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

end

end ArlibCommunity.Algorithms.CV18
