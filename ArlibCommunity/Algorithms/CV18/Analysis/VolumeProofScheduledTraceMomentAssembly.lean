/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledPhaseL2
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedHistoryMomentBridge
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofActualMeanTruncation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceCapstoneExecutable

/-!
# Actual-mean moment assembly for the executable scheduled trace

The older phase-moment assembly is centered at the exact ideal phase means.
The scheduled finite execution is only approximately stationary, so its
truncation is instead centered at its actual mean.  This file records the
same sharp one-phase truncation estimates with that actual center and then
assembles the finite products used by CV18 Lemmas 7.14--7.15.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-! ## Strict positivity of successful phase collectors -/

def ScheduledCollectedTotalPositive :
    Option (ℝ × AmbientSpace n) → Prop
  | none => True
  | some result => 0 < result.1

theorem measurableSet_scheduledCollectedTotalPositive :
    MeasurableSet {result : Option (ℝ × AmbientSpace n) |
      ScheduledCollectedTotalPositive result} := by
  let A : Set (ℝ × AmbientSpace n) := {result | 0 < result.1}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const measurable_fst
  rw [show {result : Option (ℝ × AmbientSpace n) |
      ScheduledCollectedTotalPositive result} =
      {none} ∪ optionSomeEvent A by
    ext result
    cases result <;> simp [ScheduledCollectedTotalPositive,
      optionSomeEvent, A]]
  exact measurableSet_option_none.union (measurableSet_optionSomeEvent hA)

/-- If at least one strictly positive observation is requested, every
successful branch of the finite scheduled collector has positive total. -/
theorem scheduledBalancedTransitionCollectLaw_ae_total_positive
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (hweightPos : ∀ x, 0 < weight x)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ samples, 0 < samples → ∀ total current, 0 ≤ total →
      ∀ᵐ result ∂scheduledBalancedTransitionCollectLaw q I sigma2 weight
          proposalCap properStride retryLimit samples total current,
        ScheduledCollectedTotalPositive result := by
  have htransition :=
    scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
      q I hsigma2 proposalCap properStride retryLimit
  intro samples
  induction samples with
  | zero => simp
  | succ samples ih =>
      intro hsamples total current htotal
      let tail : Option (AmbientSpace q.n) →
          Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
        match result with
        | none => Measure.dirac none
        | some target =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight
              proposalCap properStride retryLimit samples
              (total + weight target) (accuracyScaleFactor q • target)
      have htail : Measurable tail := by
        dsimp only [tail]
        have hcollect :=
          (scheduledBalancedTransitionCollectLaw_measurable_and_probability
            q I hsigma2 hweight proposalCap properStride retryLimit samples).1
        have hsome : Measurable fun target : AmbientSpace q.n =>
            scheduledBalancedTransitionCollectLaw q I sigma2 weight
              proposalCap properStride retryLimit samples
              (total + weight target) (accuracyScaleFactor q • target) :=
          hcollect.comp <|
            (measurable_const.add hweight).prodMk <|
              (measurable_const : Measurable fun _ : AmbientSpace q.n =>
                accuracyScaleFactor q).smul measurable_id
        convert Measurable.optionElim
          (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
        funext result
        cases result <;> rfl
      let good : Set (Option (ℝ × AmbientSpace q.n)) :=
        {result | ScheduledCollectedTotalPositive result}
      have hgood : MeasurableSet good :=
        measurableSet_scheduledCollectedTotalPositive
      change ∀ᵐ result ∂
          (scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
            properStride retryLimit current).bind tail,
        ScheduledCollectedTotalPositive result
      apply MeasureTheory.mem_ae_iff.mpr
      change ((scheduledBalancedAccuracyTransitionLawAux q I sigma2 proposalCap
        properStride retryLimit current).bind tail) goodᶜ = 0
      rw [Measure.bind_apply hgood.compl htail.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with result
      cases result with
      | none =>
          change (Measure.dirac
            (none : Option (ℝ × AmbientSpace q.n))) goodᶜ = 0
          rw [Measure.dirac_apply' _ hgood.compl]
          simp [good, ScheduledCollectedTotalPositive]
      | some target =>
          by_cases hsamples0 : samples = 0
          · subst samples
            change (Measure.dirac (some
              (total + weight target,
                (accuracyScaleFactor q)⁻¹ •
                  (accuracyScaleFactor q • target)))) goodᶜ = 0
            rw [Measure.dirac_apply' _ hgood.compl]
            simp [good, ScheduledCollectedTotalPositive,
              add_pos_of_nonneg_of_pos htotal (hweightPos target)]
          · exact MeasureTheory.mem_ae_iff.mp <|
              ih (Nat.pos_of_ne_zero hsamples0)
                (total + weight target) (accuracyScaleFactor q • target)
                (add_nonneg htotal (hweightPos target).le)

theorem gaussianRatioWeight_pos (sigma2 tau2 : ℝ)
    (x : AmbientSpace n) :
    0 < gaussianRatioWeight sigma2 tau2 x := by
  unfold gaussianRatioWeight
  positivity

theorem uniformRatioWeight_pos (sigma2 : ℝ) (x : AmbientSpace n) :
    0 < uniformRatioWeight sigma2 x := by
  unfold uniformRatioWeight
  positivity

theorem scheduledBalancedCoolingRatioTransitionLaw_ae_ratio_positive
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (tau2 : ℝ) (current : AmbientSpace q.n) :
    ∀ᵐ result ∂scheduledBalancedCoolingRatioTransitionLaw parameters q I
        sigma2 tau2 current,
      ScheduledCollectedTotalPositive result := by
  have hsamples : 0 < figureOnePhaseSampleCount q sigma2 := by
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  unfold scheduledBalancedCoolingRatioTransitionLaw
  apply (ae_map_iff
    (measurable_balancedCoolingAverage
      (n := q.n) (figureOnePhaseSampleCount q sigma2)).aemeasurable
    measurableSet_scheduledCollectedTotalPositive).2
  filter_upwards [scheduledBalancedTransitionCollectLaw_ae_total_positive
    q I hsigma2 (measurable_gaussianRatioWeight sigma2 tau2)
      (gaussianRatioWeight_pos sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2) hsamples 0
      (accuracyScaleFactor q • current) (by norm_num)] with result hresult
  cases result with
  | none => trivial
  | some result =>
      simpa [balancedCoolingAverage, ScheduledCollectedTotalPositive] using
        div_pos hresult (by exact_mod_cast hsamples)

theorem scheduledBalancedCoolingUniformTransitionLaw_ae_ratio_positive
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (current : AmbientSpace q.n) :
    ∀ᵐ result ∂scheduledBalancedCoolingUniformTransitionLaw parameters q I
        sigma2 current,
      ScheduledCollectedTotalPositive result := by
  have hsamples : 0 < figureOneSampleCount q := figureOneSampleCount_pos q
  unfold scheduledBalancedCoolingUniformTransitionLaw
  apply (ae_map_iff
    (measurable_balancedCoolingAverage
      (n := q.n) (figureOneSampleCount q)).aemeasurable
    measurableSet_scheduledCollectedTotalPositive).2
  filter_upwards [scheduledBalancedTransitionCollectLaw_ae_total_positive
    q I hsigma2 (measurable_uniformRatioWeight sigma2)
      (uniformRatioWeight_pos sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q) hsamples 0
      (accuracyScaleFactor q • current) (by norm_num)] with result hresult
  cases result with
  | none => trivial
  | some result =>
      simpa [balancedCoolingAverage, ScheduledCollectedTotalPositive] using
        div_pos hresult (by exact_mod_cast hsamples)

theorem scheduledBalancedTracePhaseObservationLaw_ae_total_positive
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    ∀ᵐ result ∂scheduledBalancedTracePhaseObservationLaw
        parameters q I phase trace,
      ScheduledCollectedTotalPositive result := by
  rcases trace with ⟨history, live⟩
  cases live with
  | false =>
      unfold scheduledBalancedTracePhaseObservationLaw
      apply (ae_dirac_iff measurableSet_scheduledCollectedTotalPositive).2
      trivial
  | true =>
      unfold scheduledBalancedTracePhaseObservationLaw
      simp only [if_true]
      split_ifs
      · exact scheduledBalancedCoolingRatioTransitionLaw_ae_ratio_positive
          parameters q I (scheduleValue_pos q phase)
            (scheduleValue q (phase + 1)) history.2.2.2
      · exact scheduledBalancedCoolingUniformTransitionLaw_ae_ratio_positive
          parameters q I (terminalVariance_pos' q) history.2.2.2

def BalancedCoolingHistoryHasPositiveCoordinates (m : ℕ) :
    Option (BalancedCoolingHistory n) → Prop
  | none => True
  | some history =>
      history.2.1 = m ∧ ∀ j, j < m → 0 < history.1 j

theorem measurableSet_balancedCoolingHistoryHasPositiveCoordinates
    (m : ℕ) :
    MeasurableSet {history : Option (BalancedCoolingHistory n) |
      BalancedCoolingHistoryHasPositiveCoordinates m history} := by
  let A : Set (BalancedCoolingHistory n) := {history |
    history.2.1 = m ∧ ∀ j, j < m → 0 < history.1 j}
  let B : Set (BalancedCoolingHistory n) :=
    ⋂ j ∈ Finset.range m, {history | 0 < history.1 j}
  have hB : MeasurableSet B := by
    dsimp only [B]
    apply Finset.measurableSet_biInter
    intro j hj
    exact measurableSet_lt measurable_const <|
      (measurable_pi_apply j).comp
        (measurable_fst : Measurable fun history : BalancedCoolingHistory n =>
          history.1)
  have hAB : A =
      {history : BalancedCoolingHistory n | history.2.1 = m} ∩ B := by
    ext history
    simp only [A, B, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter,
      Finset.mem_range]
  have hA : MeasurableSet A := by
    rw [hAB]
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter hB
  rw [show {history : Option (BalancedCoolingHistory n) |
      BalancedCoolingHistoryHasPositiveCoordinates m history} =
      {none} ∪ optionSomeEvent A by
    ext history
    cases history <;> simp [BalancedCoolingHistoryHasPositiveCoordinates,
      optionSomeEvent, A]]
  exact measurableSet_option_none.union (measurableSet_optionSomeEvent hA)

theorem BalancedCoolingHistoryHasPositiveCoordinates.snocTerminal
    {history : BalancedCoolingHistory n}
    (hcoordinates :
      BalancedCoolingHistoryHasPositiveCoordinates m (some history))
    {terminal : Option (ℝ × AmbientSpace n)}
    (hterminal : ScheduledCollectedTotalPositive terminal) :
    BalancedCoolingHistoryHasPositiveCoordinates (m + 1)
      (balancedCoolingHistorySnocTerminal history terminal) := by
  cases terminal with
  | none => trivial
  | some terminal =>
      simp only [BalancedCoolingHistoryHasPositiveCoordinates,
        balancedCoolingHistorySnocTerminal] at hcoordinates ⊢
      constructor
      · omega
      · intro j hj
        by_cases heq : j = history.2.1
        · change 0 < terminal.1 at hterminal
          simpa [heq] using hterminal
        · simp only [heq, if_false]
          exact hcoordinates.2 j (by omega)

/-- Dead traces are irrelevant to positivity; every coordinate stored by a
live trace is strictly positive. -/
def ScheduledBalancedCoolingTraceLiveCoordinatesPositive (m : ℕ)
    (trace : ScheduledBalancedCoolingTrace n) : Prop :=
  trace.2 = false ∨
    BalancedCoolingHistoryHasPositiveCoordinates m (some trace.1)

theorem measurableSet_scheduledBalancedCoolingTraceLiveCoordinatesPositive
    (m : ℕ) :
    MeasurableSet {trace : ScheduledBalancedCoolingTrace n |
      ScheduledBalancedCoolingTraceLiveCoordinatesPositive m trace} := by
  let dead : Set (ScheduledBalancedCoolingTrace n) :=
    {trace | trace.2 = false}
  let positive : Set (ScheduledBalancedCoolingTrace n) :=
    {trace | BalancedCoolingHistoryHasPositiveCoordinates m (some trace.1)}
  have hdead : MeasurableSet dead :=
    measurableSet_eq_fun measurable_snd measurable_const
  have hpositive : MeasurableSet positive :=
    (measurableSet_balancedCoolingHistoryHasPositiveCoordinates m).preimage
      (measurable_some.comp measurable_fst)
  change MeasurableSet (dead ∪ positive)
  exact hdead.union hpositive

theorem ScheduledBalancedCoolingTraceLiveCoordinatesPositive.append
    {trace : ScheduledBalancedCoolingTrace n}
    (hcoordinates :
      ScheduledBalancedCoolingTraceLiveCoordinatesPositive m trace)
    {result : Option (ℝ × AmbientSpace n)}
    (hresult : ScheduledCollectedTotalPositive result) :
    ScheduledBalancedCoolingTraceLiveCoordinatesPositive (m + 1)
      (scheduledBalancedCoolingTraceAppend trace result) := by
  rcases trace with ⟨history, live⟩
  cases live with
  | false =>
      cases result <;>
        simp [ScheduledBalancedCoolingTraceLiveCoordinatesPositive,
          scheduledBalancedCoolingTraceAppend]
  | true =>
      cases result with
      | none =>
          simp [ScheduledBalancedCoolingTraceLiveCoordinatesPositive,
            scheduledBalancedCoolingTraceAppend]
      | some result =>
          simp only [ScheduledBalancedCoolingTraceLiveCoordinatesPositive,
            scheduledBalancedCoolingTraceAppend, if_true,
            Bool.true_eq_false, false_or] at hcoordinates ⊢
          have h := hcoordinates.snocTerminal hresult
          rw [balancedCoolingHistorySnocTerminal_some] at h
          exact h

theorem scheduledBalancedTracePhaseKernel_ae_liveCoordinatesPositive
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase m : ℕ)
    (trace : ScheduledBalancedCoolingTrace q.n)
    (hcoordinates :
      ScheduledBalancedCoolingTraceLiveCoordinatesPositive m trace) :
    ∀ᵐ next ∂scheduledBalancedTracePhaseKernel parameters q I phase trace,
      ScheduledBalancedCoolingTraceLiveCoordinatesPositive (m + 1) next := by
  unfold scheduledBalancedTracePhaseKernel
  apply (ae_map_iff
    ((measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
    (measurableSet_scheduledBalancedCoolingTraceLiveCoordinatesPositive _)).2
  filter_upwards [
    scheduledBalancedTracePhaseObservationLaw_ae_total_positive
      parameters q I phase trace] with result hresult
  exact hcoordinates.append hresult

theorem scheduledBalancedForwardTraceLaw_ae_liveCoordinatesPositive
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) : ∀ phases,
    ∀ᵐ trace ∂scheduledBalancedForwardTraceLaw parameters q I phases,
      ScheduledBalancedCoolingTraceLiveCoordinatesPositive phases trace := by
  intro phases
  induction phases with
  | zero =>
      unfold scheduledBalancedForwardTraceLaw iteratedKernelLaw
      apply (ae_map_iff measurable_scheduledBalancedInitialTrace.aemeasurable
        (measurableSet_scheduledBalancedCoolingTraceLiveCoordinatesPositive 0)).2
      filter_upwards with point
      simp [ScheduledBalancedCoolingTraceLiveCoordinatesPositive,
        BalancedCoolingHistoryHasPositiveCoordinates,
        scheduledBalancedInitialTrace]
  | succ phases ih =>
      let prefixLaw :=
        scheduledBalancedForwardTraceLaw parameters q I phases
      let kernel := scheduledBalancedTracePhaseKernel parameters q I phases
      let good : Set (ScheduledBalancedCoolingTrace q.n) :=
        {trace | ScheduledBalancedCoolingTraceLiveCoordinatesPositive
          (phases + 1) trace}
      have hgood : MeasurableSet good :=
        measurableSet_scheduledBalancedCoolingTraceLiveCoordinatesPositive _
      have hkernel : Measurable kernel :=
        (scheduledBalancedTracePhaseKernel_measurable_and_probability
          parameters q I phases).1
      change ∀ᵐ trace ∂prefixLaw.bind kernel,
        ScheduledBalancedCoolingTraceLiveCoordinatesPositive
          (phases + 1) trace
      apply MeasureTheory.mem_ae_iff.mpr
      change (prefixLaw.bind kernel) goodᶜ = 0
      rw [Measure.bind_apply hgood.compl hkernel.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ih] with trace htrace
      exact MeasureTheory.mem_ae_iff.mp <|
        scheduledBalancedTracePhaseKernel_ae_liveCoordinatesPositive
          parameters q I phases phases trace htrace

/-- The ideal factor attached to the actual chronological phase is at most
two. -/
theorem figureOneChronologicalMomentFactor_le_two
    (q : VolumeParams) (j : ℕ) :
    figureOneChronologicalMomentFactor q j ≤ 2 :=
  figureOneIdealPhaseFactor_le_two q (figureOneChronologicalPhaseAt q j)

/-- Truncating at the actual mean can only decrease the second moment. -/
theorem scheduledFigureOneTrace_truncatedSecond_le_rawSecond
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hrawPos : 0 < scheduledFigureOneTraceRawMean q I j)
    (hWmem : MemLp (scheduledBalancedTracePhaseVariable q j) 2
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q))) :
    scheduledFigureOneTraceTruncatedSecond q I j ≤
      ∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q) := by
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let raw := scheduledFigureOneTraceRawMean q I j
  let alpha := figureOneDependentAlpha q
  let W := scheduledBalancedTracePhaseVariable q j
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  have halpha : 0 < alpha := figureOneDependentAlpha_pos q
  have hV0 : ∀ trace, 0 ≤ min (W trace) (alpha * raw) := by
    intro trace
    exact le_min (scheduledBalancedTracePhaseVariable_nonnegative q j trace)
      (mul_nonneg halpha.le hrawPos.le)
  have hVmem : MemLp (fun trace => min (W trace) (alpha * raw)) 2 mu := by
    apply MemLp.of_bound
      ((measurable_scheduledBalancedTracePhaseVariable q j).min
        measurable_const).aestronglyMeasurable
      (alpha * raw)
    filter_upwards with trace
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 trace)]
    exact min_le_right _ _
  change (∫ trace, min (W trace) (alpha * raw) ^ 2 ∂mu) ≤
    ∫ trace, W trace ^ 2 ∂mu
  apply integral_mono hVmem.integrable_sq hWmem.integrable_sq
  intro trace
  exact (sq_le_sq₀ (hV0 trace)
    (scheduledBalancedTracePhaseVariable_nonnegative q j trace)).2
      (min_le_left _ _)

/-- With the paper's sharp chronological second-moment factor, truncation at
`alpha * actualMean` loses at most the standard multiplicative
`1 + 1 / alpha`. -/
theorem scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hrawPos : 0 < scheduledFigureOneTraceRawMean q I j)
    (hWmem : MemLp (scheduledBalancedTracePhaseVariable q j) 2
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)))
    (hsecond :
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2) :
    scheduledFigureOneTraceRawMean q I j ≤
      (1 + 1 / figureOneDependentAlpha q) *
        scheduledFigureOneTraceTruncatedMean q I j := by
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let raw := scheduledFigureOneTraceRawMean q I j
  let alpha := figureOneDependentAlpha q
  let W := scheduledBalancedTracePhaseVariable q j
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  have halpha : (1024 : ℝ) ≤ alpha := figureOneDependentAlpha_ge_1024 q
  have hcap : 0 < alpha * raw := mul_pos (by linarith) hrawPos
  have htrunc := integral_min_ge_integral_sub_secondMoment_div_four mu
    (hWmem.integrable (by norm_num)) hWmem.integrable_sq
    (scheduledBalancedTracePhaseVariable_nonnegative q j) hcap
  have hfactor : figureOneChronologicalMomentFactor q j ≤ 2 :=
    figureOneChronologicalMomentFactor_le_two q j
  have hsecondTwo : (∫ trace, W trace ^ 2 ∂mu) ≤ 2 * raw ^ 2 :=
    hsecond.trans (mul_le_mul_of_nonneg_right hfactor (sq_nonneg raw))
  have hloss : (∫ trace, W trace ^ 2 ∂mu) / (4 * (alpha * raw)) ≤
      raw / (2 * alpha) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hcap)]
    field_simp [show alpha ≠ 0 by linarith]
    nlinarith [hsecondTwo]
  have hmeanLower : (1 - 1 / (2 * alpha)) * raw ≤
      scheduledFigureOneTraceTruncatedMean q I j := by
    change (∫ trace, min (W trace) (alpha * raw) ∂mu) ≥
      raw - (∫ trace, W trace ^ 2 ∂mu) / (4 * (alpha * raw)) at htrunc
    change (1 - 1 / (2 * alpha)) * raw ≤
      ∫ trace, min (W trace) (alpha * raw) ∂mu
    calc
      (1 - 1 / (2 * alpha)) * raw = raw - raw / (2 * alpha) := by ring
      _ ≤ raw - (∫ trace, W trace ^ 2 ∂mu) / (4 * (alpha * raw)) :=
        sub_le_sub_left hloss raw
      _ ≤ _ := htrunc
  have hinv0 : 0 ≤ 1 / alpha := by positivity
  have hinv1 : 1 / alpha ≤ 1 :=
    (div_le_one (by linarith : 0 < alpha)).2 (by linarith)
  have hcoefficient : 1 ≤
      (1 + 1 / alpha) * (1 - 1 / (2 * alpha)) := by
    rw [show (1 + 1 / alpha) * (1 - 1 / (2 * alpha)) =
      1 + (1 / alpha) * (1 - 1 / alpha) / 2 by ring]
    nlinarith [mul_nonneg hinv0 (sub_nonneg.mpr hinv1)]
  have hscale := mul_le_mul_of_nonneg_left hmeanLower
    (by positivity : 0 ≤ 1 + 1 / alpha)
  change raw ≤ (1 + 1 / alpha) *
    scheduledFigureOneTraceTruncatedMean q I j
  calc
    raw = 1 * raw := by ring
    _ ≤ ((1 + 1 / alpha) * (1 - 1 / (2 * alpha))) * raw :=
      mul_le_mul_of_nonneg_right hcoefficient hrawPos.le
    _ = (1 + 1 / alpha) * ((1 - 1 / (2 * alpha)) * raw) := by ring
    _ ≤ _ := hscale

/-! ## Finite products with actual executable means -/

theorem scheduledFigureOneTraceTruncatedMean_nonnegative
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hraw0 : 0 ≤ scheduledFigureOneTraceRawMean q I j) :
    0 ≤ scheduledFigureOneTraceTruncatedMean q I j := by
  apply integral_nonneg
  intro trace
  unfold scheduledFigureOneTraceTruncatedPhase dependentTruncatedPhase
  exact le_min (scheduledBalancedTracePhaseVariable_nonnegative q j trace)
    (mul_nonneg (figureOneDependentAlpha_pos q).le hraw0)

/-- The product of actual raw means loses at most the same truncation factor
as in Lemma 7.14. -/
theorem scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct
    (q : VolumeParams) (I : VolumeInput q.n)
    (hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I) i ≤
      (1 + 1 / figureOneDependentAlpha q) ^ i *
        dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i := by
  unfold dependentPhaseMeanProduct
  calc
    (∏ j ∈ Finset.range i, scheduledFigureOneTraceRawMean q I (j + 1)) ≤
        ∏ j ∈ Finset.range i,
          ((1 + 1 / figureOneDependentAlpha q) *
            scheduledFigureOneTraceTruncatedMean q I (j + 1)) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact (hrawPos (j + 1) (by omega) (by
          have := Finset.mem_range.mp hj
          omega)).le
      · intro j hj
        have hjm : j + 1 ≤ figureOneDependentPhaseCount q := by
          have := Finset.mem_range.mp hj
          omega
        exact
          scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean
            q I (j + 1) (hrawPos (j + 1) (by omega) hjm)
            (memLp_scheduledBalancedForwardTrace_phaseVariable
              q I (j + 1) (by omega) hjm)
            (hsecond (j + 1) (by omega) hjm)
    _ = (1 + 1 / figureOneDependentAlpha q) ^ i *
        ∏ j ∈ Finset.range i,
          scheduledFigureOneTraceTruncatedMean q I (j + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Truncated executable second moments are bounded by the product of the
chronological paper factors and the square of the actual raw-mean product. -/
theorem scheduledFigureOneTrace_truncatedSecondProduct_le_factor_mul_rawMeanProduct_sq
    (q : VolumeParams) (I : VolumeInput q.n)
    (hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedSecond q I) i ≤
      dependentPhaseMeanProduct (figureOneChronologicalMomentFactor q) i *
        dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I) i ^ 2 := by
  unfold dependentPhaseMeanProduct
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro j hj
    exact integral_nonneg fun _ => sq_nonneg _
  · intro j hj
    have hjm : j + 1 ≤ figureOneDependentPhaseCount q := by
      have := Finset.mem_range.mp hj
      omega
    exact (scheduledFigureOneTrace_truncatedSecond_le_rawSecond
      q I (j + 1) (hrawPos (j + 1) (by omega) hjm)
      (memLp_scheduledBalancedForwardTrace_phaseVariable
        q I (j + 1) (by omega) hjm)).trans
          (hsecond (j + 1) (by omega) hjm)

/-- The sharp one-phase executable estimates imply the product second-moment
bound used by both finite CV18 product obligations. -/
theorem scheduledFigureOneTrace_truncatedSecondProduct_le_one_add_eps_sq_div_32
    (q : VolumeParams) (I : VolumeInput q.n)
    (hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedSecond q I) i ≤
      (1 + q.eps ^ 2 / 32) *
        dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i ^ 2 := by
  let meanProduct := dependentPhaseMeanProduct
    (scheduledFigureOneTraceTruncatedMean q I) i
  let rawProduct := dependentPhaseMeanProduct
    (scheduledFigureOneTraceRawMean q I) i
  let factorProduct := dependentPhaseMeanProduct
    (figureOneChronologicalMomentFactor q) i
  have hmean0 : 0 ≤ meanProduct :=
    dependentPhaseMeanProduct_nonneg _ (fun j =>
      scheduledFigureOneTraceTruncatedMean_nonnegative q I j <|
        if hj1 : 1 ≤ j then
          if hjm : j ≤ figureOneDependentPhaseCount q then
            (hrawPos j hj1 hjm).le
          else by
            unfold scheduledFigureOneTraceRawMean
            exact integral_nonneg fun trace =>
              scheduledBalancedTracePhaseVariable_nonnegative q j trace
        else by
          unfold scheduledFigureOneTraceRawMean
          exact integral_nonneg fun trace =>
            scheduledBalancedTracePhaseVariable_nonnegative q j trace) i
  have hraw0 : 0 ≤ rawProduct :=
    dependentPhaseMeanProduct_nonneg _ (fun j => by
      unfold scheduledFigureOneTraceRawMean
      exact integral_nonneg fun trace =>
        scheduledBalancedTracePhaseVariable_nonnegative q j trace) i
  have hfactor0 : 0 ≤ factorProduct :=
    dependentPhaseMeanProduct_nonneg _ (fun j =>
      zero_le_one.trans (figureOneChronologicalMomentFactor_one_le q j)) i
  have hraw :=
    scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct
      q I hrawPos hsecond hi
  have hpow := figureOne_one_add_inv_alpha_pow_le_exp q hi
  have hrawExp : rawProduct ≤
      Real.exp (q.eps ^ 2 / 1024) * meanProduct :=
    hraw.trans (mul_le_mul_of_nonneg_right hpow hmean0)
  have hrawSq : rawProduct ^ 2 ≤
      Real.exp (q.eps ^ 2 / 1024) ^ 2 * meanProduct ^ 2 := by
    have := (sq_le_sq₀ hraw0
      (mul_nonneg (Real.exp_pos _).le hmean0)).2 hrawExp
    nlinarith
  have hsecondProduct :=
    scheduledFigureOneTrace_truncatedSecondProduct_le_factor_mul_rawMeanProduct_sq
      q I hrawPos hsecond hi
  have hfactor :=
    figureOneChronologicalMomentFactor_partialProduct_le_exp q hi
  have hbound : factorProduct * rawProduct ^ 2 ≤
      Real.exp (13 * q.eps ^ 2 / 512) *
        (Real.exp (q.eps ^ 2 / 1024) ^ 2 * meanProduct ^ 2) :=
    mul_le_mul hfactor hrawSq (sq_nonneg rawProduct) (Real.exp_pos _).le
  have hexpIdentity :
      Real.exp (13 * q.eps ^ 2 / 512) *
          Real.exp (q.eps ^ 2 / 1024) ^ 2 =
        Real.exp (7 * q.eps ^ 2 / 256) := by
    rw [show Real.exp (q.eps ^ 2 / 1024) ^ 2 =
      Real.exp (2 * (q.eps ^ 2 / 1024)) by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring,
      ← Real.exp_add]
    congr 1
    ring
  calc
    dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        factorProduct * rawProduct ^ 2 := hsecondProduct
    _ ≤ Real.exp (13 * q.eps ^ 2 / 512) *
        (Real.exp (q.eps ^ 2 / 1024) ^ 2 * meanProduct ^ 2) := hbound
    _ = Real.exp (7 * q.eps ^ 2 / 256) * meanProduct ^ 2 := by
      rw [← mul_assoc, hexpIdentity]
    _ ≤ (1 + q.eps ^ 2 / 32) * meanProduct ^ 2 :=
      mul_le_mul_of_nonneg_right
        (figureOne_exp_seven_eps_sq_div_256_le q) (sq_nonneg meanProduct)

/-- The sharp phasewise moments discharge the complete finite-prefix
relative-product premise of the executable capstone. -/
theorem scheduledFigureOneTrace_relativeProduct_finite_of_sharp_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2) :
    ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        2 * dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i ^ 2 := by
  intro i hi
  let meanProduct := dependentPhaseMeanProduct
    (scheduledFigureOneTraceTruncatedMean q I) i
  have hmeanSq0 : 0 ≤ meanProduct ^ 2 := sq_nonneg _
  have hsecondProduct :=
    scheduledFigureOneTrace_truncatedSecondProduct_le_one_add_eps_sq_div_32
      q I hrawPos hsecond hi
  have hmult := figureOneDependentMomentMultiplier_le q hi
  have hmult0 : 0 ≤ 1 + 2 * figureOneDependentEpsilon q *
      figureOneDependentAlpha q ^ 4 * (i : ℝ) := by
    have hterm : 0 ≤ 2 * figureOneDependentEpsilon q *
        figureOneDependentAlpha q ^ 4 * (i : ℝ) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num)
          (figureOneDependentEpsilon_nonneg q)) (by positivity))
        (by positivity)
    linarith
  calc
    _ ≤ (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
        ((1 + q.eps ^ 2 / 32) * meanProduct ^ 2) :=
      mul_le_mul_of_nonneg_left hsecondProduct hmult0
    _ ≤ ((1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32)) *
        meanProduct ^ 2 := by
      have hscaled := mul_le_mul_of_nonneg_right hmult
        (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
      nlinarith
    _ ≤ (1 + q.eps ^ 2 / 16) * meanProduct ^ 2 :=
      mul_le_mul_of_nonneg_right (figureOneDependentMomentBudget_le q)
        hmeanSq0
    _ ≤ 2 * meanProduct ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hmeanSq0
      nlinarith [q.heps.1, q.heps.2]

/-- The same phasewise estimate discharges the final sharper second-product
tail premise. -/
theorem scheduledFigureOneTrace_tailSecond_of_sharp_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2) :
    (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I)
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 16) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I)
            (figureOneDependentPhaseCount q) ^ 2 := by
  let meanProduct := dependentPhaseMeanProduct
    (scheduledFigureOneTraceTruncatedMean q I)
      (figureOneDependentPhaseCount q)
  have hmeanSq0 : 0 ≤ meanProduct ^ 2 := sq_nonneg _
  have hsecondProduct :=
    scheduledFigureOneTrace_truncatedSecondProduct_le_one_add_eps_sq_div_32
      q I hrawPos hsecond (le_refl _)
  have hmult := figureOneDependentMomentMultiplier_le q (le_refl _)
  have hmult0 : 0 ≤ 1 + 2 * figureOneDependentEpsilon q *
      figureOneDependentAlpha q ^ 4 *
        (figureOneDependentPhaseCount q : ℝ) := by
    have hterm : 0 ≤ 2 * figureOneDependentEpsilon q *
        figureOneDependentAlpha q ^ 4 *
          (figureOneDependentPhaseCount q : ℝ) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num)
          (figureOneDependentEpsilon_nonneg q)) (by positivity))
        (by positivity)
    linarith
  calc
    _ ≤ (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
        ((1 + q.eps ^ 2 / 32) * meanProduct ^ 2) :=
      mul_le_mul_of_nonneg_left hsecondProduct hmult0
    _ ≤ ((1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32)) *
        meanProduct ^ 2 := by
      have hscaled := mul_le_mul_of_nonneg_right hmult
        (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
      nlinarith
    _ ≤ (1 + q.eps ^ 2 / 16) * meanProduct ^ 2 :=
      mul_le_mul_of_nonneg_right (figureOneDependentMomentBudget_le q)
        hmeanSq0

/-- Actual-mean truncation decreases each phase mean. -/
theorem scheduledFigureOneTrace_truncatedMeanProduct_le_rawMeanProduct
    (q : VolumeParams) (I : VolumeInput q.n)
    (hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedMean q I) i ≤
      dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I) i := by
  let _ : IsProbabilityMeasure
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  unfold dependentPhaseMeanProduct
  apply Finset.prod_le_prod
  · intro j hj
    apply scheduledFigureOneTraceTruncatedMean_nonnegative q I (j + 1)
    exact (hrawPos (j + 1) (by omega) (by
      have := Finset.mem_range.mp hj
      omega)).le
  · intro j hj
    let mu := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)
    let W := scheduledBalancedTracePhaseVariable q (j + 1)
    have hjm : j + 1 ≤ figureOneDependentPhaseCount q := by
      have := Finset.mem_range.mp hj
      omega
    have hraw := hrawPos (j + 1) (by omega) hjm
    have hVmem : MemLp
        (scheduledFigureOneTraceTruncatedPhase q I (j + 1)) 2 mu := by
      apply MemLp.of_bound
        ((measurable_scheduledBalancedTracePhaseVariable q (j + 1)).min
          measurable_const).aestronglyMeasurable
        (figureOneDependentAlpha q *
          scheduledFigureOneTraceRawMean q I (j + 1))
      filter_upwards with trace
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact min_le_right _ _
      · exact le_min
          (scheduledBalancedTracePhaseVariable_nonnegative q (j + 1) trace)
          (mul_nonneg (figureOneDependentAlpha_pos q).le hraw.le)
    unfold scheduledFigureOneTraceTruncatedMean
      scheduledFigureOneTraceRawMean
    apply integral_mono (hVmem.integrable (by norm_num))
      ((memLp_scheduledBalancedForwardTrace_phaseVariable
        q I (j + 1) (by omega) hjm).integrable (by norm_num))
    intro trace
    exact min_le_left _ _

/-- If the product of actual raw means is within `eps/64` of the telescoping
ideal center, Lemma 7.14's truncation loss upgrades this to the capstone's
`eps/32` comparison. -/
theorem scheduledFigureOneTrace_truncatedMeanProduct_relativeApprox_ideal
    (q : VolumeParams) (I : VolumeInput q.n)
    (hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2)
    (hrawApprox : RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q))) :
    RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q)) := by
  let ideal := ∏ phase, figureOneIdealPhaseMean q I phase
  let raw := dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
    (figureOneDependentPhaseCount q)
  let truncated := dependentPhaseMeanProduct
    (scheduledFigureOneTraceTruncatedMean q I)
      (figureOneDependentPhaseCount q)
  have hidealPos : 0 < ideal := Finset.prod_pos fun phase _ =>
    figureOneIdealPhaseMean_pos q I phase
  have htruncated0 : 0 ≤ truncated :=
    dependentPhaseMeanProduct_nonneg _ (fun j =>
      scheduledFigureOneTraceTruncatedMean_nonnegative q I j <| by
        unfold scheduledFigureOneTraceRawMean
        exact integral_nonneg fun trace =>
          scheduledBalancedTracePhaseVariable_nonnegative q j trace) _
  have htruncatedRaw : truncated ≤ raw :=
    scheduledFigureOneTrace_truncatedMeanProduct_le_rawMeanProduct
      q I hrawPos (le_refl _)
  have hrawPow :=
    scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct
      q I hrawPos hsecond (le_refl _)
  have hpow := figureOne_one_add_inv_alpha_pow_le_exp q (le_refl _)
  have hrawExp : raw ≤ Real.exp (q.eps ^ 2 / 1024) * truncated :=
    hrawPow.trans (mul_le_mul_of_nonneg_right hpow htruncated0)
  have hrawBound : raw ≤ (1 + q.eps ^ 2 / 512) * truncated :=
    hrawExp.trans (mul_le_mul_of_nonneg_right
      (figureOne_exp_eps_sq_div_1024_le q) htruncated0)
  unfold RelativeApprox Arlib.relErr at hrawApprox ⊢
  change (1 - q.eps / 64) * ideal ≤ raw ∧
      raw ≤ (1 + q.eps / 64) * ideal at hrawApprox
  change (1 - q.eps / 32) * ideal ≤ truncated ∧
      truncated ≤ (1 + q.eps / 32) * ideal
  constructor
  · have hcoeff :
        (1 + q.eps ^ 2 / 512) * (1 - q.eps / 32) ≤
          1 - q.eps / 64 := by
      nlinarith [q.heps.1, q.heps.2,
        mul_nonneg q.heps.1.le (sub_nonneg.mpr q.heps.2.le)]
    have hscaled : (1 + q.eps ^ 2 / 512) *
        ((1 - q.eps / 32) * ideal) ≤
          (1 + q.eps ^ 2 / 512) * truncated := by
      calc
        _ = ((1 + q.eps ^ 2 / 512) * (1 - q.eps / 32)) * ideal := by ring
        _ ≤ (1 - q.eps / 64) * ideal :=
          mul_le_mul_of_nonneg_right hcoeff hidealPos.le
        _ ≤ raw := hrawApprox.1
        _ ≤ _ := hrawBound
    exact le_of_mul_le_mul_left hscaled (by positivity)
  · calc
      truncated ≤ raw := htruncatedRaw
      _ ≤ (1 + q.eps / 64) * ideal := hrawApprox.2
      _ ≤ (1 + q.eps / 32) * ideal := by
        apply mul_le_mul_of_nonneg_right _ hidealPos.le
        linarith [q.heps.1]

/-! ## Executable capstone with the product algebra discharged -/

/-- The unconditional scheduled capstone now needs only the sharp phasewise
second moments, the raw-mean product bias, and Lemma 7.17(c)'s approximate
independence.  All support, `L²`, truncation, and finite-product algebra is
proved above. -/
theorem figureOneFinalScheduledBalancedBase_failure_le_of_sharp_trace_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrawApprox : RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledBalancedBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  apply figureOneFinalScheduledBalancedBase_failure_le_of_trace_raw_moments
    q I oracle hrounded
  · intro j hj1 hjm
    exact memLp_scheduledBalancedForwardTrace_phaseVariable q I j hj1 hjm
  · exact hrawPos
  · intro j hj1 hjm
    calc
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
          ∂scheduledBalancedForwardTraceLaw
            figureOneFinalScheduledBalancedParameters q I
            (figureOneDependentPhaseCount q)) ≤
          figureOneChronologicalMomentFactor q j *
            scheduledFigureOneTraceRawMean q I j ^ 2 :=
        hsecond j hj1 hjm
      _ ≤ 2 * scheduledFigureOneTraceRawMean q I j ^ 2 :=
        mul_le_mul_of_nonneg_right
          (figureOneChronologicalMomentFactor_le_two q j) (sq_nonneg _)
      _ ≤ 4 * scheduledFigureOneTraceRawMean q I j ^ 2 := by
        nlinarith [sq_nonneg (scheduledFigureOneTraceRawMean q I j)]
  · exact hind
  · exact scheduledFigureOneTrace_relativeProduct_finite_of_sharp_moments
      q I hrawPos hsecond
  · exact scheduledFigureOneTrace_tailSecond_of_sharp_moments
      q I hrawPos hsecond
  · exact scheduledFigureOneTrace_truncatedMeanProduct_relativeApprox_ideal
      q I hrawPos hsecond hrawApprox

#print axioms figureOneChronologicalMomentFactor_le_two
#print axioms scheduledBalancedTransitionCollectLaw_ae_total_positive
#print axioms gaussianRatioWeight_pos
#print axioms uniformRatioWeight_pos
#print axioms scheduledBalancedCoolingRatioTransitionLaw_ae_ratio_positive
#print axioms scheduledBalancedCoolingUniformTransitionLaw_ae_ratio_positive
#print axioms scheduledBalancedTracePhaseObservationLaw_ae_total_positive
#print axioms scheduledBalancedForwardTraceLaw_ae_liveCoordinatesPositive
#print axioms scheduledFigureOneTrace_truncatedSecond_le_rawSecond
#print axioms scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean
#print axioms scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct
#print axioms scheduledFigureOneTrace_truncatedSecondProduct_le_factor_mul_rawMeanProduct_sq
#print axioms scheduledFigureOneTrace_truncatedSecondProduct_le_one_add_eps_sq_div_32
#print axioms scheduledFigureOneTrace_relativeProduct_finite_of_sharp_moments
#print axioms scheduledFigureOneTrace_tailSecond_of_sharp_moments
#print axioms scheduledFigureOneTrace_truncatedMeanProduct_relativeApprox_ideal
#print axioms figureOneFinalScheduledBalancedBase_failure_le_of_sharp_trace_moments

end ArlibCommunity.Algorithms.CV18
