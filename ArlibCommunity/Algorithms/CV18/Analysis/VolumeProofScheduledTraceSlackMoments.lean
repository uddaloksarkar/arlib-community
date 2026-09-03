/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceLemma717Capstone

/-!
# Slack moment interface for the executable scheduled trace

The paper's product calculation does not require the finite walk to attain
the ideal IID second-moment factor phase by phase.  A coarse local factor
`2` controls truncation bias, while the sharp information can be supplied as
one finite-prefix product bound.  This is the form naturally produced by a
paired/Markov phase analysis with small explicit slack.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The truncation-loss estimate only uses the coarse bound
`E[W²] ≤ 2 E[W]²`; it does not require the exact ideal phase factor. -/
theorem scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean_of_two
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
        2 * scheduledFigureOneTraceRawMean q I j ^ 2) :
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
  have hloss : (∫ trace, W trace ^ 2 ∂mu) / (4 * (alpha * raw)) ≤
      raw / (2 * alpha) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hcap)]
    field_simp [show alpha ≠ 0 by linarith]
    nlinarith [hsecond]
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

/-- Finite product form of the coarse truncation-loss estimate. -/
theorem scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct_of_two
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsecondTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2)
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
        exact (scheduledFigureOneTraceRawMean_pos q I (j + 1) (by omega)
          (by have := Finset.mem_range.mp hj; omega)).le
      · intro j hj
        have hjm : j + 1 ≤ figureOneDependentPhaseCount q := by
          have := Finset.mem_range.mp hj
          omega
        exact
          scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean_of_two
            q I (j + 1)
            (scheduledFigureOneTraceRawMean_pos q I (j + 1) (by omega) hjm)
            (memLp_scheduledBalancedForwardTrace_phaseVariable
              q I (j + 1) (by omega) hjm)
            (hsecondTwo (j + 1) (by omega) hjm)
    _ = (1 + 1 / figureOneDependentAlpha q) ^ i *
        ∏ j ∈ Finset.range i,
          scheduledFigureOneTraceTruncatedMean q I (j + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- A phase-factor version of the empirical-average calculation in CV18
Lemma 7.15, Eq. (6).  It keeps the executable phase factors abstract so the
finite-walk collector estimate can include its explicit mixing slack. -/
theorem scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor
    (q : VolumeParams) (I : VolumeInput q.n) (factor : ℕ → ℝ)
    (hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        factor j * scheduledFigureOneTraceRawMean q I j ^ 2)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedSecond q I) i ≤
      dependentPhaseMeanProduct factor i *
        dependentPhaseMeanProduct
          (scheduledFigureOneTraceRawMean q I) i ^ 2 := by
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

/-- The exact finite-prefix budget needed after the phasewise empirical
second-moment estimate.  This isolates the chunk-product arithmetic in the
middle of CV18 Lemma 7.15 from the Markov-chain collector proof. -/
theorem scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor_budget
    (q : VolumeParams) (I : VolumeInput q.n) (factor : ℕ → ℝ)
    (hfactor0 : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 ≤ factor j)
    (hsecondTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hsecondFactor : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        factor j * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hbudget : ∀ i, i ≤ figureOneDependentPhaseCount q →
      dependentPhaseMeanProduct factor i *
          ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2 ≤
        1 + q.eps ^ 2 / 32) :
    ∀ i, i ≤ figureOneDependentPhaseCount q →
      dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        (1 + q.eps ^ 2 / 32) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I) i ^ 2 := by
  intro i hi
  let raw := dependentPhaseMeanProduct
    (scheduledFigureOneTraceRawMean q I) i
  let truncated := dependentPhaseMeanProduct
    (scheduledFigureOneTraceTruncatedMean q I) i
  let factorProduct := dependentPhaseMeanProduct factor i
  have hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j :=
    fun j hj1 hjm => scheduledFigureOneTraceRawMean_pos q I j hj1 hjm
  have hfactorProduct0 : 0 ≤ factorProduct := by
    dsimp only [factorProduct, dependentPhaseMeanProduct]
    apply Finset.prod_nonneg
    intro j hj
    exact hfactor0 (j + 1) (by omega) (by
      have := Finset.mem_range.mp hj
      omega)
  have htruncated0 : 0 ≤ truncated :=
    dependentPhaseMeanProduct_nonneg _ (fun j =>
      scheduledFigureOneTraceTruncatedMean_nonnegative q I j <| by
        unfold scheduledFigureOneTraceRawMean
        exact integral_nonneg fun trace =>
          scheduledBalancedTracePhaseVariable_nonnegative q j trace) i
  have hraw0 : 0 ≤ raw :=
    dependentPhaseMeanProduct_nonneg _ (fun j => by
      unfold scheduledFigureOneTraceRawMean
      exact integral_nonneg fun trace =>
        scheduledBalancedTracePhaseVariable_nonnegative q j trace) i
  have hraw :=
    scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct_of_two
      q I hsecondTwo hi
  have hcoefficient0 :
      0 ≤ (1 + 1 / figureOneDependentAlpha q) ^ i := by
    apply pow_nonneg
    have halpha := figureOneDependentAlpha_pos q
    have hinv : 0 ≤ 1 / figureOneDependentAlpha q :=
      (one_div_pos.mpr halpha).le
    linarith
  have hrawSq : raw ^ 2 ≤
      (((1 + 1 / figureOneDependentAlpha q) ^ i) * truncated) ^ 2 :=
    (sq_le_sq₀ hraw0
      (mul_nonneg hcoefficient0 htruncated0)).2 hraw
  have hsecondProduct :=
    scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor
      q I factor hrawPos hsecondFactor hi
  calc
    dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        factorProduct * raw ^ 2 := hsecondProduct
    _ ≤ factorProduct *
        (((1 + 1 / figureOneDependentAlpha q) ^ i) * truncated) ^ 2 :=
      mul_le_mul_of_nonneg_left hrawSq hfactorProduct0
    _ = (factorProduct *
          ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2) *
        truncated ^ 2 := by ring
    _ ≤ (1 + q.eps ^ 2 / 32) * truncated ^ 2 :=
      mul_le_mul_of_nonneg_right (hbudget i hi) (sq_nonneg truncated)

/-- A coarse local second moment is enough to turn raw-product bias into the
truncated-product bias consumed by Lemma 7.15. -/
theorem scheduledFigureOneTrace_truncatedMeanProduct_relativeApprox_ideal_of_two
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsecondTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2)
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
  have hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j :=
    fun j hj1 hjm => scheduledFigureOneTraceRawMean_pos q I j hj1 hjm
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
    scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct_of_two
      q I hsecondTwo (le_refl _)
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

/-- Paper-faithful aborting accuracy with local truncation bias and global
second-product concentration separated.  This is the finite-walk slack form
of the remaining moment contract. -/
theorem figureOneFinalScheduledAbortBase_failure_le_of_slack_trace_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hsecondTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hproductSecond : ∀ i, i ≤ figureOneDependentPhaseCount q →
      dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        (1 + q.eps ^ 2 / 32) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I) i ^ 2)
    (hrawApprox : RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  apply figureOneFinalScheduledAbortBase_failure_le_of_directPostInitial q I oracle
  apply figureOnePostInitialDirectFailureBoundFor_of_trace_raw_moments
    q I oracle hrounded
  · intro j hj1 hjm
    exact memLp_scheduledBalancedForwardTrace_phaseVariable q I j hj1 hjm
  · intro j hj1 hjm
    exact scheduledFigureOneTraceRawMean_pos q I j hj1 hjm
  · intro j hj1 hjm
    exact (hsecondTwo j hj1 hjm).trans <| by
      gcongr
      norm_num
  · exact figureOneScheduledTrace_lemma717c q I
  · intro i hi
    let meanProduct := dependentPhaseMeanProduct
      (scheduledFigureOneTraceTruncatedMean q I) i
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
        mul_le_mul_of_nonneg_left (hproductSecond i hi) hmult0
      _ ≤ ((1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32)) *
          meanProduct ^ 2 := by
        have hscaled := mul_le_mul_of_nonneg_right hmult
          (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
        nlinarith
      _ ≤ (1 + q.eps ^ 2 / 16) * meanProduct ^ 2 :=
        mul_le_mul_of_nonneg_right (figureOneDependentMomentBudget_le q)
          (sq_nonneg meanProduct)
      _ ≤ 2 * meanProduct ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg meanProduct)
        nlinarith [q.heps.1, q.heps.2]
  · let meanProduct := dependentPhaseMeanProduct
      (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q)
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
        mul_le_mul_of_nonneg_left
          (hproductSecond _ (le_refl _)) hmult0
      _ ≤ ((1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32)) *
          meanProduct ^ 2 := by
        have hscaled := mul_le_mul_of_nonneg_right hmult
          (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
        nlinarith
      _ ≤ (1 + q.eps ^ 2 / 16) * meanProduct ^ 2 :=
        mul_le_mul_of_nonneg_right (figureOneDependentMomentBudget_le q)
          (sq_nonneg meanProduct)
  · exact scheduledFigureOneTrace_truncatedMeanProduct_relativeApprox_ideal_of_two
      q I hsecondTwo hrawApprox

/-- Final executable accuracy in the precise factor language of CV18
Lemma 7.15, Eq. (6): the analytic collector proof supplies one phase factor,
and the paper's chunk calculation supplies its finite-prefix budget. -/
theorem figureOneFinalScheduledAbortBase_failure_le_of_phase_factor_budget
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (factor : ℕ → ℝ)
    (hfactor0 : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 ≤ factor j)
    (hfactorTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      factor j ≤ 2)
    (hsecondFactor : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        factor j * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hbudget : ∀ i, i ≤ figureOneDependentPhaseCount q →
      dependentPhaseMeanProduct factor i *
          ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2 ≤
        1 + q.eps ^ 2 / 32)
    (hrawApprox : RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  have hsecondTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2 := by
    intro j hj1 hjm
    exact (hsecondFactor j hj1 hjm).trans <|
      mul_le_mul_of_nonneg_right (hfactorTwo j hj1 hjm) (sq_nonneg _)
  apply figureOneFinalScheduledAbortBase_failure_le_of_slack_trace_moments
    q I oracle hrounded hsecondTwo
  · exact
      scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor_budget
        q I factor hfactor0 hsecondTwo hsecondFactor hbudget
  · exact hrawApprox

#print axioms
  scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean_of_two
#print axioms
  scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct_of_two
#print axioms
  scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor
#print axioms
  scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor_budget
#print axioms
  scheduledFigureOneTrace_truncatedMeanProduct_relativeApprox_ideal_of_two
#print axioms
  figureOneFinalScheduledAbortBase_failure_le_of_slack_trace_moments
#print axioms
  figureOneFinalScheduledAbortBase_failure_le_of_phase_factor_budget

end ArlibCommunity.Algorithms.CV18
