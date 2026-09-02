/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependence

/-!
# The dependent-product recurrence in CV18 Lemma 7.15

This module formalizes the recursive truncations used after Lemma 7.17(c).
With the paper's one-based indexing, `dependentPhaseMeanProduct mean i` is
`E(V₁) * ... * E(Vᵢ)` and `dependentTruncatedProduct alpha mean V i` is `Uᵢ`.
The definitions are kept model-independent so that the recurrence can be
instantiated directly on the complete history law of the executable walk.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The deterministic product `E(V₁) * ... * E(Vᵢ)` in CV18 Lemma 7.15. -/
def dependentPhaseMeanProduct (mean : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range i, mean (j + 1)

@[simp]
theorem dependentPhaseMeanProduct_zero (mean : ℕ → ℝ) :
    dependentPhaseMeanProduct mean 0 = 1 := by
  simp [dependentPhaseMeanProduct]

theorem dependentPhaseMeanProduct_succ (mean : ℕ → ℝ) (i : ℕ) :
    dependentPhaseMeanProduct mean (i + 1) =
      dependentPhaseMeanProduct mean i * mean (i + 1) := by
  simp [dependentPhaseMeanProduct, Finset.prod_range_succ]

theorem dependentPhaseMeanProduct_nonneg (mean : ℕ → ℝ)
    (hmean : ∀ j, 0 ≤ mean j) (i : ℕ) :
    0 ≤ dependentPhaseMeanProduct mean i := by
  exact Finset.prod_nonneg fun j _ => hmean (j + 1)

/-- The recursively truncated accumulated product `Uᵢ` from CV18 Lemma 7.15.
The phase variables `V` use the paper's one-based indexing. -/
def dependentTruncatedProduct (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) : ℕ → Omega → ℝ
  | 0 => fun _ => 1
  | i + 1 => fun omega =>
      min (dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega)
        (alpha * dependentPhaseMeanProduct mean (i + 1))

@[simp]
theorem dependentTruncatedProduct_zero (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (omega : Omega) :
    dependentTruncatedProduct alpha mean V 0 omega = 1 := by
  rfl

theorem dependentTruncatedProduct_succ (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (i : ℕ) (omega : Omega) :
    dependentTruncatedProduct alpha mean V (i + 1) omega =
      min (dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega)
        (alpha * dependentPhaseMeanProduct mean (i + 1)) := by
  rfl

theorem measurable_dependentTruncatedProduct (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (hV : ∀ j, Measurable (V j)) :
    ∀ i, Measurable (dependentTruncatedProduct alpha mean V i)
  | 0 => measurable_const
  | i + 1 =>
      ((measurable_dependentTruncatedProduct alpha mean V hV i).mul
        (hV (i + 1))).min measurable_const

theorem dependentTruncatedProduct_nonneg (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 0 ≤ alpha)
    (hmean : ∀ j, 0 ≤ mean j) (hV : ∀ j omega, 0 ≤ V j omega) :
    ∀ i omega, 0 ≤ dependentTruncatedProduct alpha mean V i omega
  | 0, _ => by simp
  | i + 1, omega => by
      rw [dependentTruncatedProduct_succ]
      exact le_min
        (mul_nonneg
          (dependentTruncatedProduct_nonneg alpha mean V halpha hmean hV i omega)
          (hV (i + 1) omega))
        (mul_nonneg halpha (dependentPhaseMeanProduct_nonneg mean hmean (i + 1)))

/-- `Uᵢ Vᵢ₊₁` is the untruncated candidate for `Uᵢ₊₁`. -/
theorem dependentTruncatedProduct_succ_le_mul (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (i : ℕ) (omega : Omega) :
    dependentTruncatedProduct alpha mean V (i + 1) omega ≤
      dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega := by
  rw [dependentTruncatedProduct_succ]
  exact min_le_left _ _

/-- The deterministic cap on `Uᵢ` used in equations (8)--(11). -/
theorem dependentTruncatedProduct_succ_le_cap (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (i : ℕ) (omega : Omega) :
    dependentTruncatedProduct alpha mean V (i + 1) omega ≤
      alpha * dependentPhaseMeanProduct mean (i + 1) := by
  rw [dependentTruncatedProduct_succ]
  exact min_le_right _ _

/-- Uniform cap on `Uᵢ`, including `i = 0`.  The paper always chooses
`alpha ≥ 1`, so the base value `U₀ = 1` obeys the same formula. -/
theorem dependentTruncatedProduct_le_cap (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 1 ≤ alpha) (i : ℕ) (omega : Omega) :
    dependentTruncatedProduct alpha mean V i omega ≤
      alpha * dependentPhaseMeanProduct mean i := by
  cases i with
  | zero => simpa using halpha
  | succ i => exact dependentTruncatedProduct_succ_le_cap alpha mean V i omega

theorem integrable_dependentTruncatedProduct (mu : Measure Omega)
    [IsFiniteMeasure mu] (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 1 ≤ alpha)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega) (i : ℕ) :
    Integrable (dependentTruncatedProduct alpha mean V i) mu := by
  apply Integrable.of_bound
    (measurable_dependentTruncatedProduct alpha mean V hVmeas i).aestronglyMeasurable
    (alpha * dependentPhaseMeanProduct mean i)
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact dependentTruncatedProduct_le_cap alpha mean V halpha i omega
  · exact dependentTruncatedProduct_nonneg alpha mean V
      (zero_le_one.trans halpha) hmean hV0 i omega

theorem integrable_phase_of_le_two_mul_alpha_mean (mu : Measure Omega)
    [IsFiniteMeasure mu] (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 0 ≤ alpha)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j) (j : ℕ) :
    Integrable (V j) mu := by
  apply Integrable.of_bound (hVmeas j).aestronglyMeasurable (2 * alpha * mean j)
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (hV0 j omega)]
  exact hVcap j omega

theorem integrable_dependentTruncatedProduct_mul_phase (mu : Measure Omega)
    [IsFiniteMeasure mu] (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 1 ≤ alpha)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j) (i : ℕ) :
    Integrable (fun omega =>
      dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega) mu := by
  let a := alpha * dependentPhaseMeanProduct mean i
  let b := 2 * alpha * mean (i + 1)
  have hmeas : Measurable (fun omega =>
      dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega) :=
    (measurable_dependentTruncatedProduct alpha mean V hVmeas i).mul (hVmeas (i + 1))
  apply Integrable.of_bound hmeas.aestronglyMeasurable (a * b)
  filter_upwards with omega
  have hU0 := dependentTruncatedProduct_nonneg alpha mean V
    (zero_le_one.trans halpha) hmean hV0 i omega
  have hUa := dependentTruncatedProduct_le_cap alpha mean V halpha i omega
  have hnext0 := hV0 (i + 1) omega
  have hnextb := hVcap (i + 1) omega
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hU0 hnext0)]
  exact mul_le_mul hUa hnextb hnext0 (mul_nonneg (zero_le_one.trans halpha)
    (dependentPhaseMeanProduct_nonneg mean hmean i))

/-- Equation (8) of CV18 Lemma 7.15, with all measurability and boundedness
hypotheses exposed.  The factor `2` comes from
`Vᵢ₊₁ ≤ alpha * E(Wᵢ₊₁) ≤ 2 * alpha * E(Vᵢ₊₁)`. -/
theorem abs_integral_dependentTruncatedProduct_mul_phase_sub_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j)
    (hind : ∀ i, ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (i : ℕ) :
    |(∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) -
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          (∫ omega, V (i + 1) omega ∂mu)| ≤
      2 * epsilon * alpha ^ 2 * dependentPhaseMeanProduct mean (i + 1) := by
  have h := ApproxIndepFun.abs_integral_mul_sub_mul_integral_le mu
    (measurable_dependentTruncatedProduct alpha mean V hVmeas i)
    (hVmeas (i + 1))
    (mul_nonneg (zero_le_one.trans halpha)
      (dependentPhaseMeanProduct_nonneg mean hmean i))
    (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans halpha))
      (hmean (i + 1)))
    hepsilon
    (dependentTruncatedProduct_nonneg alpha mean V
      (zero_le_one.trans halpha) hmean hV0 i)
    (dependentTruncatedProduct_le_cap alpha mean V halpha i)
    (hV0 (i + 1)) (hVcap (i + 1)) (hind i)
  rw [dependentPhaseMeanProduct_succ]
  calc
    _ ≤ epsilon *
          (alpha * dependentPhaseMeanProduct mean i) *
          (2 * alpha * mean (i + 1)) := h
    _ = 2 * epsilon * alpha ^ 2 *
          (dependentPhaseMeanProduct mean i * mean (i + 1)) := by ring

/-- One-step upper recurrence extracted from equation (8). -/
theorem integral_dependentTruncatedProduct_succ_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (hind : ∀ i, ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (i : ℕ) :
    (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≤
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) +
        2 * epsilon * alpha ^ 2 * dependentPhaseMeanProduct mean (i + 1) := by
  have hnextInt := integrable_dependentTruncatedProduct mu alpha mean V halpha
    hmean hVmeas hV0 (i + 1)
  have hmulInt := integrable_dependentTruncatedProduct_mul_phase mu alpha mean V
    halpha hmean hVmeas hV0 hVcap i
  have hmono :
      (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≤
        ∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu :=
    integral_mono hnextInt hmulInt
      (dependentTruncatedProduct_succ_le_mul alpha mean V i)
  have hcov := abs_integral_dependentTruncatedProduct_mul_phase_sub_le
    mu alpha epsilon mean V halpha hepsilon hmean hVmeas hV0 hVcap hind i
  rw [hVmean (i + 1)] at hcov
  have hcovUpper :
      (∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) -
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) ≤
        2 * epsilon * alpha ^ 2 * dependentPhaseMeanProduct mean (i + 1) :=
    (le_abs_self _).trans hcov
  linarith

/-- Equation (9) of CV18 Lemma 7.15: the upper first-moment induction for
the recursively truncated product. -/
theorem integral_dependentTruncatedProduct_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ 2 * alpha * mean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (hind : ∀ i, ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu) :
    ∀ i,
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) ≤
        (1 + 2 * epsilon * alpha ^ 2 * i) *
          dependentPhaseMeanProduct mean i
  | 0 => by simp [dependentTruncatedProduct, dependentPhaseMeanProduct]
  | i + 1 => by
      have hstep := integral_dependentTruncatedProduct_succ_le
        mu alpha epsilon mean V halpha hepsilon hmean hVmeas hV0 hVcap
          hVmean hind i
      have hstep' :
          (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≤
            (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
                mean (i + 1) +
              2 * epsilon * alpha ^ 2 *
                (dependentPhaseMeanProduct mean i * mean (i + 1)) := by
        simpa only [dependentPhaseMeanProduct_succ] using hstep
      have hinduction := integral_dependentTruncatedProduct_le mu alpha epsilon
        mean V halpha hepsilon hmean hVmeas hV0 hVcap hVmean hind i
      have hscaled := mul_le_mul_of_nonneg_right hinduction (hmean (i + 1))
      rw [dependentPhaseMeanProduct_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
              mean (i + 1) +
            2 * epsilon * alpha ^ 2 *
              (dependentPhaseMeanProduct mean i * mean (i + 1)) := hstep'
        _ ≤ ((1 + 2 * epsilon * alpha ^ 2 * i) *
              dependentPhaseMeanProduct mean i) * mean (i + 1) +
            2 * epsilon * alpha ^ 2 *
              (dependentPhaseMeanProduct mean i * mean (i + 1)) := by
          exact add_le_add hscaled (le_refl _)
        _ = (1 + 2 * epsilon * alpha ^ 2 * (i + 1)) *
              (dependentPhaseMeanProduct mean i * mean (i + 1)) := by
          ring

/-- Squaring preserves approximate independence and gives the covariance
estimate used for the second-moment recurrence (10)--(11) of Lemma 7.15. -/
theorem ApproxIndepFun.abs_integral_sq_mul_sq_sub_mul_integral_sq_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X Y : Omega → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {a b epsilon : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hepsilon : 0 ≤ epsilon)
    (hX0 : ∀ omega, 0 ≤ X omega) (hXa : ∀ omega, X omega ≤ a)
    (hY0 : ∀ omega, 0 ≤ Y omega) (hYb : ∀ omega, Y omega ≤ b)
    (hind : ApproxIndepFun epsilon X Y mu) :
    |(∫ omega, X omega ^ 2 * Y omega ^ 2 ∂mu) -
        (∫ omega, X omega ^ 2 ∂mu) * (∫ omega, Y omega ^ 2 ∂mu)| ≤
      epsilon * a ^ 2 * b ^ 2 := by
  apply ApproxIndepFun.abs_integral_mul_sub_mul_integral_le mu
    (hX.pow_const 2) (hY.pow_const 2) (sq_nonneg a) (sq_nonneg b) hepsilon
  · intro omega
    exact sq_nonneg _
  · intro omega
    exact (sq_le_sq₀ (hX0 omega) ha).2 (hXa omega)
  · intro omega
    exact sq_nonneg _
  · intro omega
    exact (sq_le_sq₀ (hY0 omega) hb).2 (hYb omega)
  · have hsq : Measurable (fun x : ℝ => x ^ 2) :=
      measurable_id.pow_const 2
    have hsquared : ApproxIndepFun epsilon
        ((fun x : ℝ => x ^ 2) ∘ X) ((fun y : ℝ => y ^ 2) ∘ Y) mu :=
      ApproxIndepFun.comp hind hsq hsq
    simpa only [Function.comp_def] using hsquared

/-- Products of first moments squared are bounded by products of second
moments.  This is the finite-product form used between (10) and (11). -/
theorem dependentPhaseMeanProduct_sq_le (mean second : ℕ → ℝ)
    (hsecond0 : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j) (i : ℕ) :
    dependentPhaseMeanProduct mean i ^ 2 ≤
      dependentPhaseMeanProduct second i := by
  rw [dependentPhaseMeanProduct, dependentPhaseMeanProduct,
    ← Finset.prod_pow]
  exact Finset.prod_le_prod
    (fun j _ => sq_nonneg (mean (j + 1)))
    (fun j _ => hmeanSecond (j + 1))

/-- Squared form of the dependence error behind (10)--(11).  Unlike the
paper's word "similarly", this records the two estimates needed for the
constant `2`: the raw cap mean has square at most twice the truncated second
moment, and products of squared truncated means are bounded by products of
truncated second moments. -/
theorem abs_integral_dependentTruncatedProduct_sq_mul_phase_sq_sub_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hind : ∀ i, ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (i : ℕ) :
    |(∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 *
          V (i + 1) omega ^ 2 ∂mu) -
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 ∂mu) *
          (∫ omega, V (i + 1) omega ^ 2 ∂mu)| ≤
      2 * epsilon * alpha ^ 4 * dependentPhaseMeanProduct second (i + 1) := by
  have hcov := ApproxIndepFun.abs_integral_sq_mul_sq_sub_mul_integral_sq_le mu
    (measurable_dependentTruncatedProduct alpha mean V hVmeas i)
    (hVmeas (i + 1))
    (mul_nonneg (zero_le_one.trans halpha)
      (dependentPhaseMeanProduct_nonneg mean hmean i))
    (mul_nonneg (zero_le_one.trans halpha) (hrawMean (i + 1)))
    hepsilon
    (dependentTruncatedProduct_nonneg alpha mean V
      (zero_le_one.trans halpha) hmean hV0 i)
    (dependentTruncatedProduct_le_cap alpha mean V halpha i)
    (hV0 (i + 1)) (hVcap (i + 1)) (hind i)
  have hmeans := dependentPhaseMeanProduct_sq_le mean second hsecond
    hmeanSecond i
  have hpairsq :
      dependentPhaseMeanProduct mean i ^ 2 * rawMean (i + 1) ^ 2 ≤
        dependentPhaseMeanProduct second i * (2 * second (i + 1)) :=
    mul_le_mul hmeans (hrawSecond (i + 1)) (sq_nonneg _)
      (dependentPhaseMeanProduct_nonneg second hsecond i)
  rw [dependentPhaseMeanProduct_succ]
  calc
    _ ≤ epsilon *
          (alpha * dependentPhaseMeanProduct mean i) ^ 2 *
          (alpha * rawMean (i + 1)) ^ 2 := hcov
    _ = (epsilon * alpha ^ 4) *
          (dependentPhaseMeanProduct mean i ^ 2 * rawMean (i + 1) ^ 2) := by ring
    _ ≤ (epsilon * alpha ^ 4) *
          (dependentPhaseMeanProduct second i * (2 * second (i + 1))) := by
      exact mul_le_mul_of_nonneg_left hpairsq
        (mul_nonneg hepsilon (by positivity))
    _ = 2 * epsilon * alpha ^ 4 *
          (dependentPhaseMeanProduct second i * second (i + 1)) := by ring

theorem integrable_dependentTruncatedProduct_sq (mu : Measure Omega)
    [IsFiniteMeasure mu] (alpha : ℝ) (mean : ℕ → ℝ)
    (V : ℕ → Omega → ℝ) (halpha : 1 ≤ alpha)
    (hmean : ∀ j, 0 ≤ mean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega) (i : ℕ) :
    Integrable (fun omega =>
      dependentTruncatedProduct alpha mean V i omega ^ 2) mu := by
  let cap := alpha * dependentPhaseMeanProduct mean i
  have hcap0 : 0 ≤ cap := mul_nonneg (zero_le_one.trans halpha)
    (dependentPhaseMeanProduct_nonneg mean hmean i)
  apply Integrable.of_bound
    ((measurable_dependentTruncatedProduct alpha mean V hVmeas i).pow_const 2).aestronglyMeasurable
    (cap ^ 2)
  filter_upwards with omega
  have hU0 := dependentTruncatedProduct_nonneg alpha mean V
    (zero_le_one.trans halpha) hmean hV0 i omega
  have hUcap := dependentTruncatedProduct_le_cap alpha mean V halpha i omega
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ hU0 hcap0).2 hUcap

theorem integrable_dependentTruncatedProduct_sq_mul_phase_sq
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (alpha : ℝ) (mean rawMean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hmean : ∀ j, 0 ≤ mean j)
    (hrawMean : ∀ j, 0 ≤ rawMean j) (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j) (i : ℕ) :
    Integrable (fun omega =>
      dependentTruncatedProduct alpha mean V i omega ^ 2 *
        V (i + 1) omega ^ 2) mu := by
  let a := alpha * dependentPhaseMeanProduct mean i
  let b := alpha * rawMean (i + 1)
  have ha0 : 0 ≤ a := mul_nonneg (zero_le_one.trans halpha)
    (dependentPhaseMeanProduct_nonneg mean hmean i)
  have hb0 : 0 ≤ b := mul_nonneg (zero_le_one.trans halpha) (hrawMean (i + 1))
  have hmeas : Measurable (fun omega =>
      dependentTruncatedProduct alpha mean V i omega ^ 2 *
        V (i + 1) omega ^ 2) :=
    ((measurable_dependentTruncatedProduct alpha mean V hVmeas i).pow_const 2).mul
      ((hVmeas (i + 1)).pow_const 2)
  apply Integrable.of_bound hmeas.aestronglyMeasurable (a ^ 2 * b ^ 2)
  filter_upwards with omega
  have hU0 := dependentTruncatedProduct_nonneg alpha mean V
    (zero_le_one.trans halpha) hmean hV0 i omega
  have hUa := dependentTruncatedProduct_le_cap alpha mean V halpha i omega
  have hnext0 := hV0 (i + 1) omega
  have hnextb := hVcap (i + 1) omega
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact mul_le_mul ((sq_le_sq₀ hU0 ha0).2 hUa)
    ((sq_le_sq₀ hnext0 hb0).2 hnextb) (sq_nonneg _) (sq_nonneg _)

/-- Equation (11), with the sound successor index made explicit.  It is the
one-step second-moment estimate from which equation (10) follows. -/
theorem integral_dependentTruncatedProduct_sq_mul_phase_sq_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVsecond : ∀ j, (∫ omega, V j omega ^ 2 ∂mu) = second j)
    (hind : ∀ i, ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (i : ℕ) :
    (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 *
        V (i + 1) omega ^ 2 ∂mu) ≤
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 ∂mu) *
          second (i + 1) +
        2 * epsilon * alpha ^ 4 * dependentPhaseMeanProduct second (i + 1) := by
  have hcov := abs_integral_dependentTruncatedProduct_sq_mul_phase_sq_sub_le
    mu alpha epsilon mean rawMean second V halpha hepsilon hmean hrawMean
      hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap hind i
  rw [hVsecond (i + 1)] at hcov
  have hupper :
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 *
          V (i + 1) omega ^ 2 ∂mu) -
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 ∂mu) *
          second (i + 1) ≤
        2 * epsilon * alpha ^ 4 * dependentPhaseMeanProduct second (i + 1) :=
    (le_abs_self _).trans hcov
  linarith

/-- Equation (10) of CV18 Lemma 7.15. -/
theorem integral_dependentTruncatedProduct_sq_le
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean second : ℕ → ℝ)
    (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hmean : ∀ j, 0 ≤ mean j) (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVsecond : ∀ j, (∫ omega, V j omega ^ 2 ∂mu) = second j)
    (hind : ∀ i, ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu) :
    ∀ i,
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 ∂mu) ≤
        (1 + 2 * epsilon * alpha ^ 4 * i) *
          dependentPhaseMeanProduct second i
  | 0 => by simp [dependentTruncatedProduct, dependentPhaseMeanProduct]
  | i + 1 => by
      have hcandidate := integral_dependentTruncatedProduct_sq_mul_phase_sq_le
        mu alpha epsilon mean rawMean second V halpha hepsilon hmean hrawMean
          hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap hVsecond hind i
      have hnextInt := integrable_dependentTruncatedProduct_sq mu alpha mean V
        halpha hmean hVmeas hV0 (i + 1)
      have hcandidateInt := integrable_dependentTruncatedProduct_sq_mul_phase_sq
        mu alpha mean rawMean V halpha hmean hrawMean hVmeas hV0 hVcap i
      have hpoint : ∀ omega,
          dependentTruncatedProduct alpha mean V (i + 1) omega ^ 2 ≤
            dependentTruncatedProduct alpha mean V i omega ^ 2 *
              V (i + 1) omega ^ 2 := by
        intro omega
        rw [← mul_pow]
        exact (sq_le_sq₀
          (dependentTruncatedProduct_nonneg alpha mean V
            (zero_le_one.trans halpha) hmean hV0 (i + 1) omega)
          (mul_nonneg
            (dependentTruncatedProduct_nonneg alpha mean V
              (zero_le_one.trans halpha) hmean hV0 i omega)
            (hV0 (i + 1) omega))).2
          (dependentTruncatedProduct_succ_le_mul alpha mean V i omega)
      have hmono := integral_mono hnextInt hcandidateInt hpoint
      have hinduction := integral_dependentTruncatedProduct_sq_le
        mu alpha epsilon mean rawMean second V halpha hepsilon hmean hrawMean
          hsecond hmeanSecond hrawSecond hVmeas hV0 hVcap hVsecond hind i
      have hscaled := mul_le_mul_of_nonneg_right hinduction (hsecond (i + 1))
      rw [dependentPhaseMeanProduct_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ ∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 *
              V (i + 1) omega ^ 2 ∂mu := hmono
        _ ≤ (∫ omega, dependentTruncatedProduct alpha mean V i omega ^ 2 ∂mu) *
              second (i + 1) +
            2 * epsilon * alpha ^ 4 *
              (dependentPhaseMeanProduct second i * second (i + 1)) := by
          simpa only [dependentPhaseMeanProduct_succ] using hcandidate
        _ ≤ ((1 + 2 * epsilon * alpha ^ 4 * i) *
              dependentPhaseMeanProduct second i) * second (i + 1) +
            2 * epsilon * alpha ^ 4 *
              (dependentPhaseMeanProduct second i * second (i + 1)) := by
          exact add_le_add hscaled (le_refl _)
        _ = (1 + 2 * epsilon * alpha ^ 4 * (i + 1)) *
              (dependentPhaseMeanProduct second i * second (i + 1)) := by ring

/-- Equation (12), before inserting the second-moment estimate: truncating
the candidate `Uᵢ Vᵢ₊₁` at its deterministic cap loses at most its second
moment divided by four times that cap. -/
theorem integral_dependentTruncatedProduct_succ_ge
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha : ℝ) (mean rawMean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hmean : ∀ j, 0 ≤ mean j)
    (hmeanPos : ∀ j, 0 < mean j) (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hrawMean_le : ∀ j, rawMean j ≤ 2 * mean j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j) (i : ℕ) :
    (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≥
      (∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) -
        (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega) ^ 2 ∂mu) /
          (4 * (alpha * dependentPhaseMeanProduct mean (i + 1))) := by
  have hVcapTwo : ∀ j omega, V j omega ≤ 2 * alpha * mean j := by
    intro j omega
    calc
      V j omega ≤ alpha * rawMean j := hVcap j omega
      _ ≤ alpha * (2 * mean j) :=
        mul_le_mul_of_nonneg_left (hrawMean_le j) (zero_le_one.trans halpha)
      _ = 2 * alpha * mean j := by ring
  have hcandidateInt := integrable_dependentTruncatedProduct_mul_phase
    mu alpha mean V halpha hmean hVmeas hV0 hVcapTwo i
  have hcandidateSqInt : Integrable (fun omega =>
      (dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega) ^ 2) mu := by
    simpa only [mul_pow] using
      integrable_dependentTruncatedProduct_sq_mul_phase_sq mu alpha mean rawMean V
        halpha hmean hrawMean hVmeas hV0 hVcap i
  have hcandidate0 : ∀ omega,
      0 ≤ dependentTruncatedProduct alpha mean V i omega * V (i + 1) omega :=
    fun omega => mul_nonneg
      (dependentTruncatedProduct_nonneg alpha mean V
        (zero_le_one.trans halpha) hmean hV0 i omega)
      (hV0 (i + 1) omega)
  have hmeanProductPos : 0 < dependentPhaseMeanProduct mean (i + 1) := by
    apply Finset.prod_pos
    intro j _
    exact hmeanPos (j + 1)
  have hcapPos : 0 < alpha * dependentPhaseMeanProduct mean (i + 1) :=
    mul_pos (zero_lt_one.trans_le halpha) hmeanProductPos
  have htrunc := integral_min_ge_integral_sub_secondMoment_div_four mu
    hcandidateInt hcandidateSqInt hcandidate0 hcapPos
  simpa only [dependentTruncatedProduct_succ] using htrunc

/-- The one-step lower recurrence used in (14).  Its two error contributions
(dependence and truncation) are each charged `Mᵢ₊₁/(2 alpha)`. -/
theorem integral_dependentTruncatedProduct_succ_ge_sub
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hsmall : 4 * epsilon * alpha ^ 3 ≤ 1)
    (hmean : ∀ j, 0 ≤ mean j) (hmeanPos : ∀ j, 0 < mean j)
    (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hrawMean_le : ∀ j, rawMean j ≤ 2 * mean j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (hind : ∀ i, ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (hcandidateSecond : ∀ i,
      (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega) ^ 2 ∂mu) ≤
          2 * dependentPhaseMeanProduct mean (i + 1) ^ 2)
    (i : ℕ) :
    (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≥
      (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) -
        dependentPhaseMeanProduct mean (i + 1) / alpha := by
  have hVcapTwo : ∀ j omega, V j omega ≤ 2 * alpha * mean j := by
    intro j omega
    calc
      V j omega ≤ alpha * rawMean j := hVcap j omega
      _ ≤ alpha * (2 * mean j) :=
        mul_le_mul_of_nonneg_left (hrawMean_le j) (zero_le_one.trans halpha)
      _ = 2 * alpha * mean j := by ring
  have htrunc := integral_dependentTruncatedProduct_succ_ge mu alpha mean rawMean V
    halpha hmean hmeanPos hrawMean hrawMean_le hVmeas hV0 hVcap i
  have hcov := abs_integral_dependentTruncatedProduct_mul_phase_sub_le
    mu alpha epsilon mean V halpha hepsilon hmean hVmeas hV0 hVcapTwo hind i
  rw [hVmean (i + 1)] at hcov
  let M := dependentPhaseMeanProduct mean (i + 1)
  have hMpos : 0 < M := by
    dsimp [M, dependentPhaseMeanProduct]
    apply Finset.prod_pos
    intro j _
    exact hmeanPos (j + 1)
  have halphaPos : 0 < alpha := zero_lt_one.trans_le halpha
  have hcoef : 2 * epsilon * alpha ^ 2 ≤ 1 / (2 * alpha) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) halphaPos)]
    nlinarith [hsmall]
  have hdepCharge : 2 * epsilon * alpha ^ 2 * M ≤ M / (2 * alpha) := by
    calc
      2 * epsilon * alpha ^ 2 * M ≤ (1 / (2 * alpha)) * M :=
        mul_le_mul_of_nonneg_right hcoef hMpos.le
      _ = M / (2 * alpha) := by ring
  have hcovLower :
      (∫ omega, dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega ∂mu) ≥
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
            mean (i + 1) - M / (2 * alpha) := by
    have hlower :
        -(2 * epsilon * alpha ^ 2 * M) ≤
          (∫ omega, dependentTruncatedProduct alpha mean V i omega *
              V (i + 1) omega ∂mu) -
            (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
              mean (i + 1) :=
      (neg_le_of_abs_le hcov)
    linarith
  have htruncCharge :
      (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
          V (i + 1) omega) ^ 2 ∂mu) /
          (4 * (alpha * M)) ≤ M / (2 * alpha) := by
    calc
      _ ≤ (2 * M ^ 2) / (4 * (alpha * M)) := by
        exact div_le_div_of_nonneg_right (hcandidateSecond i)
          (mul_nonneg (by norm_num) (mul_nonneg halphaPos.le hMpos.le))
      _ = M / (2 * alpha) := by
        field_simp [halphaPos.ne', hMpos.ne']
        ring
  change (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≥
    (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
      mean (i + 1) - M / alpha
  change (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≥
    (∫ omega, dependentTruncatedProduct alpha mean V i omega *
      V (i + 1) omega ∂mu) -
      (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega) ^ 2 ∂mu) / (4 * (alpha * M)) at htrunc
  have hcombined :
      (∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu) ≥
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
            mean (i + 1) - M / (2 * alpha) - M / (2 * alpha) := by
    linarith
  calc
    (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) - M / alpha =
        (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
          mean (i + 1) - M / (2 * alpha) - M / (2 * alpha) := by
      field_simp [halphaPos.ne']
      ring
    _ ≤ ∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu :=
      hcombined

/-- Equation (14), in a slightly cleaner zero-based form:
`E(Uᵢ) ≥ (1 - i/alpha) * ∏ E(Vⱼ)`. -/
theorem integral_dependentTruncatedProduct_ge
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (alpha epsilon : ℝ) (mean rawMean : ℕ → ℝ) (V : ℕ → Omega → ℝ)
    (halpha : 1 ≤ alpha) (hepsilon : 0 ≤ epsilon)
    (hsmall : 4 * epsilon * alpha ^ 3 ≤ 1)
    (hmean : ∀ j, 0 ≤ mean j) (hmeanPos : ∀ j, 0 < mean j)
    (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hrawMean_le : ∀ j, rawMean j ≤ 2 * mean j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega, V j omega ≤ alpha * rawMean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (hind : ∀ i, ApproxIndepFun epsilon
      (dependentTruncatedProduct alpha mean V i) (V (i + 1)) mu)
    (hcandidateSecond : ∀ i,
      (∫ omega, (dependentTruncatedProduct alpha mean V i omega *
        V (i + 1) omega) ^ 2 ∂mu) ≤
          2 * dependentPhaseMeanProduct mean (i + 1) ^ 2) :
    ∀ i,
      (1 - i / alpha) * dependentPhaseMeanProduct mean i ≤
        ∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu
  | 0 => by simp [dependentTruncatedProduct, dependentPhaseMeanProduct]
  | i + 1 => by
      have hstep := integral_dependentTruncatedProduct_succ_ge_sub
        mu alpha epsilon mean rawMean V halpha hepsilon hsmall hmean hmeanPos
          hrawMean hrawMean_le hVmeas hV0 hVcap hVmean hind hcandidateSecond i
      have hinduction := integral_dependentTruncatedProduct_ge
        mu alpha epsilon mean rawMean V halpha hepsilon hsmall hmean hmeanPos
          hrawMean hrawMean_le hVmeas hV0 hVcap hVmean hind hcandidateSecond i
      have hscaled := mul_le_mul_of_nonneg_right hinduction (hmean (i + 1))
      rw [dependentPhaseMeanProduct_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      calc
        (1 - (i + 1) / alpha) *
            (dependentPhaseMeanProduct mean i * mean (i + 1)) =
          ((1 - i / alpha) * dependentPhaseMeanProduct mean i) *
              mean (i + 1) -
            (dependentPhaseMeanProduct mean i * mean (i + 1)) / alpha := by ring
        _ ≤ (∫ omega, dependentTruncatedProduct alpha mean V i omega ∂mu) *
              mean (i + 1) -
            (dependentPhaseMeanProduct mean i * mean (i + 1)) / alpha := by
          linarith
        _ ≤ ∫ omega, dependentTruncatedProduct alpha mean V (i + 1) omega ∂mu := by
          simpa only [dependentPhaseMeanProduct_succ] using hstep

#print axioms measurable_dependentTruncatedProduct
#print axioms dependentTruncatedProduct_nonneg
#print axioms abs_integral_dependentTruncatedProduct_mul_phase_sub_le
#print axioms integral_dependentTruncatedProduct_le
#print axioms integral_dependentTruncatedProduct_sq_le
#print axioms integral_dependentTruncatedProduct_succ_ge
#print axioms integral_dependentTruncatedProduct_ge
#print axioms ApproxIndepFun.abs_integral_sq_mul_sq_sub_mul_integral_sq_le

end ArlibCommunity.Algorithms.CV18
