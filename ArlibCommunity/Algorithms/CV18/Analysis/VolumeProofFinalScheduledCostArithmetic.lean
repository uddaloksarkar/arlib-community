/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledParameters
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryShadowDomination
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Arithmetic envelopes for the final scheduled expected-cost proof -/

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal BigOperators

/-- The safe finite retry horizon is controlled by the same protected
logarithm that appears in the corrected scheduled mixing stride. -/
theorem figureOneSafeRetryCount_cast_le_correctedMixingLog
    (q : VolumeParams) :
    (figureOneSafeRetryCount q : ℝ) ≤
      129 * protectedLog
        (1 / figureOneCorrectedBlockMixingError q
          (figureOneSafeRetryCount q - 1)) := by
  let nu := figureOnePerSampleMixingError q
  let N := figureOneSafeRetryCount q
  let B := protectedLog
    (1 / figureOneCorrectedBlockMixingError q (N - 1))
  have hnu : 0 < nu := by
    simpa [nu] using figureOnePerSampleMixingError_pos q
  have hNpos : 0 < N := by
    simpa [N] using figureOneSafeRetryCount_pos q
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hrawNonneg : 0 ≤ 128 * protectedLog (4 / nu) := by
    have : 1 ≤ protectedLog (4 / nu) := le_max_left _ _
    positivity
  have hceil : (N : ℝ) < 128 * protectedLog (4 / nu) + 1 := by
    simpa [N, figureOneSafeRetryCount, nu] using
      Nat.ceil_lt_add_one hrawNonneg
  have harg : 4 / nu ≤
      1 / figureOneCorrectedBlockMixingError q (N - 1) := by
    unfold figureOneCorrectedBlockMixingError
    change 4 / nu ≤ 1 / (nu / (4 * (((N - 1 : ℕ) : ℝ) + 1)))
    have hNcast : (((N - 1 : ℕ) : ℝ) + 1) = N := by
      exact_mod_cast Nat.sub_add_cancel hNpos
    rw [hNcast]
    rw [one_div_div]
    apply (div_le_div_iff_of_pos_right hnu).2
    nlinarith
  have hargPos : 0 < 4 / nu := by positivity
  have hprotected : protectedLog (4 / nu) ≤ B := by
    dsimp only [B, protectedLog]
    apply max_le_max_left
    exact Real.strictMonoOn_log.monotoneOn hargPos
      (hargPos.trans_le harg) harg
  have hBone : 1 ≤ B := by
    dsimp only [B, protectedLog]
    exact le_max_left _ _
  dsimp only [N, B, nu] at hceil hprotected hBone ⊢
  nlinarith

/-- The adjacent-speedy warmness factor is an absolute numerical constant. -/
theorem speedyAdjacentWarmConstant_le_twelve (q : VolumeParams) :
    speedyAdjacentWarmConstant q ≤ 12 := by
  unfold speedyAdjacentWarmConstant
  calc
    Real.exp (1 / 2) * (4 * Real.exp (1 / 2)) =
        4 * Real.exp 1 := by
      rw [show Real.exp (1 / 2) * (4 * Real.exp (1 / 2)) =
          4 * (Real.exp (1 / 2) * Real.exp (1 / 2)) by ring,
        ← Real.exp_add]
      norm_num
    _ ≤ 12 := by nlinarith [Real.exp_one_lt_three]

/-- Reciprocal-square envelope for the conductance denominator after the
scheduled proposal radius is substituted. -/
theorem figureOneScheduledMixingDenominator_inv_sq_le
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let d := figureOneScheduledProposalRadius q sigma2 * Real.log 2 /
      (640 * Real.sqrt sigma2 * Real.sqrt q.n)
    1 / d ^ 2 ≤
      10 ^ 15 * max 1 sigma2 * (q.n : ℝ) ^ 2 *
        figureOneScheduledAccuracyLog q := by
  dsimp only
  let n : ℝ := q.n
  let A := figureOneScheduledAccuracyLog q
  let s := Real.sqrt sigma2
  let rn := Real.sqrt n
  let rA := Real.sqrt (n * A)
  let d := (min s 1 / (4096 * rA)) * Real.log 2 / (640 * s * rn)
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hA : 1 ≤ A := by
    simpa [A] using figureOneScheduledAccuracyLog_one_le q
  have hs : 0 < s := by simpa [s] using Real.sqrt_pos.2 hsigma2
  have hrn : 0 < rn := by simpa [rn] using Real.sqrt_pos.2 hn
  have hrA : 0 < rA := by
    dsimp only [rA]
    positivity
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  change 1 / d ^ 2 ≤ 10 ^ 15 * max 1 sigma2 * n ^ 2 * A
  rw [div_le_iff₀ (sq_pos_of_pos hd)]
  by_cases hsmall : sigma2 ≤ 1
  · have hsle : s ≤ 1 := by
      dsimp only [s]
      nlinarith [Real.sq_sqrt hsigma2.le,
        Real.sqrt_nonneg sigma2]
    have hmax : max 1 sigma2 = 1 := max_eq_left hsmall
    have hmin : min s 1 = s := min_eq_left hsle
    have hs2 : s ^ 2 = sigma2 := by
      simpa [s] using Real.sq_sqrt hsigma2.le
    have hrn2 : rn ^ 2 = n := by
      simpa [rn] using Real.sq_sqrt hn.le
    have hrA2 : rA ^ 2 = n * A := by
      simpa [rA] using Real.sq_sqrt
        (mul_nonneg hn.le (le_trans zero_le_one hA))
    have hcoef : (4096 : ℝ) ^ 2 * 640 ^ 2 ≤
        10 ^ 15 * Real.log 2 ^ 2 := by
      nlinarith [sq_nonneg (Real.log 2 - 1 / 2)]
    have hscaled := mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (sq_nonneg n) (le_trans zero_le_one hA))
    rw [hmax]
    dsimp only [d]
    rw [hmin]
    field_simp
    rw [hrA2, hrn2]
    nlinarith
  · have hone : 1 < sigma2 := lt_of_not_ge hsmall
    have hsone : 1 ≤ s := by
      dsimp only [s]
      nlinarith [Real.sq_sqrt hsigma2.le,
        Real.sqrt_nonneg sigma2]
    have hmax : max 1 sigma2 = sigma2 := max_eq_right hone.le
    have hmin : min s 1 = 1 := min_eq_right hsone
    have hs2 : s ^ 2 = sigma2 := by
      simpa [s] using Real.sq_sqrt hsigma2.le
    have hrn2 : rn ^ 2 = n := by
      simpa [rn] using Real.sq_sqrt hn.le
    have hrA2 : rA ^ 2 = n * A := by
      simpa [rA] using Real.sq_sqrt
        (mul_nonneg hn.le (le_trans zero_le_one hA))
    have hcoef : (4096 : ℝ) ^ 2 * 640 ^ 2 ≤
        10 ^ 15 * Real.log 2 ^ 2 := by
      nlinarith [sq_nonneg (Real.log 2 - 1 / 2)]
    have hscaled := mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg hsigma2.le
        (mul_nonneg (sq_nonneg n) (le_trans zero_le_one hA)))
    rw [hmax]
    dsimp only [d]
    rw [hmin]
    field_simp
    rw [hrA2, hs2, hrn2]
    nlinarith

#print axioms figureOneSafeRetryCount_cast_le_correctedMixingLog
#print axioms figureOneScheduledMixingDenominator_inv_sq_le

end ArlibCommunity.Algorithms.CV18
