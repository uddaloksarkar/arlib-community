/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofThirdMomentLogConcavity
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependentThirdMoment

/-!
# Concrete third moments for the fixed CV18 cooling schedule

The fourth moment becomes singular at the dimension-three fixed update
`t / s = 4 / 3`.  The third moment stays finite.  This module specializes the
one-third partition inequality to that endpoint and records a rational `L³`
constant suitable for the approximate-covariance theorem.
-/

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-- On a dimension-three fixed-rate update, the precision-ratio base in the
one-third partition inequality is at most `27 / 16`. -/
theorem fixedRate_thirdMoment_precisionFactor_le
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hstep : t ≤ s * (1 + 1 / (3 : ℝ))) :
    s ^ 3 / (t ^ 2 * (3 * s - 2 * t)) ≤ 27 / 16 := by
  have ht : 0 < t := hs.trans_le hst
  have hthree : 0 < 3 * s - 2 * t := by nlinarith
  have hfirst : 0 ≤ 4 * s - 3 * t := by nlinarith
  have hsecond : 0 ≤ 18 * t ^ 2 - 3 * s * t - 4 * s ^ 2 := by
    have hprod : 0 ≤ (t - s) * (18 * t + 15 * s) :=
      mul_nonneg (sub_nonneg.mpr hst) (by positivity)
    nlinarith [sq_pos_of_pos hs]
  have hfactor :
      27 * t ^ 2 * (3 * s - 2 * t) - 16 * s ^ 3 =
        (4 * s - 3 * t) * (18 * t ^ 2 - 3 * s * t - 4 * s ^ 2) := by
    ring
  rw [div_le_iff₀ (mul_pos (sq_pos_of_pos ht) hthree)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
  have hnonneg := mul_nonneg hfirst hsecond
  rw [← hfactor] at hnonneg
  nlinarith

/-- Exact-target relative third moment for every fixed schedule step in
dimension three.  The constant `(27/16)^4` is the direct specialization of
the convex-body one-third log-concavity theorem. -/
theorem scheduleValue_fixedRate_relativeThirdMoment_le_dim_three
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hn : q.n = 3) (hsone : scheduleValue q k ≤ 1) :
    ((∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 3) ≤
      (27 / 16 : ℝ) ^ 4 := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  have hs : 0 < s := scheduleValue_pos q k
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have ht_next : t = nextVariance q s := by
    simpa [s, t] using scheduleValue_succ q k
  have hstep : t ≤ s * (1 + 1 / (3 : ℝ)) := by
    rw [ht_next]
    unfold nextVariance
    refine (min_le_right _ _).trans ?_
    rw [coolingRate, if_pos]
    · simpa [hn]
    · simpa [s] using hsone
  have hthree : 2 * t < 3 * s := by nlinarith
  have hraw := gaussianRatioWeight_relativeThirdMoment_le_of_oneThird
    q I (truncatedBody_gaussianPartitionOneThirdLogConcave q I)
      hs hst hthree
  have hbase := fixedRate_thirdMoment_precisionFactor_le hs hst hstep
  have hexponent : q.n + 1 = 4 := by omega
  rw [hexponent] at hraw
  simpa [s, t] using hraw.trans (pow_le_pow_left₀ (by positivity) hbase 4)

/-- A rational `L³` norm constant: `129/64` cubed dominates the exact
dimension-three fixed-rate relative third moment. -/
theorem scheduleValue_fixedRate_relativeThirdMoment_le_rational_cube_dim_three
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hn : q.n = 3) (hsone : scheduleValue q k ≤ 1) :
    ((∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 3) ≤
      (129 / 64 : ℝ) ^ 3 := by
  calc
    _ ≤ (27 / 16 : ℝ) ^ 4 :=
      scheduleValue_fixedRate_relativeThirdMoment_le_dim_three q I k hn hsone
    _ ≤ (129 / 64 : ℝ) ^ 3 := by norm_num

#print axioms fixedRate_thirdMoment_precisionFactor_le
#print axioms scheduleValue_fixedRate_relativeThirdMoment_le_dim_three
#print axioms
  scheduleValue_fixedRate_relativeThirdMoment_le_rational_cube_dim_three

end ArlibCommunity.Algorithms.CV18
