/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofThirdMomentLogConcavity
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependentThirdMoment
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianDeathArithmetic

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

/-- Direct `L³` form of the dimension-three bound, ready to instantiate the
coordinate premise of the approximate-independence equation-(6) theorem. -/
theorem scheduleValue_fixedRate_thirdMoment_le_rational_mean_cube_dim_three
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hn : q.n = 3) (hsone : scheduleValue q k ≤ 1) :
    let nu : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k)
    let weight := gaussianRatioWeight (n := q.n)
      (scheduleValue q k) (scheduleValue q (k + 1))
    (∫ x, weight x ^ 3 ∂nu) ≤
      ((129 / 64 : ℝ) * ∫ x, weight x ∂nu) ^ 3 := by
  dsimp only
  let mean := ∫ x, gaussianRatioWeight (scheduleValue q k)
    (scheduleValue q (k + 1)) x
      ∂(truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k) : Measure (AmbientSpace q.n))
  have hmean : 0 < mean := by
    rw [show mean = gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
        gaussianIntegral (truncatedBody q I) (scheduleValue q k) by
      simpa [mean] using gaussianRatioWeight_mean_eq q I (scheduleValue_pos q k)]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q (k + 1)))
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q k))
  have hrel :=
    scheduleValue_fixedRate_relativeThirdMoment_le_rational_cube_dim_three
      q I k hn hsone
  rw [div_le_iff₀ (pow_pos hmean 3)] at hrel
  change _ ≤ ((129 / 64 : ℝ) * mean) ^ 3
  nlinarith

/-- The first two cooling transitions cannot reach the terminal variance.
This elementary lower bound supplies the factor four in the global
dependence truncation parameter. -/
theorem four_le_figureOneDependentPhaseCount (q : VolumeParams) :
    4 ≤ figureOneDependentPhaseCount q := by
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hstep : ∀ {s : ℝ}, 0 ≤ s → s ≤ 1 →
      nextVariance q s ≤ s * (4 / 3 : ℝ) := by
    intro s hs hsone
    calc
      nextVariance q s ≤ s * coolingRate q s := min_le_right _ _
      _ = s * (1 + 1 / (q.n : ℝ)) := by
        rw [coolingRate, if_pos hsone]
      _ ≤ s * (4 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hs
        have hinv : 1 / (q.n : ℝ) ≤ 1 / 3 :=
          one_div_le_one_div_of_le (by norm_num) hn
        linarith
  have hzero : scheduleValue q 0 ≤ (1 / 192 : ℝ) := by
    simp only [scheduleValue, Function.iterate_zero_apply]
    unfold initialVariance
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 64 * (q.n : ℝ))]
    nlinarith [q.heps.2]
  have hone : scheduleValue q 1 ≤ (1 / 144 : ℝ) := by
    rw [show 1 = 0 + 1 by omega, scheduleValue_succ]
    calc
      nextVariance q (scheduleValue q 0) ≤
          scheduleValue q 0 * (4 / 3 : ℝ) :=
        hstep (scheduleValue_pos q 0).le (hzero.trans (by norm_num))
      _ ≤ (1 / 192 : ℝ) * (4 / 3 : ℝ) := by gcongr
      _ = 1 / 144 := by norm_num
  have htwo : scheduleValue q 2 ≤ (1 / 108 : ℝ) := by
    rw [show 2 = 1 + 1 by omega, scheduleValue_succ]
    calc
      nextVariance q (scheduleValue q 1) ≤
          scheduleValue q 1 * (4 / 3 : ℝ) :=
        hstep (scheduleValue_pos q 1).le (hone.trans (by norm_num))
      _ ≤ (1 / 144 : ℝ) * (4 / 3 : ℝ) := by gcongr
      _ = 1 / 108 := by norm_num
  have htwoTerminal : scheduleValue q 2 < terminalVariance q :=
    htwo.trans_lt <| (by norm_num : (1 / 108 : ℝ) < 1) |>.trans_le
      (terminalVariance_ge_one' q)
  have hterminalSteps : 3 ≤ terminalPhaseSteps q := by
    by_contra hnot
    have hle : terminalPhaseSteps q ≤ 2 := by omega
    have heq := scheduleValue_terminal_persists q hle
      (scheduleValue_terminalPhaseSteps q)
    linarith
  simpa [figureOneDependentPhaseCount] using Nat.add_le_add_right hterminalSteps 1

/-- The final CV18 truncation parameter is at least `4096`.  This is the
numerical threshold at which the dimension-three `L³` covariance loss fits
one eighth of the executable moment slack. -/
theorem figureOneDependentAlpha_ge_4096 (q : VolumeParams) :
    (4096 : ℝ) ≤ figureOneDependentAlpha q := by
  have hm : (4 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast four_le_figureOneDependentPhaseCount q
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  rw [figureOneDependentAlpha, le_div_iff₀ (sq_pos_of_pos q.heps.1)]
  nlinarith

/-- At the final CV18 parameters, the optimized `p = 3` covariance loss
with dimension-three fixed-phase norm constant `129/64` fits exactly in the
`slack/8` reserve used by the phasewise capstone. -/
theorem figureOne_fixedThirdMoment_dependence_le_slack_div_eight
    (q : VolumeParams) :
    3 * figureOneDependentEpsilon q ^ (1 / 3 : ℝ) *
        (129 / 64 : ℝ) ^ 2 ≤
      figureOneExecutableMomentSlack q / 8 := by
  let d := figureOneDependentEpsilon q ^ (1 / 3 : ℝ)
  let alpha := figureOneDependentAlpha q
  let slack := figureOneExecutableMomentSlack q
  have hepsilon : 0 < figureOneDependentEpsilon q := by
    unfold figureOneDependentEpsilon
    have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
      exact_mod_cast figureOneDependentPhaseCount_pos q
    exact div_pos (sq_pos_of_pos q.heps.1)
      (mul_pos
        (mul_pos (by norm_num) (pow_pos (figureOneDependentAlpha_pos q) 4)) hm)
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hslack0 : 0 ≤ slack / 8 := by
    exact div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num)
  have hdcube : d ^ 3 = figureOneDependentEpsilon q := by
    dsimp [d]
    convert Real.rpow_inv_natCast_pow hepsilon.le
      (by norm_num : (3 : ℕ) ≠ 0) using 1
    norm_num
  apply (pow_le_pow_iff_left₀
    (mul_nonneg (mul_nonneg (by norm_num) hd0) (sq_nonneg _))
    hslack0 (by norm_num : (3 : ℕ) ≠ 0)).mp
  have halpha : (4096 : ℝ) ≤ alpha := by
    simpa [alpha] using figureOneDependentAlpha_ge_4096 q
  have halphaPos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have halphaSq : (4096 : ℝ) ^ 2 ≤ alpha ^ 2 :=
    pow_le_pow_left₀ (by norm_num) halpha 2
  rw [show (3 * d * (129 / 64 : ℝ) ^ 2) ^ 3 =
      3 ^ 3 * d ^ 3 * (129 / 64 : ℝ) ^ 6 by ring,
    hdcube]
  have hdependent : figureOneDependentEpsilon q = slack / alpha ^ 4 := by
    simpa [slack, alpha] using
      figureOneDependentEpsilon_eq_slack_div_alpha_four q
  have hslack : slack = 1 / (4 * alpha) := by
    simpa [slack, alpha] using
      figureOneExecutableMomentSlack_eq_inv_four_alpha q
  rw [hdependent, hslack]
  field_simp [halphaPos.ne']
  nlinarith

/-- The exact dependence contribution in the empirical-average second
moment (including the finite-count factor) fits the capstone reserve. -/
theorem figureOne_fixedThirdMoment_average_dependence_le_slack_div_eight
    (q : VolumeParams) {count : ℕ} (hcount : 0 < count) (mean : ℝ) :
    3 * figureOneDependentEpsilon q ^ (1 / 3 : ℝ) *
        (1 - 1 / (count : ℝ)) *
          ((129 / 64 : ℝ) * mean) ^ 2 ≤
      figureOneExecutableMomentSlack q / 8 * mean ^ 2 := by
  have hcountR : (1 : ℝ) ≤ count := by exact_mod_cast hcount
  have hcountPos : (0 : ℝ) < count := by exact_mod_cast hcount
  have hfinite0 : 0 ≤ 1 - 1 / (count : ℝ) := by
    rw [sub_nonneg, div_le_one hcountPos]
    exact hcountR
  have hfinite1 : 1 - 1 / (count : ℝ) ≤ 1 := by
    linarith [one_div_nonneg.mpr hcountPos.le]
  have hcoefficient :=
    figureOne_fixedThirdMoment_dependence_le_slack_div_eight q
  have hmeanSq : 0 ≤ mean ^ 2 := sq_nonneg mean
  have hslack0 : 0 ≤ figureOneExecutableMomentSlack q / 8 :=
    div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num)
  calc
    3 * figureOneDependentEpsilon q ^ (1 / 3 : ℝ) *
          (1 - 1 / (count : ℝ)) * ((129 / 64 : ℝ) * mean) ^ 2 =
        (3 * figureOneDependentEpsilon q ^ (1 / 3 : ℝ) *
          (129 / 64 : ℝ) ^ 2) *
            (1 - 1 / (count : ℝ)) * mean ^ 2 := by ring
    _ ≤ (figureOneExecutableMomentSlack q / 8) * 1 * mean ^ 2 := by
      gcongr
    _ = figureOneExecutableMomentSlack q / 8 * mean ^ 2 := by ring

#print axioms fixedRate_thirdMoment_precisionFactor_le
#print axioms scheduleValue_fixedRate_relativeThirdMoment_le_dim_three
#print axioms
  scheduleValue_fixedRate_relativeThirdMoment_le_rational_cube_dim_three
#print axioms
  scheduleValue_fixedRate_thirdMoment_le_rational_mean_cube_dim_three
#print axioms four_le_figureOneDependentPhaseCount
#print axioms figureOneDependentAlpha_ge_4096
#print axioms figureOne_fixedThirdMoment_dependence_le_slack_div_eight
#print axioms
  figureOne_fixedThirdMoment_average_dependence_le_slack_div_eight

end ArlibCommunity.Algorithms.CV18
