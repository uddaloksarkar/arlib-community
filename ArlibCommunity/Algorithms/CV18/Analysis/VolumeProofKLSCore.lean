import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedyToTarget
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.KLS97Sharp

/-!
# KLS97 homothetic-core estimates used by CV18

This module follows KLS97 Theorem 4.16, the result cited in CV18's
speedy-to-target argument.  The first lemmas formalize its key separation
geometry: if `K` contains the unit ball, then `c • K` is at distance at least
`a - c` from the complement of `a • K`.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-- A ball of radius `a-c` around `c y` lies in the enlarged homothet
`a • K`.  This is the tangent-plane separation used in KLS97 Theorem 4.16. -/
theorem ball_smul_subset_outer_smul_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c a : ℝ} (hc0 : 0 ≤ c) (hca : c < a) :
    ∀ y ∈ K, ball (c • y) (a - c) ⊆ a • K := by
  intro y hy z hz
  have ha0 : 0 < a := lt_of_le_of_lt hc0 hca
  have hac0 : 0 < a - c := sub_pos.mpr hca
  let w : EuclideanSpace ℝ (Fin n) := (a - c)⁻¹ • (z - c • y)
  have hw : w ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hac0)]
    rw [mem_ball, dist_eq_norm] at hz
    calc
      (a - c)⁻¹ * ‖z - c • y‖ < (a - c)⁻¹ * (a - c) :=
        mul_lt_mul_of_pos_left hz (inv_pos.mpr hac0)
      _ = 1 := inv_mul_cancel₀ hac0.ne'
  have hcoeff0 : 0 ≤ c / a := div_nonneg hc0 ha0.le
  have hcoeff1 : 0 ≤ (a - c) / a := div_nonneg hac0.le ha0.le
  have hsum : c / a + (a - c) / a = 1 := by field_simp; ring
  have hk : (c / a) • y + ((a - c) / a) • w ∈ K :=
    hKc hy (hball hw) hcoeff0 hcoeff1 hsum
  refine ⟨(c / a) • y + ((a - c) / a) • w, hk, ?_⟩
  dsimp [w]
  have hca_mul : a * (c / a) = c := by field_simp
  have hac_scale : a * ((a - c) / a) = a - c := by field_simp
  rw [smul_add, smul_smul, smul_smul, hca_mul, hac_scale, smul_smul,
    mul_inv_cancel₀ hac0.ne', one_smul]
  abel

/-- Points outside `a • K` are at least `a-c` away from the inner core
`c • K`. -/
theorem sub_le_infDist_smul_of_not_mem_outer_smul_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c a : ℝ} (hc0 : 0 ≤ c) (hca : c < a)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∉ a • K) :
    a - c ≤ Metric.infDist z (c • K) := by
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (Metric.mem_ball_self one_pos)
  have hcoreNonempty : (c • K).Nonempty := ⟨c • 0, ⟨0, hzero, rfl⟩⟩
  rw [Metric.le_infDist hcoreNonempty]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  by_contra hdist
  have hzball : z ∈ ball (c • y) (a - c) := by
    rw [mem_ball]
    exact lt_of_not_ge hdist
  exact hz (ball_smul_subset_outer_smul_cv18 hKc hball hc0 hca y hy hzball)

/-- The sharp cap estimate on the inner core, with the KLS97 separation
inserted into the Gaussian exponent. -/
theorem volume_core_inter_closedBall_le_exp_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hKcl : IsClosed K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c a delta : ℝ} (hc0 : 0 < c) (hca : c < a) (hdelta : 0 < delta)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∉ a • K) :
    volume (c • K ∩ closedBall z delta) ≤
      ENNReal.ofReal
          (Real.exp (-((n : ℝ) * (a - c) ^ 2 / (2 * delta ^ 2)))) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (Metric.mem_ball_self one_pos)
  have hcoreNonempty : (c • K).Nonempty := ⟨c • 0, ⟨0, hzero, rfl⟩⟩
  have hsep : a - c ≤ Metric.infDist z (c • K) :=
    sub_le_infDist_smul_of_not_mem_outer_smul_cv18
      hKc hball hc0.le hca hz
  have hzcore : z ∉ c • K := by
    intro hzmem
    rw [Metric.infDist_zero_of_mem hzmem] at hsep
    linarith
  have hcap := Arlib.volume_inter_closedBall_le_sqrt
    (hKc.smul c)
    ((isClosedMap_smul_of_ne_zero hc0.ne') K hKcl)
    hcoreNonempty hzcore delta
  have hpow := Arlib.sqrt_pow_le_gaussian_exp
    (n := n) (t := delta) (h := Metric.infDist z (c • K)) hdelta
  have hdist0 : 0 ≤ Metric.infDist z (c • K) := Metric.infDist_nonneg
  have hac0 : 0 ≤ a - c := sub_nonneg.mpr hca.le
  have hsquares : (a - c) ^ 2 ≤ Metric.infDist z (c • K) ^ 2 :=
    (sq_le_sq₀ hac0 hdist0).2 hsep
  have hexp :
      Real.exp (-((n : ℝ) * Metric.infDist z (c • K) ^ 2 /
          (2 * delta ^ 2))) ≤
        Real.exp (-((n : ℝ) * (a - c) ^ 2 / (2 * delta ^ 2))) := by
    apply Real.exp_le_exp.mpr
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hden : 0 < 2 * delta ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsquares hn0
    exact neg_le_neg (div_le_div_of_nonneg_right hmul hden.le)
  calc
    volume (c • K ∩ closedBall z delta) ≤
        ENNReal.ofReal
            (Real.sqrt (delta ^ 2 - Metric.infDist z (c • K) ^ 2) ^ n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := hcap
    _ ≤ ENNReal.ofReal
          (Real.exp (-((n : ℝ) * Metric.infDist z (c • K) ^ 2 /
            (2 * delta ^ 2))) * delta ^ n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      gcongr
    _ ≤ ENNReal.ofReal
          (Real.exp (-((n : ℝ) * (a - c) ^ 2 / (2 * delta ^ 2))) *
            delta ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      gcongr
    _ = ENNReal.ofReal
          (Real.exp (-((n : ℝ) * (a - c) ^ 2 / (2 * delta ^ 2)))) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
        MeasureTheory.Measure.addHaar_closedBall volume _ hdelta.le,
        finrank_euclideanSpace_fin]
      ring

end Arlib.MarkovChains
