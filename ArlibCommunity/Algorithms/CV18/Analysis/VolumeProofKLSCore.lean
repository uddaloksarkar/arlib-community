import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedyToTarget
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAverageConductanceLV
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

/-- Closed-ball form of the homothetic inclusion, used for distance
sublevel sets. -/
theorem closedBall_smul_subset_outer_smul_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c a : ℝ} (hc0 : 0 ≤ c) (hca : c < a) :
    ∀ y ∈ K, closedBall (c • y) (a - c) ⊆ a • K := by
  intro y hy z hz
  have ha0 : 0 < a := lt_of_le_of_lt hc0 hca
  have hac0 : 0 < a - c := sub_pos.mpr hca
  let w : EuclideanSpace ℝ (Fin n) := (a - c)⁻¹ • (z - c • y)
  have hw : w ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hac0)]
    rw [mem_closedBall, dist_eq_norm] at hz
    calc
      (a - c)⁻¹ * ‖z - c • y‖ ≤ (a - c)⁻¹ * (a - c) :=
        mul_le_mul_of_nonneg_left hz (inv_pos.mpr hac0).le
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

/-- Sharp spherical-cap bound expressed at the exact distance from a closed
convex body. -/
theorem volume_inter_closedBall_le_gaussian_infDist_cv18
    {L : Set (EuclideanSpace ℝ (Fin n))} (hLc : Convex ℝ L)
    (hLcl : IsClosed L) (hLne : L.Nonempty)
    {delta : ℝ} (hdelta : 0 < delta)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∉ L) :
    volume (L ∩ closedBall z delta) ≤
      ENNReal.ofReal
          (Real.exp (-((n : ℝ) * Metric.infDist z L ^ 2 /
            (2 * delta ^ 2)))) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
  have hcap := Arlib.volume_inter_closedBall_le_sqrt
    hLc hLcl hLne hz delta
  have hpow := Arlib.sqrt_pow_le_gaussian_exp
    (n := n) (t := delta) (h := Metric.infDist z L) hdelta
  calc
    volume (L ∩ closedBall z delta) ≤
        ENNReal.ofReal
            (Real.sqrt (delta ^ 2 - Metric.infDist z L ^ 2) ^ n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := hcap
    _ ≤ ENNReal.ofReal
          (Real.exp (-((n : ℝ) * Metric.infDist z L ^ 2 /
            (2 * delta ^ 2))) * delta ^ n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      gcongr
    _ = ENNReal.ofReal
          (Real.exp (-((n : ℝ) * Metric.infDist z L ^ 2 /
            (2 * delta ^ 2)))) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
        MeasureTheory.Measure.addHaar_closedBall volume _ hdelta.le,
        finrank_euclideanSpace_fin]
      ring

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

/-- Tonelli swap for two different inside/outside bodies.  This is the exact
double-integral identity needed for the KLS core `cK` against the complement
of the original body `K`. -/
theorem lintegral_sdiff_eq_lintegral_inter_twoSets_cv18
    (A B : Set (EuclideanSpace ℝ (Fin n))) (delta : ℝ) :
    ∫⁻ x in A, volume (closedBall x delta \ B) =
      ∫⁻ y in Bᶜ, volume (A ∩ closedBall y delta) := by
  classical
  let S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    {p | dist p.1 p.2 ≤ delta}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ENNReal :=
    fun x y => S.indicator 1 (x, y)
  have hmeas : Measurable (Function.uncurry f) := by
    dsimp [f]
    exact measurable_one.indicator hS
  have hx : ∀ x : EuclideanSpace ℝ (Fin n),
      ∫⁻ y in Bᶜ, f x y = volume (closedBall x delta \ B) := by
    intro x
    have hrw : ∀ y, f x y =
        (closedBall x delta).indicator
          (1 : EuclideanSpace ℝ (Fin n) → ENNReal) y := by
      intro y
      simp only [f, Set.indicator_apply, S, Set.mem_ofPred_eq,
        mem_closedBall, Pi.one_apply]
      rw [dist_comm y x]
    simp_rw [hrw]
    rw [lintegral_indicator_one measurableSet_closedBall,
      Measure.restrict_apply measurableSet_closedBall, Set.sdiff_eq]
  have hy : ∀ y : EuclideanSpace ℝ (Fin n),
      ∫⁻ x in A, f x y = volume (A ∩ closedBall y delta) := by
    intro y
    have hrw : ∀ x, f x y =
        (closedBall y delta).indicator
          (1 : EuclideanSpace ℝ (Fin n) → ENNReal) x := by
      intro x
      simp only [f, Set.indicator_apply, S, Set.mem_ofPred_eq,
        mem_closedBall, Pi.one_apply]
    simp_rw [hrw]
    rw [lintegral_indicator_one measurableSet_closedBall,
      Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
  have hswap := lintegral_lintegral_swap (μ := volume.restrict A)
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Bᶜ)
      hmeas.aemeasurable
  simp_rw [hx, hy] at hswap
  exact hswap

/-- Layer cake for an exponential of distance, restricted to an arbitrary
measurable-domain measure. -/
theorem layercake_infDist_on_cv18
    (A K : Set (EuclideanSpace ℝ (Fin n))) {rate : ℝ} (hrate : 0 < rate)
    (shift : ℝ) :
    ∫⁻ y in A,
        ENNReal.ofReal
          (Real.exp (shift - rate * Metric.infDist y K)) =
      ∫⁻ h in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (rate * Real.exp (shift - rate * h)) *
          volume (A ∩ {y | Metric.infDist y K ≤ h}) := by
  classical
  have hinfc : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      Metric.infDist y K := Metric.continuous_infDist_pt K
  let T : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
    {p | Metric.infDist p.1 K ≤ p.2}
  have hT : MeasurableSet T :=
    measurableSet_le (hinfc.measurable.comp measurable_fst) measurable_snd
  let F : EuclideanSpace ℝ (Fin n) → ℝ → ENNReal :=
    fun y h => T.indicator
      (fun p => ENNReal.ofReal
        (rate * Real.exp (shift - rate * p.2))) (y, h)
  have hmeas : Measurable (Function.uncurry F) := by
    dsimp [F]
    refine Measurable.indicator ?_ hT
    exact ENNReal.measurable_ofReal.comp
      (((measurable_const.mul measurable_snd).const_sub shift).exp.const_mul rate)
  have hy : ∀ y : EuclideanSpace ℝ (Fin n),
      ∫⁻ h in Set.Ioi (0 : ℝ), F y h =
        ENNReal.ofReal
          (Real.exp (shift - rate * Metric.infDist y K)) := by
    intro y
    have hd0 : 0 ≤ Metric.infDist y K := Metric.infDist_nonneg
    have hrw : ∀ h : ℝ, F y h =
        (Set.Ici (Metric.infDist y K)).indicator
          (fun h => ENNReal.ofReal
            (rate * Real.exp (shift - rate * h))) h := by
      intro h
      simp only [F, Set.indicator_apply, T, Set.mem_ofPred_eq, Set.mem_Ici]
    simp_rw [hrw]
    rw [lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    have hae :
        (Set.Ici (Metric.infDist y K) ∩ Set.Ioi (0 : ℝ) : Set ℝ) =ᵐ[volume]
          Set.Ioi (Metric.infDist y K) := by
      refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
      · refine measure_mono_null ?_
          (measure_singleton (Metric.infDist y K))
        rintro x ⟨⟨hx1, _⟩, hx2⟩
        simp only [Set.mem_Ioi, not_lt] at hx2
        exact le_antisymm hx2 hx1
      · have hsub : Set.Ioi (Metric.infDist y K) ⊆
            Set.Ici (Metric.infDist y K) ∩ Set.Ioi (0 : ℝ) := by
          intro x hx
          exact ⟨Set.mem_Ici.mpr hx.le,
            Set.mem_Ioi.mpr (lt_of_le_of_lt hd0 hx)⟩
        rw [Set.sdiff_eq_empty.mpr hsub, measure_empty]
    rw [MeasureTheory.setLIntegral_congr hae]
    exact Arlib.lintegral_Ioi_exp_neg hrate shift _
  have hx : ∀ h : ℝ, ∫⁻ y in A, F y h =
      ENNReal.ofReal (rate * Real.exp (shift - rate * h)) *
        volume (A ∩ {y | Metric.infDist y K ≤ h}) := by
    intro h
    have hSm : MeasurableSet
        {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h} :=
      measurableSet_le hinfc.measurable measurable_const
    have hrw : ∀ y : EuclideanSpace ℝ (Fin n), F y h =
        {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K ≤ h}.indicator
          (fun _ => ENNReal.ofReal
            (rate * Real.exp (shift - rate * h))) y := by
      intro y
      simp only [F, Set.indicator_apply, T, Set.mem_ofPred_eq]
    simp_rw [hrw]
    rw [lintegral_indicator hSm, setLIntegral_const,
      Measure.restrict_apply hSm, Set.inter_comm]
  have hswap := lintegral_lintegral_swap
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict A)
    (ν := (volume : Measure ℝ).restrict (Set.Ioi 0)) hmeas.aemeasurable
  simp_rw [hy, hx] at hswap
  exact hswap

/-- Distance shells of the inner homothet outside `K` fit in the elementary
homothetic volume shell `(c+h)K \ K`. -/
theorem volume_compl_inter_infDist_core_le_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c h : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hh : 1 - c ≤ h) :
    volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h}) ≤
      ENNReal.ofReal ((c + h) ^ n - 1) * volume K := by
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (Metric.mem_closedBall_self zero_le_one)
  have hcoreNonempty : (c • K).Nonempty := ⟨c • 0, ⟨0, hzero, rfl⟩⟩
  have hcoreClosed : IsClosed (c • K) :=
    (isClosedMap_smul_of_ne_zero hc0.ne') K hKcl
  have hh0 : 0 < h := (sub_pos.mpr hc1).trans_le hh
  have hca : c < c + h := by linarith
  have ha1 : 1 ≤ c + h := by linarith
  have ha0 : 0 ≤ c + h := zero_le_one.trans ha1
  have houter :
      Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h} ⊆ (c + h) • K \ K := by
    rintro y ⟨hyK, hyd⟩
    obtain ⟨x, hxcore, hxy⟩ :=
      hcoreClosed.exists_infDist_eq_dist hcoreNonempty y
    have hyball : y ∈ closedBall x h := by
      rw [mem_closedBall, ← hxy]
      exact hyd
    obtain ⟨z, hz, rfl⟩ := hxcore
    have hyouter := closedBall_smul_subset_outer_smul_cv18
      hKc hball hc0.le hca z hz
    exact ⟨hyouter (by simpa only [add_sub_cancel_left] using hyball), hyK⟩
  have hKouter : K ⊆ (c + h) • K := by
    intro x hx
    refine ⟨(c + h)⁻¹ • x, ?_, ?_⟩
    · exact hKc.smul_mem_of_zero_mem hzero hx
        ⟨by positivity, by rw [inv_le_one₀ (by positivity)]; exact ha1⟩
    · change (c + h) • ((c + h)⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ (by positivity : c + h ≠ 0), one_smul]
  calc
    volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h}) ≤
        volume ((c + h) • K \ K) := measure_mono houter
    _ = volume ((c + h) • K) - volume K :=
      measure_sdiff hKouter hKcl.measurableSet.nullMeasurableSet hKfin
    _ = ENNReal.ofReal ((c + h) ^ n) * volume K - volume K := by
      rw [Arlib.volume_smul_euclidean ha0]
    _ = (ENNReal.ofReal ((c + h) ^ n) - 1) * volume K := by
      rw [ENNReal.sub_mul (fun _ _ => hKfin), one_mul]
    _ = ENNReal.ofReal ((c + h) ^ n - 1) * volume K := by
      congr 1
      calc
        ENNReal.ofReal ((c + h) ^ n) - 1 =
            ENNReal.ofReal ((c + h) ^ n) - ENNReal.ofReal 1 := by norm_num
        _ = ENNReal.ofReal ((c + h) ^ n - 1) :=
          (ENNReal.ofReal_sub _ zero_le_one).symm

/-- The explicit one-dimensional integral at the heart of KLS97 Theorem
4.16.  When `rate ≥ 2n`, the homothetic shell growth is absorbed by half of
the exponential decay. -/
theorem lintegral_kls_exp_majorant_le_cv18
    {dim rate h0 : ℝ} (hdim : 0 < dim) (hrate : 2 * dim ≤ rate) :
    ∫⁻ h in Set.Ioi h0,
        ENNReal.ofReal
          (rate * Real.exp (-rate * h) * Real.exp (dim * (h - h0))) ≤
      ENNReal.ofReal (2 * Real.exp (-rate * h0)) := by
  let decay : ℝ := rate - dim
  have hrate0 : 0 < rate := lt_of_lt_of_le (by linarith) hrate
  have hdecay : 0 < decay := by dsimp [decay]; linarith
  have hratio : rate / decay ≤ 2 := by
    rw [div_le_iff₀ hdecay]
    dsimp [decay]
    linarith
  have hfun : (fun h : ℝ => ENNReal.ofReal
        (rate * Real.exp (-rate * h) * Real.exp (dim * (h - h0)))) =
      fun h => ENNReal.ofReal (rate / decay) *
        ENNReal.ofReal
          (decay * Real.exp (-dim * h0 - decay * h)) := by
    funext h
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hexponent : -rate * h + dim * (h - h0) =
        -dim * h0 - decay * h := by
      dsimp [decay]
      ring
    calc
      rate * Real.exp (-rate * h) * Real.exp (dim * (h - h0)) =
          rate * Real.exp (-rate * h + dim * (h - h0)) := by
        rw [Real.exp_add]
        ring
      _ = rate * Real.exp (-dim * h0 - decay * h) := by rw [hexponent]
      _ = rate / decay *
          (decay * Real.exp (-dim * h0 - decay * h)) := by
        field_simp
  rw [hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    Arlib.lintegral_Ioi_exp_neg hdecay (-dim * h0) h0]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hexpEq : Real.exp (-dim * h0 - decay * h0) =
      Real.exp (-rate * h0) := by
    congr 1
    dsimp [decay]
    ring
  rw [hexpEq]
  exact mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le

/-- KLS97's exponential distance integral over the complement of `K`, after
the homothetic shell estimate and the one-dimensional calculation. -/
theorem lintegral_exp_neg_infDist_core_le_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c rate : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hrate : 2 * (n : ℝ) ≤ rate) :
    ∫⁻ y in Kᶜ,
        ENNReal.ofReal (Real.exp (-rate * Metric.infDist y (c • K))) ≤
      ENNReal.ofReal (2 * Real.exp (-rate * (1 - c))) * volume K := by
  let h0 : ℝ := 1 - c
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have h0pos : 0 < h0 := by dsimp [h0]; linarith
  have hrate0 : 0 < rate := lt_of_lt_of_le (by positivity : 0 < 2 * (n : ℝ)) hrate
  have hlayer := layercake_infDist_on_cv18
    (n := n) Kᶜ (c • K) hrate0 0
  simp only [zero_sub] at hlayer
  have hlayer' :
      (∫⁻ y in Kᶜ,
        ENNReal.ofReal (Real.exp (-rate * Metric.infDist y (c • K)))) =
        ∫⁻ h in Set.Ioi 0,
          ENNReal.ofReal (rate * Real.exp (-rate * h)) *
            volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h}) := by
    simpa only [neg_mul] using hlayer
  rw [hlayer']
  let major : ℝ → ENNReal := fun h =>
    ENNReal.ofReal
      (rate * Real.exp (-rate * h) * Real.exp ((n : ℝ) * (h - h0))) *
        volume K
  have hmajorMeas : Measurable major := by
    dsimp [major]
    fun_prop
  have hpoint : ∀ h ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal (rate * Real.exp (-rate * h)) *
          volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h}) ≤
        (Set.Ici h0).indicator major h := by
    intro h hh
    by_cases hh0 : h0 ≤ h
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hh0)]
      have hshell := volume_compl_inter_infDist_core_le_cv18
        hKc hKcl hKfin hball hc0 hc1 (by simpa [h0] using hh0)
      have hx0 : 0 ≤ h - h0 := sub_nonneg.mpr hh0
      have hpow : (c + h) ^ n ≤ Real.exp ((n : ℝ) * (h - h0)) := by
        have hone := Real.add_one_le_exp (h - h0)
        have hbase : c + h ≤ Real.exp (h - h0) := by
          have heq : c + h = 1 + (h - h0) := by dsimp [h0]; ring
          rw [heq]
          simpa [add_comm] using hone
        calc
          (c + h) ^ n ≤ Real.exp (h - h0) ^ n :=
            pow_le_pow_left₀ (by linarith) hbase n
          _ = Real.exp ((n : ℝ) * (h - h0)) := by
            rw [← Real.exp_nat_mul]
      have hshellReal : (c + h) ^ n - 1 ≤
          Real.exp ((n : ℝ) * (h - h0)) := by
        linarith [Real.exp_pos ((n : ℝ) * (h - h0))]
      calc
        ENNReal.ofReal (rate * Real.exp (-rate * h)) *
              volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h}) ≤
            ENNReal.ofReal (rate * Real.exp (-rate * h)) *
              (ENNReal.ofReal ((c + h) ^ n - 1) * volume K) := by gcongr
        _ ≤ ENNReal.ofReal (rate * Real.exp (-rate * h)) *
              (ENNReal.ofReal (Real.exp ((n : ℝ) * (h - h0))) * volume K) := by
            gcongr
        _ = major h := by
          dsimp [major]
          repeat' rw [ENNReal.ofReal_mul (by positivity)]
          ac_rfl
    · rw [Set.indicator_of_notMem (by simpa [Set.mem_Ici] using hh0)]
      have hempty : Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h} = ∅ := by
        by_contra hne
        obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
        have hsep := sub_le_infDist_smul_of_not_mem_outer_smul_cv18
          hKc (fun _ hx => hball (Metric.ball_subset_closedBall hx))
          hc0.le hc1 (z := y) (by simpa using hy.1)
        exact hh0 (by dsimp [h0]; exact hsep.trans hy.2)
      rw [hempty, measure_empty, mul_zero]
  calc
    (∫⁻ h in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (rate * Real.exp (-rate * h)) *
          volume (Kᶜ ∩ {y | Metric.infDist y (c • K) ≤ h})) ≤
        ∫⁻ h in Set.Ioi (0 : ℝ), (Set.Ici h0).indicator major h :=
      setLIntegral_mono' measurableSet_Ioi hpoint
    _ = ∫⁻ h in Set.Ioi h0, major h := by
      rw [lintegral_indicator measurableSet_Ici,
        Measure.restrict_restrict measurableSet_Ici]
      have hae : (Set.Ici h0 ∩ Set.Ioi (0 : ℝ) : Set ℝ) =ᵐ[volume]
          Set.Ioi h0 := by
        refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
        · refine measure_mono_null ?_ (measure_singleton h0)
          rintro x ⟨⟨hx1, _⟩, hx2⟩
          simp only [Set.mem_Ioi, not_lt] at hx2
          exact le_antisymm hx2 hx1
        · have hsub : Set.Ioi h0 ⊆ Set.Ici h0 ∩ Set.Ioi (0 : ℝ) := by
            intro x hx
            exact ⟨Set.mem_Ici.mpr hx.le,
              Set.mem_Ioi.mpr (h0pos.trans hx)⟩
          rw [Set.sdiff_eq_empty.mpr hsub, measure_empty]
      exact MeasureTheory.setLIntegral_congr hae
    _ = (∫⁻ h in Set.Ioi h0,
          ENNReal.ofReal
            (rate * Real.exp (-rate * h) *
              Real.exp ((n : ℝ) * (h - h0)))) * volume K := by
      dsimp [major]
      rw [lintegral_mul_const' _ _ hKfin]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-rate * h0)) * volume K := by
      gcongr
      exact lintegral_kls_exp_majorant_le_cv18 hnR hrate
    _ = ENNReal.ofReal (2 * Real.exp (-rate * (1 - c))) * volume K := by
      rfl

/-- KLS97 Theorem 4.16's unweighted core-escape estimate.  The left side is
the total volume of ball-walk proposals from `c K` that leave `K`.  The
condition `4 δ² ≤ 1-c` is exactly what lets the radial exponential dominate
homothetic shell growth. -/
theorem lintegral_core_closedBall_escape_le_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hdelta : 0 < delta)
    (hscale : 4 * delta ^ 2 ≤ 1 - c) :
    ∫⁻ x in c • K, volume (closedBall x delta \ K) ≤
      ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) *
        volume K * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
  let h0 : ℝ := 1 - c
  let rate : ℝ := (n : ℝ) * h0 / (2 * delta ^ 2)
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have h0pos : 0 < h0 := by dsimp [h0]; linarith
  have hden : 0 < 2 * delta ^ 2 := by positivity
  have hrate : 2 * (n : ℝ) ≤ rate := by
    rw [le_div_iff₀ hden]
    dsimp [rate, h0]
    nlinarith
  let V : ENNReal :=
    volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta)
  have hVtop : V ≠ ⊤ := by
    dsimp [V]
    exact measure_closedBall_lt_top.ne
  have hpoint : ∀ y ∈ Kᶜ,
      volume (c • K ∩ closedBall y delta) ≤
        ENNReal.ofReal
            (Real.exp (-rate * Metric.infDist y (c • K))) * V := by
    intro y hy
    have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
      hball (Metric.mem_closedBall_self zero_le_one)
    have hcoreNe : (c • K).Nonempty := ⟨c • 0, ⟨0, hzero, rfl⟩⟩
    have hcoreCl : IsClosed (c • K) :=
      (isClosedMap_smul_of_ne_zero hc0.ne') K hKcl
    have hsep : h0 ≤ Metric.infDist y (c • K) := by
      have hs := sub_le_infDist_smul_of_not_mem_outer_smul_cv18
        hKc (fun _ hx => hball (Metric.ball_subset_closedBall hx))
        hc0.le hc1 (z := y) (by simpa using hy)
      simpa [h0] using hs
    have hycore : y ∉ c • K := by
      intro hymem
      rw [Metric.infDist_zero_of_mem hymem] at hsep
      linarith
    have hcap := volume_inter_closedBall_le_gaussian_infDist_cv18
      (hKc.smul c) hcoreCl hcoreNe hdelta hycore
    have hd0 : 0 ≤ Metric.infDist y (c • K) := Metric.infDist_nonneg
    have hquad : rate * Metric.infDist y (c • K) ≤
        (n : ℝ) * Metric.infDist y (c • K) ^ 2 /
          (2 * delta ^ 2) := by
      dsimp [rate]
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hden.le
      have hsquare : h0 * Metric.infDist y (c • K) ≤
          Metric.infDist y (c • K) ^ 2 := by
        simpa [pow_two] using mul_le_mul_of_nonneg_right hsep hd0
      calc
        (n : ℝ) * h0 * Metric.infDist y (c • K) =
            (n : ℝ) * (h0 * Metric.infDist y (c • K)) := by ring
        _ ≤ (n : ℝ) * Metric.infDist y (c • K) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare hnR.le
    calc
      volume (c • K ∩ closedBall y delta) ≤
          ENNReal.ofReal
              (Real.exp (-((n : ℝ) * Metric.infDist y (c • K) ^ 2 /
                (2 * delta ^ 2)))) * V := hcap
      _ ≤ ENNReal.ofReal
              (Real.exp (-rate * Metric.infDist y (c • K))) * V := by
        gcongr
        simpa only [neg_mul] using neg_le_neg hquad
  rw [lintegral_sdiff_eq_lintegral_inter_twoSets_cv18 (c • K) K delta]
  calc
    (∫⁻ y in Kᶜ, volume (c • K ∩ closedBall y delta)) ≤
        ∫⁻ y in Kᶜ,
          ENNReal.ofReal
              (Real.exp (-rate * Metric.infDist y (c • K))) * V :=
      setLIntegral_mono' hKcl.measurableSet.compl hpoint
    _ = (∫⁻ y in Kᶜ,
          ENNReal.ofReal
            (Real.exp (-rate * Metric.infDist y (c • K)))) * V := by
      rw [lintegral_mul_const' _ _ hVtop]
    _ ≤ (ENNReal.ofReal (2 * Real.exp (-rate * h0)) * volume K) * V := by
      gcongr
      exact lintegral_exp_neg_infDist_core_le_cv18 hn hKc hKcl hKfin
        hball hc0 hc1 hrate
    _ = ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) *
        volume K * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta) := by
      dsimp [rate, h0, V]
      congr 2
      congr 2
      ring

/-- Normalized form of the KLS97 core-escape estimate: the average
ball-walk rejection probability on `c K` is exponentially small. -/
theorem setLIntegral_one_sub_ell_core_le_exp_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKfin : volume K ≠ ⊤)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hdelta : 0 < delta)
    (hscale : 4 * delta ^ 2 ≤ 1 - c) :
    ∫⁻ x in c • K, (1 - ell K delta x) ≤
      ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) * volume K := by
  let _ : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]
      omega)
  let V : ENNReal :=
    volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta)
  have hV0 : V ≠ 0 := by
    dsimp [V]
    exact (Metric.measure_closedBall_pos volume 0 hdelta).ne'
  have hVtop : V ≠ ⊤ := by
    dsimp [V]
    exact measure_closedBall_lt_top.ne
  have hbadm : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      1 - ell K delta x :=
    measurable_const.sub (measurable_ell hKcl.measurableSet delta)
  have hpoint : ∀ x ∈ c • K,
      V * (1 - ell K delta x) ≤ volume (closedBall x delta \ K) := by
    intro x _
    change volume (closedBall 0 delta) * (1 - ell K delta x) ≤ _
    rw [mul_comm, Measure.addHaar_closedBall_eq_addHaar_ball,
      ← volume_ball_eq x delta,
      one_sub_ell_mul_volume_ball_eq hKcl.measurableSet hdelta]
    exact measure_mono fun _ hy =>
      ⟨Metric.ball_subset_closedBall hy.1, hy.2⟩
  apply (ENNReal.mul_le_mul_iff_right hV0 hVtop).1
  rw [← lintegral_const_mul _ hbadm]
  calc
    (∫⁻ x in c • K, V * (1 - ell K delta x)) ≤
        ∫⁻ x in c • K, volume (closedBall x delta \ K) :=
      setLIntegral_mono' ((isClosedMap_smul_of_ne_zero hc0.ne') K hKcl).measurableSet
        hpoint
    _ ≤ ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) * volume K * V :=
      lintegral_core_closedBall_escape_le_cv18 hn hKc hKcl hKfin hball
        hc0 hc1 hdelta hscale
    _ = V * (ENNReal.ofReal
          (2 * Real.exp (-((n : ℝ) * (1 - c) ^ 2 /
            (2 * delta ^ 2)))) * volume K) := by ac_rfl

end Arlib.MarkovChains
