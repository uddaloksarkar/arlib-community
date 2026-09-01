import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAverageConductance
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.Rejection

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-- Conditioning is unchanged by multiplication by a finite positive scalar. -/
theorem condOn_smul_cv18 {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {S : Set Omega} (hS : MeasurableSet S)
    {a : ENNReal} (ha0 : a ≠ 0) (hatop : a ≠ ⊤) :
    Arlib.condOn (a • mu) S = Arlib.condOn mu S := by
  ext T hT
  rw [Arlib.condOn_apply _ hS hT, Arlib.condOn_apply _ hS hT,
    Measure.smul_apply, Measure.smul_apply]
  change a * mu (T ∩ S) / (a * mu S) = mu (T ∩ S) / mu S
  exact ENNReal.mul_div_mul_left _ _ ha0 hatop

/-- On a homothetic core on which every proposal ball stays inside `K`, the
speedy stationary measure is exactly the ordinary restricted Gaussian. -/
theorem ellGaussianMeasure_restrict_smul_eq_gaussian_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta variance : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hdelta : 0 < delta) (hdelta_c : delta ≤ 1 - c) :
    (ellGaussianMeasure K delta variance).restrict (c • K) =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight variance)).restrict (c • K) := by
  have hcore : MeasurableSet (c • K) :=
    measurableSet_smul_set_cv18 hK hc0.ne'
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (Metric.mem_ball_self one_pos)
  have hsub : c • K ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKc.smul_mem_of_zero_mem hzero hx ⟨hc0.le, hc1.le⟩
  ext S hS
  rw [Measure.restrict_apply hS, ellGaussianMeasure,
    withDensity_apply _ (hS.inter hcore), Measure.restrict_restrict (hS.inter hcore),
    Measure.restrict_apply hS, withDensity_apply _ (hS.inter hcore)]
  have hset : S ∩ c • K ∩ K = S ∩ c • K :=
    Set.inter_eq_left.2 fun _ hx => hsub hx.2
  rw [hset]
  refine setLIntegral_congr_fun (hS.inter hcore) fun x hx => ?_
  rw [ell_eq_one_on_shrunken_cv18 hKc hball hc0 hc1 hdelta hdelta_c hx.2,
    one_mul]

/-- The standard CV18 core keeps at least half of the ordinary Gaussian mass. -/
theorem half_mul_gaussianWeight_le_standardCore_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {variance : ℝ} (hvariance : 0 < variance) :
    ENNReal.ofReal (1 / 2) * (∫⁻ x in K, gaussianWeight variance x) ≤
      ∫⁻ x in (1 - 1 / (2 * (n : ℝ))) • K, gaussianWeight variance x := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hfrac : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hc0 : 0 < c := by
    dsimp [c]
    have hle : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  have hmono : (∫⁻ x in K, gaussianWeight variance x) ≤
      ∫⁻ x in K, gaussianWeight (variance / c ^ 2) x := by
    refine lintegral_mono fun x => gaussianWeight_mono_variance_cv18
      hvariance ?_ x
    rw [le_div_iff₀ (sq_pos_of_pos hc0)]
    have hcsq : c ^ 2 ≤ 1 := by nlinarith [hc0.le, hc1.le]
    nlinarith [hvariance.le]
  have hhalf : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (c ^ n) :=
    ENNReal.ofReal_le_ofReal (by
      dsimp [c]
      exact half_le_one_sub_inv_two_mul_pow_cv18 hn)
  change ENNReal.ofReal (1 / 2) * (∫⁻ x in K, gaussianWeight variance x) ≤
    ∫⁻ x in c • K, gaussianWeight variance x
  rw [lintegral_gaussianWeight_smul_set_cv18 hK hc0 variance]
  calc
    ENNReal.ofReal (1 / 2) * (∫⁻ x in K, gaussianWeight variance x) ≤
        ENNReal.ofReal (c ^ n) * (∫⁻ x in K, gaussianWeight variance x) := by gcongr
    _ ≤ ENNReal.ofReal (c ^ n) *
        (∫⁻ x in K, gaussianWeight (variance / c ^ 2) x) := by gcongr

/-- A speedy-stationary draw lands in the standard homothetic core with
probability at least one half.  Thus the first rejection loop has constant
expected trial count. -/
theorem half_le_ellGaussianProb_standardCore_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {delta variance : ℝ} (hdelta : 0 < delta)
    (hdelta_n : delta ≤ 1 / (2 * (n : ℝ))) (hvariance : 0 < variance)
    (hmass0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hmasstop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤) :
    ENNReal.ofReal (1 / 2) ≤
      ellGaussianProb K delta variance
        ((1 - 1 / (2 * (n : ℝ))) • K) := by
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hfrac : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hc0 : 0 < c := by
    dsimp [c]
    have hle : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  have hdelta_c : delta ≤ 1 - c := by simpa [c] using hdelta_n
  have hrest := ellGaussianMeasure_restrict_smul_eq_gaussian_cv18
    (variance := variance) hK hKc hball hc0 hc1 hdelta hdelta_c
  have hcore := congrArg
    (fun mu : Measure (EuclideanSpace ℝ (Fin n)) => mu Set.univ) hrest
  simp only [Measure.restrict_apply_univ] at hcore
  have htotal : ellGaussianMeasure K delta variance Set.univ ≤
      ∫⁻ x in K, gaussianWeight variance x := by
    rw [ellGaussianMeasure_univ]
    refine lintegral_mono fun x => ?_
    calc
      ell K delta x * gaussianWeight variance x ≤
          1 * gaussianWeight variance x :=
        mul_le_mul' (ell_le_one K delta x) le_rfl
      _ = gaussianWeight variance x := one_mul _
  have hhalf := half_mul_gaussianWeight_le_standardCore_cv18
    hn hK hvariance
  have hcoreMeas : MeasurableSet (c • K) :=
    measurableSet_smul_set_cv18 hK hc0.ne'
  have hgauss :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight variance)) (c • K) =
        ∫⁻ x in c • K, gaussianWeight variance x := by
    rw [withDensity_apply _ hcoreMeas]
  change ENNReal.ofReal (1 / 2) ≤
    (ellGaussianMeasure K delta variance Set.univ)⁻¹ *
      ellGaussianMeasure K delta variance (c • K)
  rw [← ENNReal.div_eq_inv_mul]
  refine (ENNReal.le_div_iff_mul_le (Or.inl hmass0) (Or.inl hmasstop)).2 ?_
  calc
    ENNReal.ofReal (1 / 2) * ellGaussianMeasure K delta variance Set.univ ≤
        ENNReal.ofReal (1 / 2) * (∫⁻ x in K, gaussianWeight variance x) := by gcongr
    _ ≤ ∫⁻ x in c • K, gaussianWeight variance x := by simpa [c] using hhalf
    _ = ellGaussianMeasure K delta variance (c • K) :=
      hgauss.symm.trans hcore.symm

/-- Consequently, rejecting speedy-stationary samples until they land in the
homothetic core gives exactly the ordinary Gaussian conditioned on that core. -/
theorem condOn_ellGaussianMeasure_smul_eq_gaussian_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta variance : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hdelta : 0 < delta) (hdelta_c : delta ≤ 1 - c) :
    Arlib.condOn (ellGaussianMeasure K delta variance) (c • K) =
      Arlib.condOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight variance)) (c • K) := by
  have hrest := ellGaussianMeasure_restrict_smul_eq_gaussian_cv18
    (variance := variance) hK hKc hball hc0 hc1 hdelta hdelta_c
  have hmass := congrArg
    (fun mu : Measure (EuclideanSpace ℝ (Fin n)) => mu Set.univ) hrest
  simp only [Measure.restrict_apply_univ] at hmass
  rw [Arlib.condOn_def, Arlib.condOn_def, hmass, hrest]

/-- The same exact rejection identity for the normalized speedy stationary
law used by the mixing theorem. -/
theorem condOn_ellGaussianProb_smul_eq_gaussian_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {c delta variance : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hdelta : 0 < delta) (hdelta_c : delta ≤ 1 - c)
    (hmass0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hmasstop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤) :
    Arlib.condOn (ellGaussianProb K delta variance) (c • K) =
      Arlib.condOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight variance)) (c • K) := by
  rw [ellGaussianProb, condOn_smul_cv18 _
    (measurableSet_smul_set_cv18 hK hc0.ne')
      (ENNReal.inv_ne_zero.mpr hmasstop) (ENNReal.inv_ne_top.mpr hmass0)]
  exact condOn_ellGaussianMeasure_smul_eq_gaussian_cv18
    hK hKc hball hc0 hc1 hdelta hdelta_c

/-- Scaling a Gaussian conditioned on `c • K` back to `K` divides its
variance by `c^2`.  The Jacobian cancels in the two conditional masses. -/
theorem map_condOn_gaussian_smul_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {c variance : ℝ} (hc0 : 0 < c) :
    (Arlib.condOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight variance)) (c • K)).map
        (fun x => c⁻¹ • x) =
      Arlib.condOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight (variance / c ^ 2))) K := by
  have hc : c ≠ 0 := hc0.ne'
  have hcore : MeasurableSet (c • K) := measurableSet_smul_set_cv18 hK hc
  have hmap : Measurable (fun x : EuclideanSpace ℝ (Fin n) => c⁻¹ • x) :=
    (continuous_const_smul _).measurable
  ext T hT
  rw [Measure.map_apply hmap hT,
    Arlib.condOn_apply _ hcore (hT.preimage hmap),
    Arlib.condOn_apply _ hK hT]
  have hpre :
      (fun x : EuclideanSpace ℝ (Fin n) => c⁻¹ • x) ⁻¹' T ∩ c • K =
        c • (T ∩ K) := by
    ext x
    constructor
    · rintro ⟨hxT, y, hyK, rfl⟩
      refine ⟨y, ⟨?_, hyK⟩, rfl⟩
      simpa [smul_smul, inv_mul_cancel₀ hc] using hxT
    · rintro ⟨y, ⟨hyT, hyK⟩, rfl⟩
      refine ⟨?_, ⟨y, hyK, rfl⟩⟩
      simpa [smul_smul, inv_mul_cancel₀ hc] using hyT
  rw [hpre]
  rw [withDensity_apply _ (measurableSet_smul_set_cv18 (hT.inter hK) hc),
    withDensity_apply _ hcore,
    withDensity_apply _ (hT.inter hK), withDensity_apply _ hK]
  rw [lintegral_gaussianWeight_smul_set_cv18 (hT.inter hK) hc0 variance,
    lintegral_gaussianWeight_smul_set_cv18 hK hc0 variance]
  exact ENNReal.mul_div_mul_left _ _
    (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hc0 n))
    ENNReal.ofReal_ne_top

/-- Acceptance probability used after scaling the core back to `K`. -/
noncomputable def gaussianScaleAcceptance (variance c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ENNReal :=
  gaussianWeight variance x / gaussianWeight (variance / c ^ 2) x

theorem measurable_gaussianScaleAcceptance (variance c : ℝ) :
    Measurable (gaussianScaleAcceptance (n := n) variance c) := by
  exact (measurable_gaussianWeight variance).div
    (measurable_gaussianWeight (variance / c ^ 2))

theorem gaussianWeight_mul_gaussianScaleAcceptance (variance c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianWeight (variance / c ^ 2) x *
        gaussianScaleAcceptance variance c x = gaussianWeight variance x := by
  unfold gaussianScaleAcceptance
  rw [mul_comm, ENNReal.div_mul_cancel
    (gaussianWeight_ne_zero (variance / c ^ 2) x)
    (gaussianWeight_ne_top (variance / c ^ 2) x)]

theorem gaussianScaleAcceptance_le_one {variance c : ℝ}
    (hvariance : 0 < variance) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianScaleAcceptance variance c x ≤ 1 := by
  have hc2pos : 0 < c ^ 2 := sq_pos_of_pos hc0
  have hc2le : c ^ 2 ≤ 1 := by nlinarith
  have hvar : variance ≤ variance / c ^ 2 := by
    rw [le_div_iff₀ hc2pos]
    nlinarith [hvariance.le]
  unfold gaussianScaleAcceptance
  rw [ENNReal.div_le_iff
    (gaussianWeight_ne_zero (variance / c ^ 2) x)
    (gaussianWeight_ne_top (variance / c ^ 2) x)]
  simpa using gaussianWeight_mono_variance_cv18 hvariance hvar x

/-- On CV18's phase truncation `‖x‖ ≤ 4 * sqrt(variance*n)`, the second
rejection accepts with probability at least `exp (-8)`, an absolute constant. -/
theorem exp_neg_eight_le_gaussianScaleAcceptance_standardCore_cv18
    (hn : 1 ≤ n) {variance : ℝ} (hvariance : 0 < variance)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ ^ 2 ≤ 16 * variance * (n : ℝ)) :
    ENNReal.ofReal (Real.exp (-8)) ≤
      gaussianScaleAcceptance variance (1 - 1 / (2 * (n : ℝ))) x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnRone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hc0 : 0 < c := by
    dsimp [c]
    rw [sub_pos, div_lt_one (by positivity)]
    nlinarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have : 0 ≤ 1 / (2 * (n : ℝ)) := by positivity
    linarith
  have hc2pos : 0 < c ^ 2 := sq_pos_of_pos hc0
  have hscalePos : 0 < variance / c ^ 2 := div_pos hvariance hc2pos
  have hcLoss : (n : ℝ) * (1 - c ^ 2) ≤ 1 := by
    dsimp [c]
    field_simp
    nlinarith [sq_nonneg (n : ℝ)]
  have hx0 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hcLoss0 : 0 ≤ 1 - c ^ 2 := by nlinarith [hc0.le, hc1]
  have hloss : (1 - c ^ 2) * ‖x‖ ^ 2 ≤ 16 * variance := by
    have h1 := mul_le_mul_of_nonneg_right hcLoss hx0
    have h2 := hx
    nlinarith [mul_nonneg hcLoss0 hx0]
  unfold gaussianScaleAcceptance gaussianWeight gaussianWeightReal
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)))
    (Or.inl ENNReal.ofReal_ne_top)]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hexponent :
      -(8 : ℝ) + -(‖x‖ ^ 2 / (2 * (variance / c ^ 2))) ≤
        -(‖x‖ ^ 2 / (2 * variance)) := by
    have hratio : (1 - c ^ 2) * ‖x‖ ^ 2 / (2 * variance) ≤ 8 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hid :
        ‖x‖ ^ 2 / (2 * variance) - ‖x‖ ^ 2 / (2 * (variance / c ^ 2)) =
          (1 - c ^ 2) * ‖x‖ ^ 2 / (2 * variance) := by
      field_simp
    linarith
  dsimp [c] at hexponent ⊢
  convert hexponent using 1 <;> ring

/-- Variable-probability rejection after the scaling step has exactly the
desired unnormalised Gaussian law on `K`. -/
theorem gaussianScaleAcceptance_withDensity_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (variance c : ℝ) :
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (variance / c ^ 2))).restrict K).withDensity
          (gaussianScaleAcceptance variance c) =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight variance)).restrict K := by
  rw [restrict_withDensity hK, ← withDensity_mul _
    (measurable_gaussianWeight (variance / c ^ 2))
    (measurable_gaussianScaleAcceptance variance c)]
  have hfun :
      (fun x : EuclideanSpace ℝ (Fin n) =>
        gaussianWeight (variance / c ^ 2) x *
          gaussianScaleAcceptance variance c x) =
        (fun x => gaussianWeight variance x) := by
    funext x
    exact gaussianWeight_mul_gaussianScaleAcceptance variance c x
  change (volume.restrict K).withDensity
      (fun x : EuclideanSpace ℝ (Fin n) =>
        gaussianWeight (variance / c ^ 2) x *
          gaussianScaleAcceptance variance c x) = _
  rw [hfun, ← restrict_withDensity hK]

/-- The second rejection has average acceptance at least one half on every
convex body containing the origin; no outer-radius hypothesis is needed. -/
theorem half_mul_scaledGaussianMass_le_gaussianMass_standardCore_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) (variance : ℝ) :
    ENNReal.ofReal (1 / 2) *
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight
            (variance / (1 - 1 / (2 * (n : ℝ))) ^ 2))) K ≤
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight variance)) K := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hfrac : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hc0 : 0 < c := by
    dsimp [c]
    have hle : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  have hsub : c • K ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKc.smul_mem_of_zero_mem hzero hx ⟨hc0.le, hc1.le⟩
  have hhalf : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (c ^ n) :=
    ENNReal.ofReal_le_ofReal (by
      dsimp [c]
      exact half_le_one_sub_inv_two_mul_pow_cv18 hn)
  rw [withDensity_apply _ hK, withDensity_apply _ hK]
  change ENNReal.ofReal (1 / 2) *
      (∫⁻ x in K, gaussianWeight (variance / c ^ 2) x) ≤
    ∫⁻ x in K, gaussianWeight variance x
  calc
    ENNReal.ofReal (1 / 2) *
          (∫⁻ x in K, gaussianWeight (variance / c ^ 2) x) ≤
        ENNReal.ofReal (c ^ n) *
          (∫⁻ x in K, gaussianWeight (variance / c ^ 2) x) := by gcongr
    _ = ∫⁻ x in c • K, gaussianWeight variance x :=
      (lintegral_gaussianWeight_smul_set_cv18 hK hc0 variance).symm
    _ ≤ ∫⁻ x in K, gaussianWeight variance x :=
      lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

/-- Reweighting the normalized scaled proposal by the executable acceptance
probability gives the target restriction, divided by the proposal mass. -/
theorem condOn_gaussian_withDensity_scaleAcceptance_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (variance c : ℝ) :
    (Arlib.condOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (variance / c ^ 2))) K).withDensity
          (gaussianScaleAcceptance variance c) =
      ((((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (variance / c ^ 2))) K)⁻¹) •
        (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight variance)).restrict K) := by
  rw [Arlib.condOn_def, withDensity_smul_measure,
    gaussianScaleAcceptance_withDensity_cv18 hK variance c]

/-- Hence the normalized scaled proposal accepts with probability at least
one half on the whole convex body. -/
theorem half_le_condOn_gaussian_scaleAcceptance_mass_standardCore_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) {variance : ℝ}
    (hprop0 :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight
          (variance / (1 - 1 / (2 * (n : ℝ))) ^ 2))) K ≠ 0)
    (hproptop :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight
          (variance / (1 - 1 / (2 * (n : ℝ))) ^ 2))) K ≠ ⊤) :
    ENNReal.ofReal (1 / 2) ≤
      (Arlib.condOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight
            (variance / (1 - 1 / (2 * (n : ℝ))) ^ 2))) K).withDensity
        (gaussianScaleAcceptance variance (1 - 1 / (2 * (n : ℝ)))) Set.univ := by
  rw [condOn_gaussian_withDensity_scaleAcceptance_cv18 hK,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    ← ENNReal.div_eq_inv_mul]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hprop0) (Or.inl hproptop)).2
    (half_mul_scaledGaussianMass_le_gaussianMass_standardCore_cv18
      hn hK hKc hzero variance)

end Arlib.MarkovChains
