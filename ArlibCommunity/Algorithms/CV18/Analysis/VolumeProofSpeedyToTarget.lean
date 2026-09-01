import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAverageConductance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofTruncation
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisConductance
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.Rejection

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-- Weighting two nearby laws by the same measurable acceptance function
bounded by one cannot increase their setwise total-variation error.  The
resulting measures need not yet be normalized; this is the exact statement
needed before conditioning on a rejection sampler's success event. -/
theorem TVLe.withDensity_le_one_cv18
    {Omega : Type*} [MeasurableSpace Omega]
    {mu nu : Measure Omega} {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    {accept : Omega → ENNReal} (haccept : Measurable accept)
    (haccept_one : ∀ x, accept x ≤ 1) :
    Arlib.TVLe (mu.withDensity accept) (nu.withDensity accept) epsilon := by
  intro S hS
  rw [withDensity_apply _ hS, withDensity_apply _ hS,
    ← lintegral_indicator hS, ← lintegral_indicator hS]
  have hm : Measurable (S.indicator accept) := haccept.indicator hS
  have hle : ∀ x, S.indicator accept x ≤ 1 := by
    intro x
    by_cases hx : x ∈ S
    · simpa [Set.indicator_of_mem hx] using haccept_one x
    · simp [Set.indicator_of_notMem hx]
  exact ⟨lintegral_le_of_tvLe h hm hle,
    lintegral_le_of_tvLe h.symm hm hle⟩

/-- Conditioning two probability laws on the same event amplifies a TV error
by at most twice the reciprocal of a common lower bound on the event mass.
This intentionally exposes the amplification factor: the CV18 acceptance
lemmas provide `p = 1/2`, so a rejection stage costs at most `4 * epsilon`.
-/
theorem TVLe.condOn_cv18
    {Omega : Type*} [MeasurableSpace Omega]
    {mu nu : Measure Omega} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    {epsilon p : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≠ ⊤) {S : Set Omega} (hS : MeasurableSet S)
    (hp0 : p ≠ 0) (hpmu : p ≤ mu S) (hpnu : p ≤ nu S) :
    Arlib.TVLe (Arlib.condOn mu S) (Arlib.condOn nu S)
      (2 * epsilon / p) := by
  have hmutop : mu S ≠ ⊤ := measure_ne_top mu S
  have hnutop : nu S ≠ ⊤ := measure_ne_top nu S
  have hptop : p ≠ ⊤ := ne_top_of_le_ne_top hmutop hpmu
  have hp_pos : 0 < p := bot_lt_iff_ne_bot.2 hp0
  have hmu0 : mu S ≠ 0 := ne_of_gt (hp_pos.trans_le hpmu)
  have hnu0 : nu S ≠ 0 := ne_of_gt (hp_pos.trans_le hpnu)
  let _ : IsProbabilityMeasure (Arlib.condOn mu S) :=
    Arlib.isProbabilityMeasure_condOn mu hmu0 hmutop
  let _ : IsProbabilityMeasure (Arlib.condOn nu S) :=
    Arlib.isProbabilityMeasure_condOn nu hnu0 hnutop
  refine Arlib.tvLe_of_forall_le fun T hT => ?_
  rw [Arlib.condOn_apply mu hS hT, Arlib.condOn_apply nu hS hT]
  have herrorTop : 2 * epsilon / p ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) hepsilon) hp0
  have hleftTop : mu (T ∩ S) / mu S ≠ ⊤ :=
    ENNReal.div_ne_top (measure_ne_top mu _) hmu0
  have hrightTop : nu (T ∩ S) / nu S + 2 * epsilon / p ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (measure_ne_top nu _) hnu0, herrorTop⟩
  apply (ENNReal.toReal_le_toReal hleftTop hrightTop).mp
  rw [ENNReal.toReal_add
    (ENNReal.div_ne_top (measure_ne_top nu _) hnu0) herrorTop,
    ENNReal.toReal_div, ENNReal.toReal_div]
  let a : ℝ := (mu (T ∩ S)).toReal
  let b : ℝ := (nu (T ∩ S)).toReal
  let A : ℝ := (mu S).toReal
  let B : ℝ := (nu S).toReal
  let e : ℝ := epsilon.toReal
  let P : ℝ := p.toReal
  have hPpos : 0 < P := ENNReal.toReal_pos hp0 hptop
  have hPA : P ≤ A := ENNReal.toReal_mono hmutop hpmu
  have hPB : P ≤ B := ENNReal.toReal_mono hnutop hpnu
  have hApos : 0 < A := lt_of_lt_of_le hPpos hPA
  have hBpos : 0 < B := lt_of_lt_of_le hPpos hPB
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  have hbB : b ≤ B := by
    exact measureReal_mono (Set.inter_subset_right)
  have habs := h.abs_measureReal_sub_le hepsilon (hT.inter hS)
  have hABs := h.abs_measureReal_sub_le hepsilon hS
  change |a - b| ≤ e at habs
  change |A - B| ≤ e at hABs
  have hab : a ≤ b + e := by
    rw [abs_sub_le_iff] at habs
    linarith
  have hAB : B - A ≤ e := by
    rw [abs_sub_le_iff] at hABs
    linarith
  have herrorReal : (2 * epsilon / p).toReal = 2 * e / P := by
    simp [e, P, ENNReal.toReal_div, ENNReal.toReal_mul]
  rw [herrorReal]
  change a / A ≤ b / B + 2 * e / P
  calc
    a / A ≤ (b + e) / A := div_le_div_of_nonneg_right hab hApos.le
    _ = b / A + e / A := by ring
    _ ≤ b / B + e / P + e / P := by
      by_cases hBA : B ≤ A
      · have hbdiv : b / A ≤ b / B :=
          div_le_div_of_nonneg_left hb0 hBpos hBA
        have hediv : e / A ≤ e / P :=
          div_le_div_of_nonneg_left he0 hPpos hPA
        calc
          b / A + e / A ≤ b / B + e / P := add_le_add hbdiv hediv
          _ ≤ b / B + e / P + e / P :=
            le_add_of_nonneg_right (div_nonneg he0 hPpos.le)
      · have hABlt : A < B := lt_of_not_ge hBA
        have hdiff0 : 0 ≤ B - A := sub_nonneg.2 hABlt.le
        have hnum : b * (B - A) ≤ B * e :=
          mul_le_mul hbB hAB hdiff0 hBpos.le
        have hdenpos : 0 < A * B := mul_pos hApos hBpos
        have hfrac : b * (B - A) / (A * B) ≤ B * e / (A * B) :=
          div_le_div_of_nonneg_right hnum hdenpos.le
        have hid : b / A - b / B = b * (B - A) / (A * B) := by
          field_simp
        have hcancel : B * e / (A * B) = e / A := by
          field_simp
        have hediv : e / A ≤ e / P :=
          div_le_div_of_nonneg_left he0 hPpos hPA
        rw [hcancel] at hfrac
        have hdiff : b / A - b / B ≤ e / P := by
          rw [hid]
          exact hfrac.trans hediv
        linarith [hediv]
    _ = b / B + 2 * e / P := by ring

/-- TV stability of a complete accept/reject stage.  Weight by the common
acceptance probability and then normalize by conditioning on `univ`.  A
common acceptance-mass floor `p` is the only source of amplification. -/
theorem TVLe.normalize_withDensity_cv18
    {Omega : Type*} [MeasurableSpace Omega]
    {mu nu : Measure Omega} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon p : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≠ ⊤) {accept : Omega → ENNReal}
    (haccept : Measurable accept) (haccept_one : ∀ x, accept x ≤ 1)
    (hp0 : p ≠ 0)
    (hpmu : p ≤ (mu.withDensity accept) Set.univ)
    (hpnu : p ≤ (nu.withDensity accept) Set.univ) :
    Arlib.TVLe
      (Arlib.condOn (mu.withDensity accept) Set.univ)
      (Arlib.condOn (nu.withDensity accept) Set.univ)
      (2 * epsilon / p) := by
  have hmuInt : ∫⁻ x, accept x ∂mu ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact lintegral_le_const (Filter.Eventually.of_forall haccept_one)
  have hnuInt : ∫⁻ x, accept x ∂nu ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact lintegral_le_const (Filter.Eventually.of_forall haccept_one)
  let _ : IsFiniteMeasure (mu.withDensity accept) :=
    isFiniteMeasure_withDensity hmuInt
  let _ : IsFiniteMeasure (nu.withDensity accept) :=
    isFiniteMeasure_withDensity hnuInt
  exact TVLe.condOn_cv18
    (TVLe.withDensity_le_one_cv18 h haccept haccept_one)
    hepsilon MeasurableSet.univ hp0 hpmu hpnu

/-- The CV18 form of rejection stability: when both ideal and approximate
laws accept with probability at least one half, normalization costs at most a
factor four in TV. -/
theorem TVLe.normalize_withDensity_half_cv18
    {Omega : Type*} [MeasurableSpace Omega]
    {mu nu : Measure Omega} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≠ ⊤) {accept : Omega → ENNReal}
    (haccept : Measurable accept) (haccept_one : ∀ x, accept x ≤ 1)
    (hmu : ENNReal.ofReal (1 / 2 : ℝ) ≤
      (mu.withDensity accept) Set.univ)
    (hnu : ENNReal.ofReal (1 / 2 : ℝ) ≤
      (nu.withDensity accept) Set.univ) :
    Arlib.TVLe
      (Arlib.condOn (mu.withDensity accept) Set.univ)
      (Arlib.condOn (nu.withDensity accept) Set.univ)
      (4 * epsilon) := by
  have hbase := TVLe.normalize_withDensity_cv18 h hepsilon haccept haccept_one
    (p := ENNReal.ofReal (1 / 2 : ℝ)) (by norm_num) hmu hnu
  convert hbase using 1
  simp [ENNReal.div_eq_inv_mul]
  ring

/-- Conditioning on a target event of mass at least one half is stable even
when no separate acceptance bound for the approximate law is assumed.  An
incoming error at most `1/4` forces its acceptance mass to be at least `1/4`,
and the normalized laws are within `8 * epsilon`. -/
theorem TVLe.condOn_target_half_cv18
    {Omega : Type*} [MeasurableSpace Omega]
    {mu nu : Measure Omega} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≠ ⊤) (hepsilon_quarter : epsilon ≤ ENNReal.ofReal (1 / 4 : ℝ))
    {S : Set Omega} (hS : MeasurableSet S)
    (hnu : ENNReal.ofReal (1 / 2 : ℝ) ≤ nu S) :
    Arlib.TVLe (Arlib.condOn mu S) (Arlib.condOn nu S) (8 * epsilon) := by
  have hquarter_add : ENNReal.ofReal (1 / 4 : ℝ) + epsilon ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      ENNReal.ofReal (1 / 4 : ℝ) + epsilon ≤
          ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) := by gcongr
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        norm_num
  have hmu_add : ENNReal.ofReal (1 / 4 : ℝ) + epsilon ≤ mu S + epsilon :=
    hquarter_add.trans (hnu.trans (h.right hS))
  have hmu : ENNReal.ofReal (1 / 4 : ℝ) ≤ mu S :=
    ENNReal.le_of_add_le_add_right hepsilon hmu_add
  have hnu_quarter : ENNReal.ofReal (1 / 4 : ℝ) ≤ nu S :=
    le_trans (by norm_num) hnu
  have hbase := TVLe.condOn_cv18 h hepsilon hS
    (p := ENNReal.ofReal (1 / 4 : ℝ)) (by norm_num) hmu hnu_quarter
  convert hbase using 1
  simp [ENNReal.div_eq_inv_mul]
  ring

/-- Complete CV18 rejection stability with only the exact target's acceptance
bound as input.  This is the form consumed after a mixing theorem: weighting
is a contraction, and the one-half exact acceptance plus `epsilon ≤ 1/4`
controls normalization. -/
theorem TVLe.normalize_withDensity_target_half_cv18
    {Omega : Type*} [MeasurableSpace Omega]
    {mu nu : Measure Omega} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {epsilon : ENNReal} (h : Arlib.TVLe mu nu epsilon)
    (hepsilon : epsilon ≠ ⊤) (hepsilon_quarter : epsilon ≤ ENNReal.ofReal (1 / 4 : ℝ))
    {accept : Omega → ENNReal} (haccept : Measurable accept)
    (haccept_one : ∀ x, accept x ≤ 1)
    (hnu : ENNReal.ofReal (1 / 2 : ℝ) ≤
      (nu.withDensity accept) Set.univ) :
    Arlib.TVLe
      (Arlib.condOn (mu.withDensity accept) Set.univ)
      (Arlib.condOn (nu.withDensity accept) Set.univ)
      (8 * epsilon) := by
  have hmuInt : ∫⁻ x, accept x ∂mu ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact lintegral_le_const (Filter.Eventually.of_forall haccept_one)
  have hnuInt : ∫⁻ x, accept x ∂nu ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact lintegral_le_const (Filter.Eventually.of_forall haccept_one)
  let _ : IsFiniteMeasure (mu.withDensity accept) :=
    isFiniteMeasure_withDensity hmuInt
  let _ : IsFiniteMeasure (nu.withDensity accept) :=
    isFiniteMeasure_withDensity hnuInt
  exact TVLe.condOn_target_half_cv18
    (TVLe.withDensity_le_one_cv18 h haccept haccept_one)
    hepsilon hepsilon_quarter MeasurableSet.univ hnu

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

/-- Conditioning a restriction on the whole space is the same as directly
conditioning the original measure on the restricting set. -/
theorem condOn_restrict_univ_cv18 {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {S : Set Omega} (hS : MeasurableSet S) :
    Arlib.condOn (mu.restrict S) Set.univ = Arlib.condOn mu S := by
  ext T hT
  rw [Arlib.condOn_apply _ MeasurableSet.univ hT,
    Arlib.condOn_apply _ hS hT, Set.inter_univ,
    Measure.restrict_apply hT, Measure.restrict_apply_univ]

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

/-- After normalizing the second rejection, its exact target is the Gaussian
of variance `variance` conditioned on `K`. -/
theorem condOn_gaussian_scaleAcceptance_eq_target_cv18
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (variance c : ℝ)
    (hprop0 :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (variance / c ^ 2))) K ≠ 0)
    (hproptop :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (variance / c ^ 2))) K ≠ ⊤) :
    Arlib.condOn
        ((Arlib.condOn
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight (variance / c ^ 2))) K).withDensity
          (gaussianScaleAcceptance variance c)) Set.univ =
      Arlib.condOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight variance)) K := by
  rw [condOn_gaussian_withDensity_scaleAcceptance_cv18 hK]
  rw [condOn_smul_cv18 _ MeasurableSet.univ
    (ENNReal.inv_ne_zero.mpr hproptop) (ENNReal.inv_ne_top.mpr hprop0)]
  exact condOn_restrict_univ_cv18 _ hK

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

/-- The complete two-rejection distributional transfer used after a speedy
walk phase.  If the approximate speedy law is within `epsilon` of stationarity
and `epsilon ≤ 1/32`, core rejection, rescaling, and Gaussian correction
produce a law within `64 * epsilon` of the Gaussian target restricted to `K`. -/
theorem TVLe.speedyToGaussian_twoStage_cv18
    (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {delta variance : ℝ} (hdelta : 0 < delta)
    (hdelta_n : delta ≤ 1 / (2 * (n : ℝ)))
    (hvariance : 0 < variance)
    (hmass0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hmasstop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤)
    (hprop0 :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight
          (variance / (1 - 1 / (2 * (n : ℝ))) ^ 2))) K ≠ 0)
    (hproptop :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight
          (variance / (1 - 1 / (2 * (n : ℝ))) ^ 2))) K ≠ ⊤)
    {mu : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu]
    {epsilon : ENNReal}
    (hmix : Arlib.TVLe mu (ellGaussianProb K delta variance) epsilon)
    (hepsilon : epsilon ≠ ⊤)
    (hepsilon_small : epsilon ≤ ENNReal.ofReal (1 / 32 : ℝ)) :
    let c : ℝ := 1 - 1 / (2 * (n : ℝ))
    Arlib.TVLe
      (Arlib.condOn
        (((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)).withDensity
          (gaussianScaleAcceptance variance c)) Set.univ)
      (Arlib.condOn
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (gaussianWeight variance)) K)
      (64 * epsilon) := by
  dsimp only
  let c : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hc0 : 0 < c := by
    dsimp [c]
    have hle : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : ℝ)) := by positivity
    linarith
  have hcore : MeasurableSet (c • K) :=
    measurableSet_smul_set_cv18 hK hc0.ne'
  let nu : Measure (EuclideanSpace ℝ (Fin n)) :=
    ellGaussianProb K delta variance
  let _ : IsProbabilityMeasure nu :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hhalfCore : ENNReal.ofReal (1 / 2 : ℝ) ≤ nu (c • K) := by
    dsimp [nu, c]
    exact half_le_ellGaussianProb_standardCore_cv18 hn hK hKc hball
      hdelta hdelta_n hvariance hmass0 hmasstop
  have hepsQuarter : epsilon ≤ ENNReal.ofReal (1 / 4 : ℝ) :=
    hepsilon_small.trans (by norm_num)
  have hfirst := TVLe.condOn_target_half_cv18 hmix hepsilon
    hepsQuarter hcore hhalfCore
  have hquarter_add : ENNReal.ofReal (1 / 4 : ℝ) + epsilon ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      ENNReal.ofReal (1 / 4 : ℝ) + epsilon ≤
          ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) := by gcongr
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        norm_num
  have hmuCoreAdd : ENNReal.ofReal (1 / 4 : ℝ) + epsilon ≤
      mu (c • K) + epsilon :=
    hquarter_add.trans (hhalfCore.trans (hmix.right hcore))
  have hmuCore : ENNReal.ofReal (1 / 4 : ℝ) ≤ mu (c • K) :=
    ENNReal.le_of_add_le_add_right hepsilon hmuCoreAdd
  have hmuCore0 : mu (c • K) ≠ 0 :=
    ne_of_gt ((by norm_num : 0 < ENNReal.ofReal (1 / 4 : ℝ)).trans_le hmuCore)
  let _ : IsProbabilityMeasure (Arlib.condOn mu (c • K)) :=
    Arlib.isProbabilityMeasure_condOn mu hmuCore0 (measure_ne_top mu _)
  have hnuCore0 : nu (c • K) ≠ 0 :=
    ne_of_gt ((by norm_num : 0 < ENNReal.ofReal (1 / 2 : ℝ)).trans_le hhalfCore)
  let _ : IsProbabilityMeasure (Arlib.condOn nu (c • K)) :=
    Arlib.isProbabilityMeasure_condOn nu hnuCore0 (measure_ne_top nu _)
  have hmap := hfirst.map
    ((continuous_const_smul c⁻¹).measurable)
  let _ : IsProbabilityMeasure
      ((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)) :=
    Measure.isProbabilityMeasure_map
      ((continuous_const_smul c⁻¹).measurable.aemeasurable)
  let proposal : Measure (EuclideanSpace ℝ (Fin n)) :=
    Arlib.condOn
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (gaussianWeight (variance / c ^ 2))) K
  let _ : IsProbabilityMeasure proposal :=
    Arlib.isProbabilityMeasure_condOn _ hprop0 hproptop
  have htargetMap :
      (Arlib.condOn nu (c • K)).map (fun x => c⁻¹ • x) = proposal := by
    dsimp [nu, proposal]
    rw [condOn_ellGaussianProb_smul_eq_gaussian_cv18 hK hKc hball
      hc0 hc1 hdelta (by simpa [c] using hdelta_n) hmass0 hmasstop]
    exact map_condOn_gaussian_smul_cv18 hK hc0
  rw [htargetMap] at hmap
  have heightSmall : 8 * epsilon ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
    calc
      8 * epsilon ≤ 8 * ENNReal.ofReal (1 / 32 : ℝ) := by gcongr
      _ = ENNReal.ofReal (1 / 4 : ℝ) := by
        rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
        norm_num
  have heightTop : 8 * epsilon ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hepsilon
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    hball (Metric.mem_ball_self one_pos)
  have hhalfAccept : ENNReal.ofReal (1 / 2 : ℝ) ≤
      proposal.withDensity (gaussianScaleAcceptance variance c) Set.univ := by
    dsimp [proposal, c]
    exact half_le_condOn_gaussian_scaleAcceptance_mass_standardCore_cv18
      hn hK hKc hzero hprop0 hproptop
  have hsecond := TVLe.normalize_withDensity_target_half_cv18
    hmap heightTop heightSmall (measurable_gaussianScaleAcceptance variance c)
    (gaussianScaleAcceptance_le_one hvariance hc0 hc1.le) hhalfAccept
  have htarget :
      Arlib.condOn
          (proposal.withDensity (gaussianScaleAcceptance variance c)) Set.univ =
        Arlib.condOn
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (gaussianWeight variance)) K := by
    dsimp [proposal, c]
    exact condOn_gaussian_scaleAcceptance_eq_target_cv18 hK variance _
      hprop0 hproptop
  rw [htarget] at hsecond
  convert hsecond using 1
  ring

end Arlib.MarkovChains

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

/-- The global one-half acceptance bound specialized to the exact fixed body
used by the current Figure-1 executable. -/
theorem half_le_truncatedBody_gaussianScaleAcceptance_mass
    (q : VolumeParams) (I : VolumeInput q.n) {variance : ℝ}
    (hvariance : 0 < variance) :
    ENNReal.ofReal (1 / 2) ≤
      (Arlib.condOn
        ((volume : Measure (AmbientSpace q.n)).withDensity
          (Arlib.MarkovChains.gaussianWeight
            (variance / (1 - 1 / (2 * (q.n : ℝ))) ^ 2)))
        (truncatedBody q I)).withDensity
          (Arlib.MarkovChains.gaussianScaleAcceptance variance
            (1 - 1 / (2 * (q.n : ℝ)))) Set.univ := by
  have hn : 1 ≤ q.n := le_trans (by norm_num) q.dim_ok
  have hnR : (0 : ℝ) < q.n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hc0 : 0 < 1 - 1 / (2 * (q.n : ℝ)) := by
    rw [sub_pos, div_lt_one (by positivity)]
    have hnRone : (1 : ℝ) ≤ q.n := by exact_mod_cast hn
    nlinarith
  have hscaled :
      0 < variance / (1 - 1 / (2 * (q.n : ℝ))) ^ 2 := by positivity
  have hK0 : volume (truncatedBody q I) ≠ 0 := by
    apply ne_of_gt
    exact (Metric.measure_ball_pos volume (0 : AmbientSpace q.n) one_pos).trans_le
      (measure_mono fun x hx =>
        unitBall_subset_truncatedBody q I (Metric.ball_subset_closedBall hx))
  have hKtop : volume (truncatedBody q I) ≠ ⊤ :=
    (truncatedVolumeInput q I).body.isCompact.measure_lt_top.ne
  exact Arlib.MarkovChains.half_le_condOn_gaussian_scaleAcceptance_mass_standardCore_cv18
    hn (truncatedBody_measurable q I) (truncatedVolumeInput q I).body.convex
    (unitBall_subset_truncatedBody q I (by simp [unitBall]))
    (Arlib.MarkovChains.withDensity_gaussianWeight_ne_zero _ hK0)
    (Arlib.MarkovChains.withDensity_gaussianWeight_ne_top
      hscaled (truncatedBody_measurable q I) hKtop)

end ArlibCommunity.Algorithms.CV18
