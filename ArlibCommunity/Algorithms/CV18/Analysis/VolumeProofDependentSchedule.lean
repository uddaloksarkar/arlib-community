/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAnalyticCore
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofDependentProduct

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-!
# Concrete CV18 dependent-product parameters

This file is the numerical and final-assembly layer between Lemma 7.17(c)
and Lemma 7.15.  It deliberately does not change the existing analytic
capstone: the paper's dependent-product argument gives a direct failure
bound, whereas `FigureOnePostInitialMixingBound` compares with the exact
(unknown) failure probability of a separate ideal experiment.
-/

/-- There is one empirical estimator for every Gaussian transition and one
more for the terminal Gaussian-to-uniform transition. -/
noncomputable def figureOneDependentPhaseCount (q : VolumeParams) : ℕ :=
  terminalPhaseSteps q + 1

/-- A uniform upper bound for the two phase-sensitive sample counts. -/
noncomputable def figureOneDependentMaxSampleCount (q : VolumeParams) : ℕ :=
  max (figureOneFixedSampleCount q) (figureOneSampleCount q)

/-- The truncation level used when Lemma 7.15 is instantiated at final
relative error `q.eps / 2`.  The large absolute constant leaves a clean
`9/64` total probability budget. -/
noncomputable def figureOneDependentAlpha (q : VolumeParams) : ℝ :=
  1024 * (figureOneDependentPhaseCount q : ℝ) / q.eps ^ 2

/-- Dependence coefficient consumed by the recursive moment estimates in
Lemma 7.15. -/
noncomputable def figureOneDependentEpsilon (q : VolumeParams) : ℝ :=
  1 / (16 * figureOneDependentAlpha q ^ 3)

/-- Per-sample mixing accuracy sufficient for Lemma 7.17(c).  With at most
`k` samples in each of `m` phases, `3 k m nu` is exactly the dependence
coefficient selected above. -/
noncomputable def figureOnePerSampleMixingError (q : VolumeParams) : ℝ :=
  figureOneDependentEpsilon q /
    (3 * (figureOneDependentMaxSampleCount q : ℝ) *
      (figureOneDependentPhaseCount q : ℝ))

theorem figureOneDependentPhaseCount_pos (q : VolumeParams) :
    0 < figureOneDependentPhaseCount q := by
  simp [figureOneDependentPhaseCount]

theorem figureOneDependentMaxSampleCount_pos (q : VolumeParams) :
    0 < figureOneDependentMaxSampleCount q := by
  exact lt_of_lt_of_le (figureOneSampleCount_pos q) (le_max_right _ _)

theorem figureOneDependentAlpha_pos (q : VolumeParams) :
    0 < figureOneDependentAlpha q := by
  unfold figureOneDependentAlpha
  exact div_pos
    (mul_pos (by norm_num) (by
      exact_mod_cast figureOneDependentPhaseCount_pos q))
    (sq_pos_of_pos q.heps.1)

theorem figureOneDependentAlpha_one_le (q : VolumeParams) :
    1 ≤ figureOneDependentAlpha q := by
  have hm : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  rw [figureOneDependentAlpha, le_div_iff₀ (sq_pos_of_pos q.heps.1)]
  nlinarith

theorem figureOneDependentPhaseCount_div_alpha (q : VolumeParams) :
    (figureOneDependentPhaseCount q : ℝ) / figureOneDependentAlpha q =
      q.eps ^ 2 / 1024 := by
  have hm : (figureOneDependentPhaseCount q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (figureOneDependentPhaseCount_pos q))
  have he : q.eps ≠ 0 := q.heps.1.ne'
  unfold figureOneDependentAlpha
  field_simp [hm, he]

theorem figureOneDependent_tail_probability_real (q : VolumeParams) :
    ((q.eps ^ 2 / 32 +
          2 * ((figureOneDependentPhaseCount q : ℝ) /
            figureOneDependentAlpha q)) /
        (q.eps / 2) ^ 2) = 17 / 128 := by
  rw [figureOneDependentPhaseCount_div_alpha]
  field_simp [q.heps.1.ne']
  ring

theorem figureOneDependentEpsilon_nonneg (q : VolumeParams) :
    0 ≤ figureOneDependentEpsilon q := by
  unfold figureOneDependentEpsilon
  have ha := figureOneDependentAlpha_pos q
  positivity

theorem figureOneDependent_smallness (q : VolumeParams) :
    4 * figureOneDependentEpsilon q * figureOneDependentAlpha q ^ 3 ≤ 1 := by
  have ha := figureOneDependentAlpha_pos q
  rw [figureOneDependentEpsilon]
  field_simp [ha.ne']
  norm_num

theorem figureOnePerSampleMixingError_pos (q : VolumeParams) :
    0 < figureOnePerSampleMixingError q := by
  unfold figureOnePerSampleMixingError figureOneDependentEpsilon
  have ha := figureOneDependentAlpha_pos q
  have hk : (0 : ℝ) < figureOneDependentMaxSampleCount q := by
    exact_mod_cast figureOneDependentMaxSampleCount_pos q
  have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  positivity

/-- The exact parameter identity needed to feed the output of Lemma 7.17(c)
into the `ApproxIndepFun` premise of Lemma 7.15. -/
theorem figureOne_lemma717c_budget (q : VolumeParams) :
    3 * (figureOneDependentMaxSampleCount q : ℝ) *
        (figureOneDependentPhaseCount q : ℝ) *
          figureOnePerSampleMixingError q =
      figureOneDependentEpsilon q := by
  have hk : (figureOneDependentMaxSampleCount q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (figureOneDependentMaxSampleCount_pos q))
  have hm : (figureOneDependentPhaseCount q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (figureOneDependentPhaseCount_pos q))
  unfold figureOnePerSampleMixingError
  field_simp [hk, hm]

/-- The successor coefficient required in the recursive first-moment lower
bound of Lemma 7.15. -/
theorem figureOneDependent_coefficient (q : VolumeParams) {i : ℕ}
    (hi : i < figureOneDependentPhaseCount q) :
    2 * figureOneDependentEpsilon q * figureOneDependentAlpha q ^ 2 *
        (i + 1) ≤ 1 := by
  have ha := figureOneDependentAlpha_pos q
  have hmR : (i + 1 : ℕ) ≤ figureOneDependentPhaseCount q := by omega
  have hmR' : (i + 1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast hmR
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  have hmAlpha : (figureOneDependentPhaseCount q : ℝ) ≤
      figureOneDependentAlpha q := by
    rw [figureOneDependentAlpha, le_div_iff₀ (sq_pos_of_pos q.heps.1)]
    have hm0 : (0 : ℝ) ≤ figureOneDependentPhaseCount q := by positivity
    nlinarith
  rw [figureOneDependentEpsilon]
  field_simp [ha.ne']
  nlinarith [hmR'.trans hmAlpha]

/-- The two Markov truncations in Lemma 7.15 cost at most
`3 eps^2 / 1024` over all phases. -/
theorem figureOneDependent_truncation_probability (q : VolumeParams) :
    (∑ _ : Fin (figureOneDependentPhaseCount q),
        (ENNReal.ofReal (1 / figureOneDependentAlpha q) +
          ENNReal.ofReal (2 / figureOneDependentAlpha q))) =
      ENNReal.ofReal (3 * q.eps ^ 2 / 1024) := by
  have ha := figureOneDependentAlpha_pos q
  have hone : 0 ≤ 1 / figureOneDependentAlpha q := by positivity
  have htwo : 0 ≤ 2 / figureOneDependentAlpha q := by positivity
  calc
    (∑ _ : Fin (figureOneDependentPhaseCount q),
        (ENNReal.ofReal (1 / figureOneDependentAlpha q) +
          ENNReal.ofReal (2 / figureOneDependentAlpha q))) =
        figureOneDependentPhaseCount q •
          (ENNReal.ofReal (1 / figureOneDependentAlpha q) +
            ENNReal.ofReal (2 / figureOneDependentAlpha q)) := by simp
    _ = figureOneDependentPhaseCount q •
          ENNReal.ofReal (3 / figureOneDependentAlpha q) := by
      congr 1
      rw [← ENNReal.ofReal_add hone htwo]
      congr 1
      ring
    _ = ENNReal.ofReal
          ((figureOneDependentPhaseCount q : ℝ) *
            (3 / figureOneDependentAlpha q)) := by
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (3 * q.eps ^ 2 / 1024) := by
      congr 1
      rw [show (figureOneDependentPhaseCount q : ℝ) *
          (3 / figureOneDependentAlpha q) =
            3 * ((figureOneDependentPhaseCount q : ℝ) /
              figureOneDependentAlpha q) by ring,
        figureOneDependentPhaseCount_div_alpha]
      ring

/-- With the schedule's empirical-moment excess `eps^2/32`, the full
Chebyshev plus two-truncation right-hand side of Lemma 7.15 is below `9/64`.
This leaves ample room inside the direct `3/16` post-initial budget. -/
theorem figureOneDependent_lemma715_probability_budget (q : VolumeParams) :
    ENNReal.ofReal
        ((q.eps ^ 2 / 32 +
            2 * ((figureOneDependentPhaseCount q : ℝ) /
              figureOneDependentAlpha q)) /
          (q.eps / 2) ^ 2) +
        ∑ _ : Fin (figureOneDependentPhaseCount q),
          (ENNReal.ofReal (1 / figureOneDependentAlpha q) +
            ENNReal.ofReal (2 / figureOneDependentAlpha q)) ≤
      ENNReal.ofReal (9 / 64 : ℝ) := by
  rw [figureOneDependent_tail_probability_real,
    figureOneDependent_truncation_probability]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 17 / 128)
    (by positivity : 0 ≤ 3 * q.eps ^ 2 / 1024)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [q.heps.1, q.heps.2]

/-- Lemma 7.15 with every purely numerical Figure-1 obligation discharged.
The remaining premises are exactly the probabilistic facts about the
executable phase estimators: their first/two moments, truncation identity,
and the Lemma 7.17(c) `ApproxIndepFun` bridge. -/
theorem measure_dependentPhaseSampleProduct_figureOne_le
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (mu : Measure Omega) [IsProbabilityMeasure mu]
    (mean rawMean second : ℕ → ℝ) (V W : ℕ → Omega → ℝ)
    (hmean : ∀ j, 0 ≤ mean j) (hmeanPos : ∀ j, 0 < mean j)
    (hrawMean : ∀ j, 0 ≤ rawMean j)
    (hrawMeanPos : ∀ j, 0 < rawMean j)
    (hrawMean_le : ∀ j, rawMean j ≤ 2 * mean j)
    (hsecond : ∀ j, 0 ≤ second j)
    (hmeanSecond : ∀ j, mean j ^ 2 ≤ second j)
    (hrawSecond : ∀ j, rawMean j ^ 2 ≤ 2 * second j)
    (hVmeas : ∀ j, Measurable (V j))
    (hV0 : ∀ j omega, 0 ≤ V j omega)
    (hVcap : ∀ j omega,
      V j omega ≤ figureOneDependentAlpha q * rawMean j)
    (hVmean : ∀ j, (∫ omega, V j omega ∂mu) = mean j)
    (hVsecond : ∀ j, (∫ omega, V j omega ^ 2 ∂mu) = second j)
    (hVeq : ∀ j omega, V j omega =
      dependentTruncatedPhase (figureOneDependentAlpha q) rawMean W j omega)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWint : ∀ j, Integrable (W j) mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) = rawMean j)
    (hind : ∀ i, ApproxIndepFun (figureOneDependentEpsilon q)
      (dependentTruncatedProduct (figureOneDependentAlpha q) mean V i)
      (V (i + 1)) mu)
    (hrelative : ∀ i,
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct second i ≤
        2 * dependentPhaseMeanProduct mean i ^ 2)
    (htailSecond :
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct second
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 32) *
          dependentPhaseMeanProduct mean
            (figureOneDependentPhaseCount q) ^ 2) :
    mu {omega | (q.eps / 2) *
          dependentPhaseMeanProduct mean
            (figureOneDependentPhaseCount q) ≤
        |dependentPhaseSampleProduct W
            (figureOneDependentPhaseCount q) omega -
          dependentPhaseMeanProduct mean
            (figureOneDependentPhaseCount q)|} ≤
      ENNReal.ofReal (9 / 64 : ℝ) := by
  refine (measure_dependentPhaseSampleProduct_relativeDeviation_le
    mu (figureOneDependentAlpha q) (figureOneDependentEpsilon q)
      mean rawMean second V W
      (figureOneDependentAlpha_one_le q)
      (figureOneDependentEpsilon_nonneg q)
      (figureOneDependent_smallness q)
      hmean hmeanPos hrawMean hrawMeanPos hrawMean_le hsecond
      hmeanSecond hrawSecond hVmeas hV0 hVcap hVmean hVsecond hVeq
      hWmeas hW0 hWint hWmean hind hrelative
      (figureOneDependentPhaseCount q)
      (fun i hi => figureOneDependent_coefficient q hi)
      (tailDelta := q.eps ^ 2 / 32) (relativeEps := q.eps / 2)
      (div_nonneg (sq_nonneg q.eps) (by norm_num))
      (div_pos q.heps.1 (by norm_num)) htailSecond).trans ?_
  exact figureOneDependent_lemma715_probability_budget q

/-- Deterministic accuracy transfer used after Lemma 7.15.  A half-epsilon
deviation from the telescoping phase mean, the already-proved initial
Gaussian normalization estimate, and radial truncation imply final
`q.eps`-relative accuracy for the original body. -/
theorem measure_scaledDependentProduct_failure_le_of_relativeDeviation
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n)
    (htrunc : FigureOneRadialTruncationBound q I)
    (mu : Measure Omega) (X : Omega → ℝ) {mean : ℝ}
    (hmeanEq : mean = ∏ i, figureOneIdealPhaseMean q I i)
    {delta : ENNReal}
    (htail : mu {omega | (q.eps / 2) * mean ≤
      |X omega - mean|} ≤ delta) :
    mu {omega | initialGaussianIntegral q * X omega ∉
      accurateOutcome q I} ≤ delta := by
  let target := euclideanVolume (truncatedVolumeInput q I)
  let A := initialGaussianIntegral q
  have hA : 0 < A := by
    dsimp [A, initialGaussianIntegral]
    exact Real.rpow_pos_of_pos
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) (initialVariance_pos q)) _
  have htarget : 0 < target := by
    dsimp [target]
    exact euclideanVolume_pos q (truncatedVolumeInput q I)
  have hcenter : RelativeApprox (q.eps / 32) target (A * mean) := by
    rw [hmeanEq]
    simpa [A, target] using
      figureOneIdealMean_relativeApprox_truncatedVolume q I
  have hsubset :
      {omega | initialGaussianIntegral q * X omega ∉ accurateOutcome q I} ⊆
        {omega | (q.eps / 2) * mean ≤ |X omega - mean|} := by
    intro omega hbad
    by_contra hdev
    have hdev' : |X omega - mean| < (q.eps / 2) * mean :=
      lt_of_not_ge hdev
    have hscaled : |A * X omega - A * mean| <
        (q.eps / 2) * (A * mean) := by
      rw [← mul_sub, abs_mul, abs_of_pos hA]
      nlinarith
    have hcenterBounds := hcenter
    unfold RelativeApprox Arlib.relErr at hcenterBounds
    have hlower : (1 - 3 * q.eps / 4) * target ≤ A * X omega := by
      have hdiffLower := (abs_lt.mp hscaled).1
      have hbase : (1 - q.eps / 32) * target ≤ A * mean := hcenterBounds.1
      have hnonneg : 0 ≤ target := htarget.le
      have hc : 0 ≤ 1 - q.eps / 2 := by linarith [q.heps.2]
      have hbaseScaled := mul_le_mul_of_nonneg_left hbase hc
      have hcoefficient :
          (1 - 3 * q.eps / 4) * target ≤
            (1 - q.eps / 2) * ((1 - q.eps / 32) * target) := by
        nlinarith [mul_nonneg q.heps.1.le hnonneg,
          mul_nonneg (sq_nonneg q.eps) hnonneg]
      nlinarith
    have hupper : A * X omega ≤ (1 + 3 * q.eps / 4) * target := by
      have hdiffUpper := (abs_lt.mp hscaled).2
      have hbase : A * mean ≤ (1 + q.eps / 32) * target := hcenterBounds.2
      have hnonneg : 0 ≤ target := htarget.le
      have hc : 0 ≤ 1 + q.eps / 2 := by linarith [q.heps.1]
      have hbaseScaled := mul_le_mul_of_nonneg_left hbase hc
      have hcoefficient :
          (1 + q.eps / 2) * ((1 + q.eps / 32) * target) ≤
            (1 + 3 * q.eps / 4) * target := by
        nlinarith [mul_nonneg q.heps.1.le hnonneg,
          mul_nonneg q.heps.1.le
            (mul_nonneg (sub_nonneg.mpr q.heps.2.le) hnonneg)]
      nlinarith
    apply hbad
    apply relativeApprox_full_of_three_quarters_truncated q I htrunc
    unfold RelativeApprox Arlib.relErr
    simpa [A, target] using And.intro hlower hupper
  exact (measure_mono hsubset).trans htail

/-- The direct post-initial statement naturally produced by the paper's
Lemma 7.15 argument.  Unlike `FigureOnePostInitialMixingBound`, it does not
compare the executable experiment with the exact failure mass of an ideal
experiment. -/
def FigureOnePostInitialDirectFailureBound
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) : Prop :=
  ((truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
    (figureOneContinuationLaw explicitVolumeCoolingSchedule q I oracle))
      (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (3 / 16 : ℝ)

/-- Smallest law-level bridge from the executable continuation to the
paper's dependent-product experiment.  Once the continuation law is the map
of a history probability space and Lemma 7.15 supplies its `9/64` deviation
bound, the direct post-initial contract follows. -/
theorem figureOnePostInitialDirectFailureBound_of_dependentProduct
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (htrunc : FigureOneRadialTruncationBound q I)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (hX : Measurable X) {mean : ℝ}
    (hmeanEq : mean = ∏ i, figureOneIdealPhaseMean q I i)
    (hlaw :
      (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          (figureOneContinuationLaw explicitVolumeCoolingSchedule q I oracle) =
        mu.map fun omega => initialGaussianIntegral q * X omega)
    (htail : mu {omega | (q.eps / 2) * mean ≤
      |X omega - mean|} ≤ ENNReal.ofReal (9 / 64 : ℝ)) :
    FigureOnePostInitialDirectFailureBound q I oracle := by
  have hscaled : Measurable fun omega => initialGaussianIntegral q * X omega :=
    measurable_const.mul hX
  have hfailure :=
    measure_scaledDependentProduct_failure_le_of_relativeDeviation
      q I htrunc mu X hmeanEq htail
  unfold FigureOnePostInitialDirectFailureBound
  rw [hlaw, Measure.map_apply hscaled (accurateOutcome_measurable q I).compl]
  refine hfailure.trans ?_
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- A direct `3/16` post-initial failure bound is already stronger than what
the base-run theorem needs: the initial-start replacement costs at most
`eps/64 ≤ 1/64`, leaving total failure `13/64 < 1/4`. -/
theorem figureOne_base_accuracy_of_direct_postInitialFailure
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (hpost : FigureOnePostInitialDirectFailureBound q I oracle) :
    3 / 4 ≤
      outcomeProbability
        (volumeAlgorithmLaw
          (fun q => baseVolumeCooling figureOnePrimitives
            explicitVolumeCoolingSchedule q) q I oracle)
        (accurateOutcome q I) := by
  let μ : Measure ℝ :=
    volumeAlgorithmLaw
      (fun q => baseVolumeCooling figureOnePrimitives
        explicitVolumeCoolingSchedule q) q I oracle
  have hstrong := figureOneBaseVolumeCooling_stronglyMeasurable
    explicitVolumeCoolingSchedule q I oracle
  let _ : IsProbabilityMeasure μ := by
    unfold μ volumeAlgorithmLaw
    exact MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
      hstrong.estimateMeasurable
  apply outcomeProbability_ge_three_quarters_of_failure_le μ q I
  change
    (baseVolumeCooling figureOnePrimitives explicitVolumeCoolingSchedule q).runEstimate
        oracle.query (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ)
  calc
    _ ≤ ((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
        (figureOneContinuationLaw explicitVolumeCoolingSchedule q I oracle))
          (accurateOutcome q I)ᶜ + ENNReal.ofReal (q.eps / 64) :=
      figureOneBaseVolumeCooling_event_le_idealStart_add
        explicitVolumeCoolingSchedule q I oracle (accurateOutcome q I)ᶜ
          (accurateOutcome_measurable q I).compl
    _ ≤ ENNReal.ofReal (3 / 16 : ℝ) + ENNReal.ofReal (q.eps / 64) := by
      exact add_le_add
        (by simpa [FigureOnePostInitialDirectFailureBound] using hpost) le_rfl
    _ ≤ ENNReal.ofReal (3 / 16 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) := by
      gcongr
      exact q.heps.2.le
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 3 / 16)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      apply ENNReal.ofReal_le_ofReal
      norm_num

#print axioms figureOne_lemma717c_budget
#print axioms figureOneDependent_coefficient
#print axioms figureOneDependent_lemma715_probability_budget
#print axioms measure_dependentPhaseSampleProduct_figureOne_le
#print axioms measure_scaledDependentProduct_failure_le_of_relativeDeviation
#print axioms figureOnePostInitialDirectFailureBound_of_dependentProduct
#print axioms figureOne_base_accuracy_of_direct_postInitialFailure

end ArlibCommunity.Algorithms.CV18
