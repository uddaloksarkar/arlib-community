/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPhaseMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialTail

/-! # Concrete KLS error parameters for every CV18 accuracy phase -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal Pointwise

/-- A concrete error for the KLS homothetic-core argument.  Its exponential
decay leaves ample room in Figure 1's proposal-radius constant. -/
noncomputable def accuracyCoreError (q : VolumeParams) : ℝ :=
  Real.exp (-128 * protectedLog ((q.n : ℝ) / q.eps)) / (q.n : ℝ)

theorem accuracyCoreError_pos (q : VolumeParams) :
    0 < accuracyCoreError q := by
  unfold accuracyCoreError
  apply div_pos (Real.exp_pos _)
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)

theorem accuracyCoreError_le_one_div_sixteen (q : VolumeParams) :
    accuracyCoreError q ≤ 1 / 16 := by
  have hn : (1 : ℝ) ≤ q.n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
  have hL : 1 ≤ protectedLog ((q.n : ℝ) / q.eps) :=
    le_max_left _ _
  have hexp : Real.exp (-128 * protectedLog ((q.n : ℝ) / q.eps)) ≤
      Real.exp (-6) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold accuracyCoreError
  calc
    Real.exp (-128 * protectedLog ((q.n : ℝ) / q.eps)) / (q.n : ℝ) ≤
        Real.exp (-6) / 1 := by
      calc
        _ ≤ Real.exp (-6) / (q.n : ℝ) :=
          div_le_div_of_nonneg_right hexp (by positivity)
        _ ≤ Real.exp (-6) / 1 := by
          exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hn
    _ ≤ 1 / 64 := by simpa using exp_neg_six_le_one_div_64
    _ ≤ 1 / 16 := by norm_num

theorem accuracyCoreError_le_one_div_sixty_four (q : VolumeParams) :
    accuracyCoreError q ≤ 1 / 64 := by
  have hn : (1 : ℝ) ≤ q.n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) q.dim_ok)
  have hL : 1 ≤ protectedLog ((q.n : ℝ) / q.eps) :=
    le_max_left _ _
  have hexp : Real.exp (-128 * protectedLog ((q.n : ℝ) / q.eps)) ≤
      Real.exp (-6) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold accuracyCoreError
  calc
    Real.exp (-128 * protectedLog ((q.n : ℝ) / q.eps)) / (q.n : ℝ) ≤
        Real.exp (-6) / 1 := by
      calc
        _ ≤ Real.exp (-6) / (q.n : ℝ) :=
          div_le_div_of_nonneg_right hexp (by positivity)
        _ ≤ Real.exp (-6) / 1 := by
          exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hn
    _ ≤ 1 / 64 := by simpa using exp_neg_six_le_one_div_64

theorem log_n_div_accuracyCoreError_le (q : VolumeParams) :
    Real.log ((q.n : ℝ) / accuracyCoreError q) ≤
      130 * protectedLog ((q.n : ℝ) / q.eps) := by
  let L : ℝ := protectedLog ((q.n : ℝ) / q.eps)
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have heps0 : 0 < q.eps := q.heps.1
  have hnle : (q.n : ℝ) ≤ (q.n : ℝ) / q.eps := by
    rw [le_div_iff₀ heps0]
    have hnnonneg : (0 : ℝ) ≤ q.n := hn0.le
    nlinarith [q.heps.2.le]
  have hlogn : Real.log (q.n : ℝ) ≤ L := by
    calc
      Real.log (q.n : ℝ) ≤ Real.log ((q.n : ℝ) / q.eps) :=
        Real.strictMonoOn_log.monotoneOn hn0 (div_pos hn0 heps0) hnle
      _ ≤ L := le_max_right _ _
  have hexp0 : Real.exp (-128 * L) ≠ 0 := (Real.exp_pos _).ne'
  have hnne : (q.n : ℝ) ≠ 0 := hn0.ne'
  change Real.log ((q.n : ℝ) /
      (Real.exp (-128 * L) / (q.n : ℝ))) ≤ 130 * L
  have heq : (q.n : ℝ) / (Real.exp (-128 * L) / (q.n : ℝ)) =
      ((q.n : ℝ) * (q.n : ℝ)) / Real.exp (-128 * L) := by
    field_simp
  rw [heq, Real.log_div (mul_ne_zero hnne hnne) hexp0,
    Real.log_mul hnne hnne, Real.log_exp]
  nlinarith

/-- Figure 1's actual proposal radius satisfies the KLS large-core condition
at the concrete error above; no phase-local analytic premise remains. -/
theorem figureOneProposalRadius_le_accuracyCoreErrorStep
    (q : VolumeParams) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    figureOneProposalRadius q sigma2 ≤
      1 / (8 * Real.sqrt
        ((q.n : ℝ) * Real.log ((q.n : ℝ) / accuracyCoreError q))) := by
  let L : ℝ := protectedLog ((q.n : ℝ) / q.eps)
  let b : ℝ := Real.sqrt ((q.n : ℝ) * L)
  let d : ℝ := Real.sqrt
    ((q.n : ℝ) * Real.log ((q.n : ℝ) / accuracyCoreError q))
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hL : 1 ≤ L := by dsimp [L]; exact le_max_left _ _
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hcore16 := accuracyCoreError_le_one_div_sixteen q
  have hratio : 1 < (q.n : ℝ) / accuracyCoreError q := by
    rw [lt_div_iff₀ (accuracyCoreError_pos q)]
    have hn3 : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
    nlinarith
  have hlog0 : 0 < Real.log ((q.n : ℝ) / accuracyCoreError q) :=
    Real.log_pos hratio
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hlog := log_n_div_accuracyCoreError_le q
  change Real.log ((q.n : ℝ) / accuracyCoreError q) ≤ 130 * L at hlog
  have hsq : d ^ 2 ≤ (16 * b) ^ 2 := by
    have hbSq : b ^ 2 = (q.n : ℝ) * L := by
      dsimp [b]
      rw [Real.sq_sqrt]
      positivity
    have hdSq : d ^ 2 = (q.n : ℝ) *
        Real.log ((q.n : ℝ) / accuracyCoreError q) := by
      dsimp [d]
      rw [Real.sq_sqrt]
      positivity
    rw [hdSq, mul_pow, hbSq]
    norm_num
    have := mul_le_mul_of_nonneg_left hlog hn0.le
    nlinarith
  have hdb : d ≤ 16 * b := by
    nlinarith [Real.sqrt_nonneg
      ((q.n : ℝ) * Real.log ((q.n : ℝ) / accuracyCoreError q))]
  unfold figureOneProposalRadius
  change min (Real.sqrt sigma2) 1 / (4096 * b) ≤ 1 / (8 * d)
  calc
    min (Real.sqrt sigma2) 1 / (4096 * b) ≤ 1 / (4096 * b) := by
      gcongr
      exact min_le_right _ _
    _ ≤ 1 / (8 * d) := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith

set_option maxHeartbeats 800000 in
/-- The complete KLS phase sampler with all geometric and core-error choices
discharged.  This combines the small- and large-radius branches and leaves
only the ordinary warm-start and walk-length inputs. -/
theorem accuracyPhaseSampleToGaussian_cv18
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {mu0 : Measure (AmbientSpace q.n)} [IsProbabilityMeasure mu0]
    {M mixError : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2))
    (hmixError0 : 0 < mixError) (hmixError64 : mixError ≤ 1 / 64)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / mixError)) /
      (figureOneProposalRadius q sigma2 * Real.log 2 /
        (640 * Real.sqrt sigma2 * Real.sqrt q.n)) ^ 2) + 1 ≤ (t : ℝ)) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
    let mu := Arlib.MarkovChains.iterate P mu0 t
    let c : ℝ := 1 - 1 / (2 * (q.n : ℝ))
    Arlib.TVLe
      (Arlib.condOn
        (((Arlib.condOn mu (c • K)).map (fun x => c⁻¹ • x)).withDensity
          (Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c)) Set.univ)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))
      (64 * ENNReal.ofReal mixError +
        32 * ENNReal.ofReal (accuracyCoreError q) +
        ENNReal.ofReal ((q.eps / (q.n : ℝ)) ^ 16)) := by
  dsimp only
  by_cases hsmall : accuracyPhaseRadius q sigma2 ≤ 1
  · have h := accuracyPhaseSampleToGaussian_smallRadius_cv18 q I hsigma2
      hsmall hM hwarm hmixError0 (hmixError64.trans (by norm_num)) ht
    apply h.mono
    gcongr
    exact le_self_add
  · have hlarge : 1 ≤ accuracyPhaseRadius q sigma2 := le_of_not_ge hsmall
    have hcore0 := accuracyCoreError_pos q
    have hcore16 := accuracyCoreError_le_one_div_sixteen q
    have hcombinedReal :
        8 * mixError + 4 * accuracyCoreError q ≤ (1 : ℝ) / 4 := by
      nlinarith [accuracyCoreError_le_one_div_sixty_four q]
    have hcombined :
        8 * ENNReal.ofReal mixError +
          4 * ENNReal.ofReal (accuracyCoreError q) ≤
            ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ 8 * mixError)
          (by positivity : 0 ≤ 4 * accuracyCoreError q)]
      exact ENNReal.ofReal_le_ofReal hcombinedReal
    exact accuracyPhaseSampleToGaussian_largeRadius_cv18 q I hsigma2
      hlarge hcore0 hcore16
      (figureOneProposalRadius_le_accuracyCoreErrorStep q hsigma2)
      hM hwarm hmixError0 (hmixError64.trans (by norm_num)) ht hcombined

end ArlibCommunity.Algorithms.CV18
