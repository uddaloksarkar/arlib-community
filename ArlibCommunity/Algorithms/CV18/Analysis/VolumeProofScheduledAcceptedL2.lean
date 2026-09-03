/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledAcceptedSupport
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyTVL2

/-!
# L2 domination for the schedule-targeted accepted law

The schedule-targeted KLS core uses a different radius from the older
accuracy core.  This module supplies the corresponding warm domination
needed to transfer unbounded Gaussian-ratio moments.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Pointwise

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib _root_.Arlib.MarkovChains

/-- The unnormalised speedy measure on the scheduled core is dominated by
the ordinary Gaussian measure on the full truncated body. -/
theorem scheduledPhase_ellGaussianMeasure_le_truncatedGaussianMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    ellGaussianMeasure
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2 ≤
      truncatedGaussianMeasure q I sigma2 := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [ellGaussianMeasure, withDensity_apply _ hA,
    truncatedGaussianMeasure, withDensity_apply _ hA]
  rw [Measure.restrict_restrict hA, Measure.restrict_restrict hA]
  have hsub : A ∩ figureOneScheduledPhaseBody q I sigma2 ⊆
      A ∩ truncatedBody q I := fun _ hx => ⟨hx.1, hx.2.1⟩
  calc
    (∫⁻ x in A ∩ figureOneScheduledPhaseBody q I sigma2,
        ell (figureOneScheduledPhaseBody q I sigma2)
            (figureOneScheduledProposalRadius q sigma2) x *
          gaussianWeight sigma2 x) ≤
      ∫⁻ x in A ∩ figureOneScheduledPhaseBody q I sigma2,
        gaussianWeight sigma2 x := by
      apply lintegral_mono
      intro x
      simpa using mul_le_mul'
        (ell_le_one (figureOneScheduledPhaseBody q I sigma2)
          (figureOneScheduledProposalRadius q sigma2) x) le_rfl
    _ ≤ ∫⁻ x in A ∩ truncatedBody q I,
        gaussianWeight sigma2 x :=
      lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    _ = ∫⁻ x in A ∩ truncatedBody q I,
        ENNReal.ofReal (gaussianDensity sigma2 x) := by
      apply lintegral_congr
      intro x
      simp [gaussianWeight, gaussianWeightReal, gaussianDensity_eq]

/-- The full truncated Gaussian normalizer is at most four times the
scheduled speedy-core normalizer. -/
theorem scheduledPhase_gaussianMass_le_four_ellGaussianMass
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    truncatedGaussianMeasure q I sigma2 Set.univ ≤
      4 * ellGaussianMeasure
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2 Set.univ := by
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let full : ENNReal := ∫⁻ x in truncatedBody q I, gaussianWeight sigma2 x
  let core : ENNReal := ∫⁻ x in K, gaussianWeight sigma2 x
  let speedy : ENNReal := ellGaussianMeasure K delta sigma2 Set.univ
  have hfull : truncatedGaussianMeasure q I sigma2 Set.univ = full := by
    rw [truncatedGaussianMeasure_apply_univ q I hsigma2]
    exact (lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
      (truncatedBody_measurable q I) hsigma2).symm
  have hfullCore : full ≤ 2 * core := by
    rw [show full = ENNReal.ofReal
        (gaussianIntegral (truncatedBody q I) sigma2) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (truncatedBody_measurable q I) hsigma2]
    rw [show core = ENNReal.ofReal (gaussianIntegral K sigma2) by
      exact lintegral_gaussianWeight_eq_ofReal_gaussianIntegral
        (by dsimp [K]; exact figureOneScheduledPhaseBody_measurable q I sigma2)
        hsigma2]
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [K] using
        scheduledPhase_full_gaussianIntegral_le_two_core q I hsigma2)
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) * core ≤ speedy := by
    simpa [K, delta, core, speedy] using
      half_mul_gaussianWeight_le_scheduledPhaseEllGaussian q I hsigma2
  have hcore : core ≤ 2 * speedy := by
    calc
      core = 2 * (ENNReal.ofReal (1 / 2 : ℝ) * core) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ 2 * speedy := mul_le_mul' le_rfl hhalf
  rw [hfull]
  calc
    full ≤ 2 * core := hfullCore
    _ ≤ 2 * (2 * speedy) := mul_le_mul' le_rfl hcore
    _ = 4 * speedy := by ring

/-- The schedule-targeted speedy stationary law is universally `4`-warm
for the exact truncated Gaussian at the same variance. -/
theorem scheduledPhase_speedyStationary_isWarm_target
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    IsWarm 4
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) := by
  let mu := ellGaussianMeasure
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  let nu := truncatedGaussianMeasure q I sigma2
  have hdelta : 0 < figureOneScheduledProposalRadius q sigma2 :=
    figureOneScheduledProposalRadius_pos q hsigma2
  have hmu0 : mu Set.univ ≠ 0 := by
    dsimp [mu]
    exact ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmutop : mu Set.univ ≠ ⊤ := by
    dsimp [mu]
    exact ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) hsigma2
  have hnu0 : nu Set.univ ≠ 0 := by
    intro hzero
    have hmeasure : nu = 0 := Measure.measure_univ_eq_zero.mp hzero
    exact truncatedGaussianMeasure_ne_zero q I hsigma2
      (by simpa [nu] using hmeasure)
  have hnutop : nu Set.univ ≠ ⊤ := by
    let _ := truncatedGaussianMeasure_isFinite q I hsigma2
    exact measure_ne_top nu Set.univ
  have hdom : mu ≤ (1 : ENNReal) • nu := by
    simpa [mu, nu] using
      scheduledPhase_ellGaussianMeasure_le_truncatedGaussianMeasure
        q I sigma2
  have hmass : nu Set.univ ≤ (4 : ENNReal) * mu Set.univ := by
    simpa [mu, nu] using
      scheduledPhase_gaussianMass_le_four_ellGaussianMass q I hsigma2
  have hw := isWarm_normalize_of_le_smul hmu0 hmutop hnu0 hnutop hdom hmass
  simpa [mu, nu, ellGaussianProb,
    truncatedGaussianProbability_toMeasure q I hsigma2,
    truncatedGaussianMeasure_apply_univ q I hsigma2] using hw

#print axioms scheduledPhase_ellGaussianMeasure_le_truncatedGaussianMeasure
#print axioms scheduledPhase_gaussianMass_le_four_ellGaussianMass
#print axioms scheduledPhase_speedyStationary_isWarm_target

end ArlibCommunity.Algorithms.CV18
