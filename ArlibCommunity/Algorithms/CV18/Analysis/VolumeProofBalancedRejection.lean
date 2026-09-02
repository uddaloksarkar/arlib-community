/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyAcceptance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSubprobabilityMixing

/-!
# Balanced KLS rejection branches

The KLS correction already has a constant lower acceptance probability, but
its rejection probability need not have an a priori lower bound.  Multiplying
the acceptance coefficient by `1/2` leaves the law conditioned on acceptance
unchanged and makes rejection pointwise at least `1/2`.  Consequently both
normalized branches are uniformly warm for the speedy stationary law.  This
is the branch-reset invariant used by the finite retry sampler.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib _root_.Arlib.MarkovChains

private theorem ofReal_one_half_balanced :
    ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- The deliberately throttled KLS acceptance coefficient. -/
noncomputable def balancedAccuracyGaussianAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current : AmbientSpace q.n) : ENNReal :=
  (2 : ENNReal)⁻¹ * accuracyGaussianRejectionAcceptance q I sigma2 current

theorem measurable_balancedAccuracyGaussianAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (balancedAccuracyGaussianAcceptance q I sigma2) := by
  exact (measurable_accuracyGaussianRejectionAcceptance q I sigma2).const_mul _

theorem balancedAccuracyGaussianAcceptance_le_half
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    balancedAccuracyGaussianAcceptance q I sigma2 current ≤ (2 : ENNReal)⁻¹ := by
  unfold balancedAccuracyGaussianAcceptance
  calc
    (2 : ENNReal)⁻¹ * accuracyGaussianRejectionAcceptance q I sigma2 current
        ≤ (2 : ENNReal)⁻¹ * 1 := mul_le_mul le_rfl
          (accuracyGaussianRejectionAcceptance_le_one q I hsigma2 current)
          bot_le bot_le
    _ = (2 : ENNReal)⁻¹ := mul_one _

theorem half_le_one_sub_balancedAccuracyGaussianAcceptance
    (q : VolumeParams) (I : VolumeInput q.n) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) (current : AmbientSpace q.n) :
    (2 : ENNReal)⁻¹ ≤
      1 - balancedAccuracyGaussianAcceptance q I sigma2 current := by
  apply ENNReal.le_sub_of_add_le_left
    (ne_top_of_le_ne_top (by norm_num)
      (balancedAccuracyGaussianAcceptance_le_half q I hsigma2 current))
  have h := balancedAccuracyGaussianAcceptance_le_half q I hsigma2 current
  calc
    balancedAccuracyGaussianAcceptance q I sigma2 current + (2 : ENNReal)⁻¹
        ≤ (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ := add_le_add_left h _
    _ = 1 := by
      rw [← ofReal_one_half_balanced,
        ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num

/-- Current-state submeasure corresponding to a balanced successful attempt. -/
noncomputable def balancedAcceptedStateMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) : Measure (AmbientSpace q.n) :=
  mu.withDensity (balancedAccuracyGaussianAcceptance q I sigma2)

/-- Current-state submeasure corresponding to a balanced rejected attempt. -/
noncomputable def balancedRejectedStateMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) : Measure (AmbientSpace q.n) :=
  mu.withDensity (fun x => 1 - balancedAccuracyGaussianAcceptance q I sigma2 x)

theorem balancedAcceptedStateMeasure_eq_half_smul
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (mu : Measure (AmbientSpace q.n)) :
    balancedAcceptedStateMeasure q I sigma2 mu =
      (2 : ENNReal)⁻¹ •
        mu.withDensity (accuracyGaussianRejectionAcceptance q I sigma2) := by
  unfold balancedAcceptedStateMeasure balancedAccuracyGaussianAcceptance
  change mu.withDensity
      ((2 : ENNReal)⁻¹ • accuracyGaussianRejectionAcceptance q I sigma2) = _
  rw [withDensity_smul]
  exact measurable_accuracyGaussianRejectionAcceptance q I sigma2

theorem balancedAcceptedStateMeasure_mass_ge
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  rw [balancedAcceptedStateMeasure_eq_half_smul,
    Measure.smul_apply, smul_eq_mul]
  have h := accuracyPhase_stationary_acceptance_ge q I hsigma2
  change ENNReal.ofReal (7 / 64 : ℝ) ≤
    (pi.withDensity (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ at h
  calc
    ENNReal.ofReal (7 / 128 : ℝ) =
        (2 : ENNReal)⁻¹ * ENNReal.ofReal (7 / 64 : ℝ) := by
      rw [← ofReal_one_half_balanced,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    _ ≤ (2 : ENNReal)⁻¹ *
        (pi.withDensity
          (accuracyGaussianRejectionAcceptance q I sigma2)) Set.univ :=
      mul_le_mul' le_rfl h

theorem balancedRejectedStateMeasure_mass_ge_half
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (mu : Measure (AmbientSpace q.n)) [IsProbabilityMeasure mu] :
    (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 mu Set.univ := by
  unfold balancedRejectedStateMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    (2 : ENNReal)⁻¹ = ∫⁻ _x, (2 : ENNReal)⁻¹ ∂mu := by simp
    _ ≤ ∫⁻ x, 1 - balancedAccuracyGaussianAcceptance q I sigma2 x ∂mu :=
      lintegral_mono (half_le_one_sub_balancedAccuracyGaussianAcceptance
        q I hsigma2)

theorem balancedAcceptedStateMeasure_le_half_smul
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (mu : Measure (AmbientSpace q.n)) :
    balancedAcceptedStateMeasure q I sigma2 mu ≤ (2 : ENNReal)⁻¹ • mu := by
  rw [balancedAcceptedStateMeasure_eq_half_smul]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hA]
  calc
    (2 : ENNReal)⁻¹ *
        ∫⁻ x in A, accuracyGaussianRejectionAcceptance q I sigma2 x ∂mu ≤
      (2 : ENNReal)⁻¹ * ∫⁻ _x in A, (1 : ENNReal) ∂mu := by
        gcongr
        exact accuracyGaussianRejectionAcceptance_le_one q I hsigma2 _
    _ = (2 : ENNReal)⁻¹ * mu A := by rw [setLIntegral_one]

theorem balancedRejectedStateMeasure_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (sigma2 : ℝ) (mu : Measure (AmbientSpace q.n)) :
    balancedRejectedStateMeasure q I sigma2 mu ≤ mu := by
  unfold balancedRejectedStateMeasure
  apply Measure.le_iff.mpr
  intro A hA
  rw [withDensity_apply _ hA]
  calc
    (∫⁻ x in A, 1 - balancedAccuracyGaussianAcceptance q I sigma2 x ∂mu) ≤
        ∫⁻ _x in A, (1 : ENNReal) ∂mu :=
      lintegral_mono fun _ => tsub_le_self
    _ = mu A := by rw [setLIntegral_one]

/-- A normalized balanced successful branch at stationarity is uniformly
warm for the same speedy stationary law. -/
theorem balancedAcceptedStationary_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    _root_.Arlib.IsWarm 16
      (Arlib.condOn
        (balancedAcceptedStateMeasure q I sigma2 pi) Set.univ) pi := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  let branch := balancedAcceptedStateMeasure q I sigma2 pi
  have hp : ENNReal.ofReal (7 / 128 : ℝ) ≤ branch Set.univ := by
    simpa [K, delta, pi, branch] using
      balancedAcceptedStateMeasure_mass_ge q I hsigma2
  have hp32 : (32 : ENNReal)⁻¹ ≤ branch Set.univ := by
    calc
      (32 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 32 : ℝ) := by
        rw [show (1 / 32 : ℝ) = (32 : ℝ)⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
      _ ≤ ENNReal.ofReal (7 / 128 : ℝ) :=
        ENNReal.ofReal_le_ofReal (by norm_num)
      _ ≤ branch Set.univ := hp
  have hle : branch ≤ (2 : ENNReal)⁻¹ • pi := by
    simpa [branch] using balancedAcceptedStateMeasure_le_half_smul
      q I hsigma2 pi
  intro A hA
  rw [Arlib.condOn_def, Measure.restrict_univ,
    Measure.smul_apply, smul_eq_mul]
  have hbranch : branch A ≤ (2 : ENNReal)⁻¹ * pi A := by
    simpa [Measure.smul_apply, smul_eq_mul] using Measure.le_iff.mp hle A hA
  calc
    (branch Set.univ)⁻¹ * branch A ≤
        (branch Set.univ)⁻¹ * ((2 : ENNReal)⁻¹ * pi A) :=
      mul_le_mul' le_rfl hbranch
    _ ≤ ((32 : ENNReal)⁻¹)⁻¹ *
        ((2 : ENNReal)⁻¹ * pi A) := by gcongr
    _ = 16 * pi A := by
      rw [← ofReal_one_half_balanced]
      rw [inv_inv]
      rw [← mul_assoc]
      have hcoeff : (32 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) = 16 := by
        rw [show (32 : ENNReal) = ENNReal.ofReal (32 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
        norm_num
      rw [hcoeff]

/-- A normalized balanced rejection branch at stationarity is `2`-warm. -/
theorem balancedRejectedStationary_isWarm
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    let K := accuracyPhaseTruncatedBody q I sigma2
    let delta := figureOneProposalRadius q sigma2
    let pi := ellGaussianProb K delta sigma2
    _root_.Arlib.IsWarm 2
      (Arlib.condOn
        (balancedRejectedStateMeasure q I sigma2 pi) Set.univ) pi := by
  dsimp only
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  let branch := balancedRejectedStateMeasure q I sigma2 pi
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero
      (accuracyPhaseTruncatedBody_measurable q I sigma2)
      (accuracyPhaseTruncatedBody_convex q I sigma2)
      (accuracyPhaseTruncatedBody_isCompact q I sigma2).isBounded
      (accuracyPhaseTruncatedBody_volume_ne_zero q I hsigma2) hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18
      (accuracyPhaseTruncatedBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have hp : (2 : ENNReal)⁻¹ ≤ branch Set.univ := by
    simpa [branch] using
      balancedRejectedStateMeasure_mass_ge_half q I hsigma2 pi
  have hle : branch ≤ pi := by
    simpa [branch] using balancedRejectedStateMeasure_le q I sigma2 pi
  intro A hA
  rw [Arlib.condOn_def, Measure.restrict_univ,
    Measure.smul_apply, smul_eq_mul]
  have hbranch : branch A ≤ pi A := Measure.le_iff.mp hle A hA
  calc
    (branch Set.univ)⁻¹ * branch A ≤
        (branch Set.univ)⁻¹ * pi A := mul_le_mul' le_rfl hbranch
    _ ≤ ((2 : ENNReal)⁻¹)⁻¹ * pi A := by gcongr
    _ = 2 * pi A := by norm_num

end ArlibCommunity.Algorithms.CV18
