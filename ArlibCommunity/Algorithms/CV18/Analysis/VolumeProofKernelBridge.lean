/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStationary
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisGaussian

/-!
# The executable CV18 proposal is the standard lazy Metropolis proposal

The executable Figure-1 walk was defined independently of the abstract
continuous Markov-chain library.  This file removes two representation
differences needed before the abstract mixing theorem can be applied:

* normalizing Lebesgue measure on a closed proposal ball gives the same
  probability measure as normalizing it on the open ball used by
  `Arlib.MarkovChains.metropolisGaussian`; the boundary sphere is null;
* the executable acceptance probability is exactly one half of
  `Arlib.MarkovChains.metropolisAccept`, including the indicator of the fixed
  truncated body.

The remaining bridge is trajectory-level: relate a fixed number of these raw
lazy steps to sufficiently many proper speedy steps and compose the resulting
per-sample errors through the dependent cooling schedule.
-/

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

open Arlib.MarkovChains
open scoped ENNReal

/-- Normalizing the implementation's closed proposal ball is identical to
normalizing the abstract chain's open ball. -/
theorem centeredClosedBallMeasure_eq_openBall {n : ℕ} [NeZero n]
    {radius : ℝ} (hradius : 0 < radius) :
    centeredClosedBallMeasure n radius =
      (volume (Metric.ball (0 : AmbientSpace n) radius))⁻¹ •
        volume.restrict (Metric.ball 0 radius) := by
  let finite : FiniteMeasure (AmbientSpace n) :=
    centeredClosedBallFiniteMeasure n radius
  have hfinite : finite ≠ 0 := by
    intro hzero
    have huniv : (finite : Measure (AmbientSpace n)) Set.univ = 0 := by
      rw [hzero]
      rfl
    change volume.restrict (Metric.closedBall (0 : AmbientSpace n) radius)
      Set.univ = 0 at huniv
    rw [Measure.restrict_apply_univ] at huniv
    exact (Metric.measure_closedBall_pos volume (0 : AmbientSpace n) hradius).ne' huniv
  have hae : Metric.closedBall (0 : AmbientSpace n) radius =ᵐ[volume]
      Metric.ball 0 radius := by
    apply (ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall ?_
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne).symm
    rw [Measure.addHaar_closedBall_eq_addHaar_ball]
  unfold centeredClosedBallMeasure
  change (finite.normalize : Measure (AmbientSpace n)) = _
  rw [finite.toMeasure_normalize_eq_of_nonzero hfinite]
  have hmass : (finite.mass : ENNReal) =
      volume (Metric.ball (0 : AmbientSpace n) radius) := by
    rw [FiniteMeasure.ennreal_mass]
    change volume.restrict (Metric.closedBall (0 : AmbientSpace n) radius) Set.univ = _
    rw [Measure.restrict_apply_univ,
      Measure.addHaar_closedBall_eq_addHaar_ball]
  rw [← Measure.coe_nnreal_smul, ENNReal.coe_inv
    (finite.mass_nonzero_iff.mpr hfinite), hmass]
  exact congrArg
    (fun mu : Measure (AmbientSpace n) =>
      (volume (Metric.ball (0 : AmbientSpace n) radius))⁻¹ • mu)
    (Measure.restrict_congr_set hae)

/-- After translation, the executable proposal measure is the usual uniform
measure on the open ball about the current state. -/
theorem uniformClosedBallMeasure_eq_openBall {n : ℕ} [NeZero n]
    (current : AmbientSpace n) {radius : ℝ} (hradius : 0 < radius) :
    uniformClosedBallMeasure n current radius =
      (volume (Metric.ball current radius))⁻¹ •
        volume.restrict (Metric.ball current radius) := by
  have hvolume : volume (Metric.ball (0 : AmbientSpace n) radius) =
      volume (Metric.ball current radius) :=
    (volume_ball_eq current radius).symm
  have hpre : (fun z : AmbientSpace n => current + z) ⁻¹'
      Metric.ball current radius = Metric.ball 0 radius := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have hrestrict := Measure.restrict_map
    (μ := (volume : Measure (AmbientSpace n)))
    (f := fun z : AmbientSpace n => current + z)
    (s := Metric.ball current radius)
    (by fun_prop) measurableSet_ball
  rw [hpre] at hrestrict
  unfold uniformClosedBallMeasure
  rw [centeredClosedBallMeasure_eq_openBall hradius, Measure.map_smul,
    hvolume]
  exact congrArg
    (fun mu : Measure (AmbientSpace n) =>
      (volume (Metric.ball current radius))⁻¹ • mu)
    (hrestrict.symm.trans (by rw [map_add_left_eq_self]))

/-- The program's body-filtered acceptance coefficient is exactly one half
of the standard Metropolis coefficient.  Thus laziness is represented by the
coin threshold in the executable and by `lazy` in the abstract kernel. -/
theorem ofReal_truncatedMetropolisAcceptance_eq_half_metropolisAccept
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    ENNReal.ofReal
        (truncatedMetropolisAcceptance q I sigma2 current proposal) =
      (2 : ENNReal)⁻¹ *
        (truncatedBody q I).indicator
          (fun y => metropolisAccept sigma2 current y) proposal := by
  by_cases hp : proposal ∈ truncatedBody q I
  · rw [Set.indicator_of_mem hp]
    unfold truncatedMetropolisAcceptance
    rw [Set.indicator_of_mem hp]
    rw [metropolisAccept_eq_ofReal]
    unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
    unfold gaussianWeightReal
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
    rw [div_eq_mul_inv, mul_comm]
  · rw [Set.indicator_of_notMem hp]
    unfold truncatedMetropolisAcceptance
    rw [Set.indicator_of_notMem hp]
    simp

end ArlibCommunity.Algorithms.CV18

#print axioms ArlibCommunity.Algorithms.CV18.centeredClosedBallMeasure_eq_openBall
#print axioms ArlibCommunity.Algorithms.CV18.uniformClosedBallMeasure_eq_openBall
#print axioms ArlibCommunity.Algorithms.CV18.ofReal_truncatedMetropolisAcceptance_eq_half_metropolisAccept
