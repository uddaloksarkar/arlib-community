/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorSecondMoment
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceSlackMoments

/-!
# Sharp scalar-law moment transfer to an executable trace coordinate

This specializes the sharp perturbation algebra to the exact `hsecond`
premise of the unconditional scheduled capstone.  It deliberately leaves
only the law-comparison and its explicit error arithmetic as inputs.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A sufficiently small scalar-law perturbation of the ideal chronological
phase preserves its paper factor, enlarged only by the executable moment
slack. -/
theorem scheduledFigureOneTrace_second_le_executableMomentFactor_of_mapped_tv
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    {epsilon : ENNReal} (hepsilonTop : epsilon ≠ ⊤)
    {B : ℝ} (hB : 0 < B)
    (hscalar : Arlib.TVLe
      ((scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)).map
          (scheduledBalancedTracePhaseVariable q j))
      ((figureOneIdealPhaseLaw q I (figureOneChronologicalPhaseAt q j)).map
        (figureOneIdealPhaseEstimator q
          (figureOneChronologicalPhaseAt q j))) epsilon)
    (hWB : ∀ᵐ trace ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q),
      scheduledBalancedTracePhaseVariable q j trace ≤ B)
    (hidealB : ∀ᵐ samples
        ∂figureOneIdealPhaseLaw q I (figureOneChronologicalPhaseAt q j),
      figureOneIdealPhaseEstimator q (figureOneChronologicalPhaseAt q j)
        samples ≤ B)
    {eta zeta : ℝ} (heta1 : eta < 1)
    (hmeanError : B * epsilon.toReal ≤
      eta * figureOneIdealPhaseMean q I
        (figureOneChronologicalPhaseAt q j))
    (hsecondError : B ^ 2 * epsilon.toReal ≤
      zeta * figureOneIdealPhaseMean q I
        (figureOneChronologicalPhaseAt q j) ^ 2)
    (hfactorBudget :
      figureOneChronologicalMomentFactor q j + zeta ≤
        figureOneChronologicalMomentFactor q j *
          (1 + figureOneExecutableMomentSlack q) * (1 - eta) ^ 2) :
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
      ∂scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)) ≤
      figureOneExecutableMomentFactor q j *
        scheduledFigureOneTraceRawMean q I j ^ 2 := by
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let phase := figureOneChronologicalPhaseAt q j
  let idealLaw := figureOneIdealPhaseLaw q I phase
  let W := scheduledBalancedTracePhaseVariable q j
  let estimator := figureOneIdealPhaseEstimator q phase
  let actualScalar := mu.map W
  let idealScalar := idealLaw.map estimator
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  let _ : IsProbabilityMeasure idealLaw :=
    figureOneIdealPhaseLaw_isProbabilityMeasure q I phase
  let _ : IsProbabilityMeasure actualScalar :=
    Measure.isProbabilityMeasure_map
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
  let _ : IsProbabilityMeasure idealScalar :=
    Measure.isProbabilityMeasure_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
  have hactual0 : ∀ᵐ y ∂actualScalar, 0 ≤ y :=
    (ae_map_iff
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      measurableSet_Ici).2 <| Filter.Eventually.of_forall
        (scheduledBalancedTracePhaseVariable_nonnegative q j)
  have hactualB : ∀ᵐ y ∂actualScalar, y ≤ B :=
    (ae_map_iff
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      measurableSet_Iic).2 hWB
  have hideal0 : ∀ᵐ y ∂idealScalar, 0 ≤ y :=
    (ae_map_iff
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurableSet_Ici).2 <| Filter.Eventually.of_forall
        (figureOneIdealPhaseEstimator_nonneg q phase)
  have hidealScalarB : ∀ᵐ y ∂idealScalar, y ≤ B :=
    (ae_map_iff
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurableSet_Iic).2 hidealB
  have hidealMoments := figureOneIdealPhase_moments q I
    (figureOneSharpAcceleratedMoments q I) phase
  have hidealMean : figureOneIdealPhaseMean q I phase =
      ∫ y, id y ∂idealScalar := by
    rw [integral_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      measurable_id.aestronglyMeasurable]
    simpa only [id_eq] using hidealMoments.1.symm
  have hidealSecond : (∫ y, id y ^ 2 ∂idealScalar) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneIdealPhaseMean q I phase ^ 2 := by
    rw [integral_map
      (figureOneIdealPhaseEstimator_measurable q phase).aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable]
    simpa [phase, figureOneChronologicalMomentFactor] using hidealMoments.2
  have htransport := Arlib.TVLe.second_le_factor_mul_mean_sq_of_ae
    (show Arlib.TVLe actualScalar idealScalar epsilon from hscalar)
    hepsilonTop measurable_id hB hactual0 hactualB hideal0 hidealScalarB
    hidealMean (figureOneIdealPhaseMean_pos q I phase) hidealSecond
    (zero_le_one.trans (figureOneChronologicalMomentFactor_one_le q j))
    (figureOneExecutableMomentSlack_nonneg q) heta1 hmeanError hsecondError
    hfactorBudget
  have hmeanMap : (∫ y, id y ∂actualScalar) =
      scheduledFigureOneTraceRawMean q I j := by
    rw [integral_map
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      measurable_id.aestronglyMeasurable]
    rfl
  have hsecondMap : (∫ y, id y ^ 2 ∂actualScalar) =
      ∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2 ∂mu := by
    rw [integral_map
      (measurable_scheduledBalancedTracePhaseVariable q j).aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable]
    rfl
  change (∫ y, id y ^ 2 ∂actualScalar) ≤
    figureOneChronologicalMomentFactor q j *
      (1 + figureOneExecutableMomentSlack q) *
        (∫ y, id y ∂actualScalar) ^ 2 at htransport
  rw [hmeanMap, hsecondMap] at htransport
  simpa only [mu, figureOneExecutableMomentFactor] using htransport

#print axioms
  scheduledFigureOneTrace_second_le_executableMomentFactor_of_mapped_tv

end ArlibCommunity.Algorithms.CV18
