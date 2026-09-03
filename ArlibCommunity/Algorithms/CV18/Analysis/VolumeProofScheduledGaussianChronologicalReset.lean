/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalResetStep
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledLocalResetDependenceBudget

/-!
# Gaussian phases of the chronological reset reference

This file instantiates the generic public-trace reset step with the accepted
Gaussian endpoint target and the equation-(6) empirical-average moments.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

theorem ae_scheduledResetPairGood_of_nonnegative_of_snd_map_some
    (target : Measure (ℝ × Option (AmbientSpace n)))
    (retained : Measure (AmbientSpace n))
    (hstate : target.map Prod.snd = retained.map some)
    (hnonnegative : ∀ᵐ result ∂target, 0 ≤ result.1) :
    ∀ᵐ result ∂target, ScheduledResetPairGood result := by
  have hsome : ∀ᵐ value ∂retained.map some, value ≠ none :=
    (ae_map_iff measurable_some.aemeasurable
      measurableSet_option_none.compl).2 <| ae_of_all _ fun point => by simp
  rw [← hstate] at hsome
  have hpoint : ∀ᵐ result ∂target, result.2 ≠ none :=
    (ae_map_iff measurable_snd.aemeasurable
      measurableSet_option_none.compl).1 hsome
  filter_upwards [hnonnegative, hpoint] with result hscore hpoint
  constructor
  · exact hscore
  · rw [liveRaw_scheduledResetPairToResult]
    simp [hpoint, max_eq_right hscore]

/-- Full-pair approximate independence transports from the public phase
observation law to the pair-valued reset kernel. -/
theorem approxIndepFun_scheduledResetPairKernel_of_observation
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    (oldStatistic : ScheduledBalancedCoolingTrace q.n → ℝ)
    (hold : Measurable oldStatistic) {eta : ℝ}
    (hind : ApproxIndepFun eta
      Prod.fst Prod.snd
      (sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase))) :
    ApproxIndepFun eta (oldStatistic ∘ Prod.fst) Prod.snd
      (sequentialPairLaw source (scheduledResetPairKernel q I phase)) := by
  let raw := sequentialPairLaw source
    (scheduledBalancedTracePhaseObservationLaw
      figureOneFinalScheduledBalancedParameters q I phase)
  let mapped := fun state : ScheduledBalancedCoolingTrace q.n ×
      Option (ℝ × AmbientSpace q.n) =>
    (state.1, scheduledResetPairOutput state.2)
  have hmapped : Measurable mapped :=
    measurable_fst.prodMk
      (measurable_scheduledResetPairOutput.comp measurable_snd)
  have hind' : ApproxIndepFun eta
      (oldStatistic ∘ Prod.fst)
      (scheduledResetPairOutput ∘ Prod.snd) raw :=
    hind.comp hold measurable_scheduledResetPairOutput
  let pairObs := fun state : ScheduledBalancedCoolingTrace q.n ×
      (ℝ × Option (AmbientSpace q.n)) =>
    (oldStatistic state.1, state.2)
  have hpairObs : Measurable pairObs :=
    (hold.comp measurable_fst).prodMk measurable_snd
  apply ApproxIndepFun.of_map_pair_eq
    (hold.comp measurable_fst)
    (measurable_scheduledResetPairOutput.comp measurable_snd)
    (hold.comp measurable_fst) measurable_snd
  · calc
      raw.map (fun state =>
          (oldStatistic state.1, scheduledResetPairOutput state.2)) =
          raw.map (pairObs ∘ mapped) := by rfl
      _ = (raw.map mapped).map pairObs :=
        (Measure.map_map hpairObs hmapped).symm
      _ = (sequentialPairLaw source
          (scheduledResetPairKernel q I phase)).map (fun state =>
            (oldStatistic state.1, state.2)) := by
        rw [sequentialPairLaw_scheduledResetPairKernel_eq_map]
  · exact hind'

/-- Pair-valued operational output is within the sum of the walk-transition
and equation-(6)/endpoint reset budgets of the accepted reset target. -/
theorem scheduledResetPairKernel_gaussian_leUpTo_acceptedTarget
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    [IsProbabilityMeasure source]
    (accepted : Measure (AmbientSpace q.n)) [IsProbabilityMeasure accepted]
    (hretained : source.map scheduledBalancedTraceRetainedOption =
      accepted.map some)
    (hgood : Arlib.IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q))
      (accepted.map fun point => accuracyScaleFactor q • point)
      (figureOneScheduledSpeedyPiAt q I phase))
    (target : Measure (ℝ × Option (AmbientSpace q.n)))
    [IsProbabilityMeasure target]
    (htarget : MeasureLeUpTo
      ((figureOneScheduledGaussianPhaseTarget q I phase).map
        scheduledResetPairOutput)
      target
      (scheduledResetReferenceError q
        (figureOnePhaseSampleCount q (scheduleValue q phase) - 1) +
          scheduledBalancedStationaryTargetError q)) :
    MeasureLeUpTo
      ((sequentialPairLaw source
        (scheduledResetPairKernel q I phase)).map Prod.snd)
      target
      (figureOneCorrectedTransitionBudget q +
        scheduledResetReferenceError q
          (figureOnePhaseSampleCount q (scheduleValue q phase) - 1) +
        scheduledBalancedStationaryTargetError q) := by
  have hphaseRaw :=
    sequentialPairLaw_gaussian_output_leUpTo_of_retainedSome_warm
      q I phase hphase source accepted hretained <| hgood.mono <| by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [speedyAdjacentWarmConstant_one_le q]
  have hmapped := hphaseRaw.map measurable_scheduledResetPairOutput
  have hseq := sequentialPairLaw_scheduledResetPairKernel_eq_map
    q I phase source
  have hpair : Measurable fun state : ScheduledBalancedCoolingTrace q.n ×
      Option (ℝ × AmbientSpace q.n) =>
      (state.1, scheduledResetPairOutput state.2) :=
    measurable_fst.prodMk
      (measurable_scheduledResetPairOutput.comp measurable_snd)
  have hleft : ((sequentialPairLaw source
      (scheduledResetPairKernel q I phase)).map Prod.snd) =
      (((sequentialPairLaw source
        (scheduledBalancedTracePhaseObservationLaw
          figureOneFinalScheduledBalancedParameters q I phase)).map
            Prod.snd).map scheduledResetPairOutput) := by
    rw [hseq, Measure.map_map measurable_snd hpair,
      Measure.map_map measurable_scheduledResetPairOutput measurable_snd]
    rfl
  rw [hleft]
  simpa only [add_assoc] using hmapped.trans htarget

#print axioms ae_scheduledResetPairGood_of_nonnegative_of_snd_map_some
#print axioms approxIndepFun_scheduledResetPairKernel_of_observation
#print axioms scheduledResetPairKernel_gaussian_leUpTo_acceptedTarget

end

end ArlibCommunity.Algorithms.CV18
