/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorInitializedSampleHistory
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorConditionedTransition

/-!
# Prefix independence for the scheduled initialized collector

This instantiates CV18 Lemma 7.17(b) for every tail coordinate of a phase
whose exact first sample is stored at coordinate zero.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

/-- Conditioned one-step error at tail time `i`. -/
noncomputable def scheduledRetainedConditioningError
    (q : VolumeParams) (i : ℕ) : ENNReal :=
  figureOneCorrectedTransitionBudget q +
    2 * (scheduledBalancedStationaryTargetError q +
      i • figureOneCorrectedTransitionBudget q)

theorem scheduledRetainedConditioningError_ne_top
    (q : VolumeParams) (i : ℕ) :
    scheduledRetainedConditioningError q i ≠ ⊤ := by
  unfold scheduledRetainedConditioningError
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.ofReal_ne_top
  · apply ENNReal.mul_ne_top (by norm_num)
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · rw [nsmul_eq_mul]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        ENNReal.ofReal_ne_top

/-- The initialized coordinate-recording law for one scheduled phase. -/
noncomputable def initializedScheduledRetainedHistoryLaw
    (q : VolumeParams) (I : VolumeInput q.n) (phase tail : ℕ) :
    Measure (RetainedSampleHistory (AmbientSpace q.n)) :=
  iteratedKernelLaw
    (fun i => retainedSampleHistoryKernel
      (figureOneFinalScheduledRetainedOptionKernel q I
        (scheduleValue q phase)) (i + 1))
    ((truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
        retainedSampleHistoryWithFirst)
    tail

theorem initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phase tail : ℕ) :
    IsProbabilityMeasure
      (initializedScheduledRetainedHistoryLaw q I phase tail) := by
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  let initial : Measure (RetainedSampleHistory (AmbientSpace q.n)) :=
    exact.map retainedSampleHistoryWithFirst
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  have hinitial : IsProbabilityMeasure initial := by
    dsimp [initial]
    exact Measure.isProbabilityMeasure_map
      measurable_retainedSampleHistoryWithFirst.aemeasurable
  simpa [initializedScheduledRetainedHistoryLaw, exact, initial, K] using
    (iteratedKernelLaw_isProbabilityMeasure
      (fun i => retainedSampleHistoryKernel K (i + 1)) initial hinitial
      (fun i =>
        (retainedSampleHistoryKernel_measurable_and_probability
          K hK.1 hK.2 (i + 1)).1)
      (fun i history =>
        (retainedSampleHistoryKernel_measurable_and_probability
          K hK.1 hK.2 (i + 1)).2 history)
      tail)

/-- The retained state marginal at tail time `i` is exactly the killed chain
from the exact first sample after `i` transitions. -/
theorem map_initializedScheduledRetainedHistoryLaw_state
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ) :
    (initializedScheduledRetainedHistoryLaw q I phase i).map
        retainedSampleHistoryState =
      iteratedKernelLaw
        (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
          (scheduleValue q phase))
        ((truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
        i := by
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  rw [initializedScheduledRetainedHistoryLaw,
    map_iterated_initializedRetainedSampleHistoryKernel_state
      K hK.1 hK.2]
  rw [map_retainedSampleHistoryWithFirst_state]

/-- CV18 Lemma 7.17(b) for tail sample `i + 1`, transported to the final
history horizon. -/
theorem approxIndepFun_initializedScheduledRetainedHistory_prefix_next
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    {i tail : ℕ} (hi : i < tail) :
    ApproxIndepFun
      (scheduledRetainedConditioningError q i +
        scheduledRetainedConditioningError q i).toReal
      (sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) (i + 1))
      (retainedSampleObservation
        (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1))) (i + 1))
      (initializedScheduledRetainedHistoryLaw q I phase tail) := by
  let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
    (scheduleValue q (phase + 1))
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q phase)
      (scheduleValue_pos q phase)
  let exactSome : Measure (Option (AmbientSpace q.n)) := exact.map some
  let initial : Measure (RetainedSampleHistory (AmbientSpace q.n)) :=
    exact.map retainedSampleHistoryWithFirst
  let rho := initializedScheduledRetainedHistoryLaw q I phase i
  let delta := scheduledRetainedConditioningError q i
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  have hrho : IsProbabilityMeasure rho := by
    simpa [rho] using
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
        q I phase i
  have hexactSome : IsProbabilityMeasure exactSome := by
    dsimp [exactSome]
    exact Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  let _ : IsProbabilityMeasure rho := hrho
  let _ : IsProbabilityMeasure exactSome := hexactSome
  have hbase := approxIndepFun_history_next_of_state_warm_leUpTo
    rho retainedSampleHistoryState measurable_snd hK.1 hK.2 exactSome
      (scheduledRetainedConditioningError_ne_top q i)
      (fun mu hmu hwarm => by
        let _ : IsProbabilityMeasure mu := hmu
        apply
          bind_figureOneFinalScheduledRetainedOptionKernel_leUpTo_of_warm_iterated_truncated
            q I phase i mu
        simpa [rho, K, exactSome, exact,
          map_initializedScheduledRetainedHistoryLaw_state q I phase i] using
          hwarm)
  have hpair := hbase.comp
    (measurable_sequentialPrefixSum
      (fun t => measurable_retainedSampleObservation
        (measurable_gaussianRatioWeight (scheduleValue q phase)
          (scheduleValue q (phase + 1))) t) (i + 1))
    (measurable_retainedOptionWeight
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1))))
  apply initializedRetainedSampleHistory_approxIndep_prefix_next_final
    K hK.1 hK.2 weight
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1))) initial hi
  simpa only [rho, initial, exact, exactSome, K, weight, delta,
    initializedScheduledRetainedHistoryLaw, Function.comp_def] using hpair

#print axioms scheduledRetainedConditioningError_ne_top
#print axioms initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
#print axioms map_initializedScheduledRetainedHistoryLaw_state
#print axioms
  approxIndepFun_initializedScheduledRetainedHistory_prefix_next

end ArlibCommunity.Algorithms.CV18
