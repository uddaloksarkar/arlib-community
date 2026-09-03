/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianEndpointMean
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceFullGoodBad

/-!
# First moment of the complete scheduled Gaussian phase

The paper-faithful complete-phase target draws its first retained point from
the exact truncated Gaussian and then uses the executable killed Markov tail.
Here it is identified with the retained-sum shadow so its mean can be reduced
to the endpoint marginals proved in `VolumeProofScheduledGaussianEndpointMean`.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib _root_.Arlib.MarkovChains

/-- Killing an accumulated nonnegative total only on the final dead event
costs at most its `L²` norm times the square root of the death probability.
This is the usable replacement for multiplying the tiny failure probability
by the enormous compact-support supremum of an early Gaussian ratio. -/
theorem integral_retainedLiveTotal_loss_le_sqrt
    {S : Type*} [MeasurableSpace S]
    (mu : Measure (ℝ × Option S)) [IsProbabilityMeasure mu]
    (htotal0 : ∀ᵐ state ∂mu, 0 ≤ state.1)
    (htotalMem : MemLp (fun state : ℝ × Option S => state.1) 2 mu) :
    (∫ state, state.1 ∂mu) - ∫ state, retainedLiveTotal state ∂mu ≤
      Real.sqrt (∫ state, state.1 ^ 2 ∂mu) *
        Real.sqrt (mu.real {state | state.2 = none}) := by
  let dead : Set (ℝ × Option S) := {state | state.2 = none}
  let killed : ℝ × Option S → ℝ :=
    dead.indicator (fun _ => (1 : ℝ))
  have hdead : MeasurableSet dead :=
    measurable_snd measurableSet_option_none
  have hkilled : Measurable killed := measurable_const.indicator hdead
  have hkilledMem : MemLp killed 2 mu := by
    apply MemLp.of_bound hkilled.aestronglyMeasurable 1
    filter_upwards with state
    by_cases hstate : state ∈ dead
    · simp [killed, Set.indicator_of_mem hstate]
    · simp [killed, Set.indicator_of_notMem hstate]
  have hfstInt : Integrable (fun state : ℝ × Option S => state.1) mu :=
    htotalMem.integrable (by norm_num)
  have hliveInt : Integrable (retainedLiveTotal (S := S)) mu := by
    apply Integrable.mono' hfstInt
      measurable_retainedLiveTotal.aestronglyMeasurable
    filter_upwards [htotal0] with state hstate0
    rcases state with ⟨total, state⟩
    cases state with
    | none =>
        simpa [retainedLiveTotal] using hstate0
    | some value =>
        simpa [retainedLiveTotal, Real.norm_eq_abs,
          abs_of_nonneg hstate0] using hstate0
  have hloss : (∫ state, state.1 ∂mu) -
        ∫ state, retainedLiveTotal state ∂mu =
      ∫ state, state.1 * killed state ∂mu := by
    rw [← integral_sub hfstInt hliveInt]
    apply integral_congr_ae
    filter_upwards with state
    rcases state with ⟨total, state⟩
    cases state <;> simp [retainedLiveTotal, killed, dead]
  have hkilledSq : (∫ state, killed state ^ 2 ∂mu) = mu.real dead := by
    calc
      (∫ state, killed state ^ 2 ∂mu) = ∫ state, killed state ∂mu := by
        apply integral_congr_ae
        filter_upwards with state
        by_cases hstate : state ∈ dead <;>
          simp [killed, Set.indicator_of_mem, Set.indicator_of_notMem, hstate]
      _ = mu.real dead := by
        simpa [killed] using integral_indicator_const (μ := mu) (1 : ℝ) hdead
  rw [hloss]
  have hCS := integral_mul_le_sqrt_mul_sqrt htotalMem hkilledMem
  rw [hkilledSq] at hCS
  exact hCS

set_option maxHeartbeats 1000000 in
/-- The common-tail Gaussian phase target is exactly the killed retained-sum
shadow, followed by the public output and averaging maps. -/
theorem figureOneScheduledGaussianPhaseTarget_eq_map_retainedSumKernel
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    let count := figureOnePhaseSampleCount q (scheduleValue q phase)
    let weight := gaussianRatioWeight (n := q.n) (scheduleValue q phase)
      (scheduleValue q (phase + 1))
    let K := figureOneFinalScheduledRetainedOptionKernel q I
      (scheduleValue q phase)
    let initial :=
      (truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map
          (fun x => (weight x, some x))
    figureOneScheduledGaussianPhaseTarget q I phase =
      (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        initial (count - 1)).map
          (balancedCoolingAverage count ∘ retainedSumOutput) := by
  dsimp only
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  let s := scheduleValue q phase
  let t := scheduleValue q (phase + 1)
  let weight := gaussianRatioWeight (n := q.n) s t
  let exact : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I s (scheduleValue_pos q phase)
  let first : Measure (Option (AmbientSpace q.n)) := exact.map some
  let K := figureOneFinalScheduledRetainedOptionKernel q I s
  let R := retainedSumKernel K weight
  let initialMap : AmbientSpace q.n →
      ℝ × Option (AmbientSpace q.n) := fun x => (weight x, some x)
  let initial := exact.map initialMap
  let shadow := iteratedKernelLaw (fun _ => R) initial (count - 1)
  let tail : Option (AmbientSpace q.n) →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun result =>
    match result with
    | none => Measure.dirac none
    | some point =>
        scheduledBalancedTransitionCollectLaw q I s weight
          (figureOneFinalScheduledBalancedParameters.proposalCap q s)
          (figureOneFinalScheduledBalancedParameters.properStride q s)
          (figureOneFinalScheduledBalancedParameters.retryLimit q s)
          (count - 1) (weight point) (accuracyScaleFactor q • point)
  have hs : 0 < s := scheduleValue_pos q phase
  have hweight : Measurable weight := measurable_gaussianRatioWeight s t
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I hs
  have hR := retainedSumKernel_measurable_and_probability
    K hK.1 hK.2 weight hweight
  have hinitialMap : Measurable initialMap :=
    hweight.prodMk measurable_some
  have hout : Measurable
      (retainedSumOutput (S := AmbientSpace q.n)) :=
    measurable_retainedSumOutput
  have havg : Measurable
      (balancedCoolingAverage (n := q.n) count) :=
    measurable_balancedCoolingAverage count
  have htailCollect :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I hs hweight
      (figureOneFinalScheduledBalancedParameters.proposalCap q s)
      (figureOneFinalScheduledBalancedParameters.properStride q s)
      (figureOneFinalScheduledBalancedParameters.retryLimit q s) (count - 1)
  have htail : Measurable tail := by
    have hsome : Measurable fun point : AmbientSpace q.n =>
        scheduledBalancedTransitionCollectLaw q I s weight
          (figureOneFinalScheduledBalancedParameters.proposalCap q s)
          (figureOneFinalScheduledBalancedParameters.properStride q s)
          (figureOneFinalScheduledBalancedParameters.retryLimit q s)
          (count - 1) (weight point) (accuracyScaleFactor q • point) := by
      exact htailCollect.1.comp <| hweight.prodMk <|
        (measurable_const : Measurable fun _ : AmbientSpace q.n =>
          accuracyScaleFactor q).smul measurable_id
    convert Measurable.optionElim
      (Measure.dirac (none : Option (ℝ × AmbientSpace q.n))) hsome using 1
    funext result
    cases result <;> rfl
  have hcollector : ∀ x,
      tail (some x) =
        (iteratedKernelLaw (fun _ => R)
          (Measure.dirac (initialMap x)) (count - 1)).map
            retainedSumOutput := by
    intro x
    have hKeq : scheduledBalancedRetainedOptionKernel q I s
        (figureOneFinalScheduledBalancedParameters.proposalCap q s)
        (figureOneFinalScheduledBalancedParameters.properStride q s)
        (figureOneFinalScheduledBalancedParameters.retryLimit q s) = K := by
      funext state
      cases state <;> rfl
    have hcollect :=
      scheduledBalancedTransitionCollectLaw_eq_map_retainedSumKernel
        q I hs hweight
        (figureOneFinalScheduledBalancedParameters.proposalCap q s)
        (figureOneFinalScheduledBalancedParameters.properStride q s)
        (figureOneFinalScheduledBalancedParameters.retryLimit q s)
        (count - 1) (weight x) x
    rw [hKeq] at hcollect
    simpa [tail, R, weight, s, initialMap] using hcollect
  have hiter : Measurable fun x : AmbientSpace q.n =>
      iteratedKernelLaw (fun _ => R) (Measure.dirac (initialMap x))
        (count - 1) :=
    (iteratedKernelLaw_dirac_measurable_and_probability
      (fun _ => R) (fun _ => hR.1) (fun _ _ => hR.2 _) (count - 1)).1.comp
        hinitialMap
  have hbindIter : exact.bind (fun x =>
      iteratedKernelLaw (fun _ => R) (Measure.dirac (initialMap x))
        (count - 1)) = shadow := by
    simpa [shadow, initial] using
      bind_iteratedKernelLaw_dirac_eq_iteratedKernelLaw_map
        (fun _ => R) (fun _ => hR.1) (fun _ _ => hR.2 _)
        exact initialMap hinitialMap (count - 1)
  have hfirstBind : first.bind tail = shadow.map retainedSumOutput := by
    calc
      first.bind tail = exact.bind (tail ∘ some) := by
        exact map_bind_eq_bind_comp_state exact measurable_some htail
      _ = exact.bind (fun x =>
          (iteratedKernelLaw (fun _ => R)
            (Measure.dirac (initialMap x)) (count - 1)).map
              retainedSumOutput) := by
        apply Measure.bind_congr_right
        filter_upwards with x
        exact hcollector x
      _ = (exact.bind fun x =>
          iteratedKernelLaw (fun _ => R)
            (Measure.dirac (initialMap x)) (count - 1)).map
              retainedSumOutput :=
        (map_bind_eq_bind_map_of_measurable exact hiter hout).symm
      _ = shadow.map retainedSumOutput := by rw [hbindIter]
  change (first.bind tail).map (balancedCoolingAverage count) =
    shadow.map (balancedCoolingAverage count ∘ retainedSumOutput)
  rw [hfirstBind, Measure.map_map havg hout]

#print axioms figureOneScheduledGaussianPhaseTarget_eq_map_retainedSumKernel
#print axioms integral_retainedLiveTotal_loss_le_sqrt

end ArlibCommunity.Algorithms.CV18
