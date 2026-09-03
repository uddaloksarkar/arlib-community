/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorSampleHistory

/-!
# Sample-history shadow including the exact first sample

The phase experiment in CV18 draws its first sample from the exact truncated
Gaussian and then runs `count - 1` retained transitions.  The base history
shadow records transition outputs starting at coordinate zero.  Here the
exact first sample is stored in coordinate zero and tail transition `i`
writes coordinate `i + 1`.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- History initialized with the exact first retained sample in coordinate
zero. -/
def retainedSampleHistoryWithFirst {S : Type*} (x : S) :
    RetainedSampleHistory S :=
  (Function.update (fun _ => none) 0 (some x), some x)

theorem measurable_retainedSampleHistoryWithFirst
    {S : Type*} [MeasurableSpace S] :
    Measurable (retainedSampleHistoryWithFirst :
      S → RetainedSampleHistory S) := by
  apply Measurable.prodMk
  · refine measurable_pi_lambda _ fun j => ?_
    by_cases hj : j = 0
    · subst j
      simpa [retainedSampleHistoryWithFirst, Function.update] using
        (measurable_some : Measurable fun x : S => some x)
    · simpa [retainedSampleHistoryWithFirst, Function.update, hj] using
        (measurable_const : Measurable fun _ : S => (none : Option S))
  · exact measurable_some

@[simp] theorem retainedSampleHistoryWithFirst_state
    {S : Type*} (x : S) :
    retainedSampleHistoryState (retainedSampleHistoryWithFirst x) = some x :=
  rfl

@[simp] theorem retainedSampleHistoryWithFirst_observation_zero
    {S : Type*} (weight : S → ℝ) (x : S) :
    retainedSampleObservation weight 0 (retainedSampleHistoryWithFirst x) =
      weight x := by
  simp [retainedSampleObservation, retainedSampleHistoryWithFirst,
    retainedOptionWeight, Function.update]

@[simp] theorem retainedSampleHistoryWithFirst_toSum_one
    {S : Type*} (weight : S → ℝ) (x : S) :
    retainedSampleHistoryToSum weight 1 (retainedSampleHistoryWithFirst x) =
      (weight x, some x) := by
  apply Prod.ext
  · simp [retainedSampleHistoryToSum]
  · rfl

/-- Forgetting the initialized coordinate record gives the exact first-sample
law mapped into the retained optional state. -/
theorem map_retainedSampleHistoryWithFirst_state
    {S : Type*} [MeasurableSpace S] (initial : Measure S) :
    (initial.map retainedSampleHistoryWithFirst).map
        retainedSampleHistoryState =
      initial.map some := by
  change (initial.map retainedSampleHistoryWithFirst).map Prod.snd =
    initial.map some
  rw [Measure.map_map measurable_snd
    measurable_retainedSampleHistoryWithFirst]
  rfl

/-- The shifted history shadow and the retained-sum shadow have exactly the
same law.  This is the law identity needed for a phase containing an exact
first sample followed by `tail` executable samples. -/
theorem map_iterated_initializedRetainedSampleHistoryKernel_sum
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure S) : ∀ tail,
    (iteratedKernelLaw
      (fun i => retainedSampleHistoryKernel K (i + 1))
      (initial.map retainedSampleHistoryWithFirst) tail).map
        (retainedSampleHistoryToSum weight (tail + 1)) =
      iteratedKernelLaw (fun _ => retainedSumKernel K weight)
        (initial.map fun x => (weight x, some x)) tail := by
  intro tail
  induction tail with
  | zero =>
      simp only [iteratedKernelLaw_zero, zero_add]
      rw [Measure.map_map
        (measurable_retainedSampleHistoryToSum hweight 1)
        measurable_retainedSampleHistoryWithFirst]
      apply Measure.map_congr
      filter_upwards with x
      exact retainedSampleHistoryWithFirst_toSum_one weight x
  | succ tail ih =>
      rw [iteratedKernelLaw_succ, iteratedKernelLaw_succ]
      let old := iteratedKernelLaw
        (fun i => retainedSampleHistoryKernel K (i + 1))
        (initial.map retainedSampleHistoryWithFirst) tail
      have hrecord := retainedSampleHistoryKernel_measurable_and_probability
        K hK hKprob (tail + 1)
      have hsum := retainedSumKernel_measurable_and_probability
        K hK hKprob weight hweight
      have htoOld :=
        measurable_retainedSampleHistoryToSum hweight (tail + 1)
      have htoNew :=
        measurable_retainedSampleHistoryToSum hweight (tail + 1 + 1)
      have hpoint : (fun history : RetainedSampleHistory S =>
          (retainedSampleHistoryKernel K (tail + 1) history).map
            (retainedSampleHistoryToSum weight (tail + 1 + 1))) =
          (fun history => retainedSumKernel K weight
            (retainedSampleHistoryToSum weight (tail + 1) history)) := by
        funext history
        unfold retainedSampleHistoryKernel retainedSumKernel
        have hupdateHistory : Measurable fun next : Option S =>
            retainedSampleHistoryUpdate (tail + 1) history next :=
          (measurable_retainedSampleHistoryUpdate (tail + 1)).comp
            (measurable_const.prodMk measurable_id)
        rw [Measure.map_map htoNew hupdateHistory]
        apply Measure.map_congr
        filter_upwards with next
        apply Prod.ext
        · exact retainedSampleHistory_prefixSum_update weight
            (tail + 1) history next
        · rfl
      calc
        (old.bind (retainedSampleHistoryKernel K (tail + 1))).map
              (retainedSampleHistoryToSum weight (tail + 1 + 1)) =
            old.bind fun history =>
              (retainedSampleHistoryKernel K (tail + 1) history).map
                (retainedSampleHistoryToSum weight (tail + 1 + 1)) :=
          map_bind_eq_bind_map_of_measurable old hrecord.1 htoNew
        _ = old.bind fun history => retainedSumKernel K weight
              (retainedSampleHistoryToSum weight (tail + 1) history) := by
          rw [hpoint]
        _ = (old.map
              (retainedSampleHistoryToSum weight (tail + 1))).bind
              (retainedSumKernel K weight) :=
          (map_bind_eq_bind_comp_state old htoOld hsum.1).symm
        _ = (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
            (initial.map fun x => (weight x, some x)) tail).bind
              (retainedSumKernel K weight) := by rw [ih]

#print axioms measurable_retainedSampleHistoryWithFirst
#print axioms map_retainedSampleHistoryWithFirst_state
#print axioms map_iterated_initializedRetainedSampleHistoryKernel_sum

end ArlibCommunity.Algorithms.CV18
