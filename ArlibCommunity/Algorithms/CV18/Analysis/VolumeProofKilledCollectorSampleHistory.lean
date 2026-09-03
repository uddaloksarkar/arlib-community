/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledCollectorMean

/-!
# Sample-history shadow for a killed collector

The executable retry collector retains only its accumulated total.  To use
the sequential approximate-independence calculation one needs all individual
observations on one probability space.  This module augments the retained
optional-state chain by an infinite, initially empty coordinate record.  The
`i`-th transition writes exactly its returned optional state in coordinate
`i`; after death the usual absorbing optional kernel therefore records zero
observations.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A coordinate record together with the current retained optional state. -/
abbrev RetainedSampleHistory (S : Type*) := (ℕ → Option S) × Option S

/-- Write the next retained state into coordinate `i` and carry it forward. -/
def retainedSampleHistoryUpdate {S : Type*} (i : ℕ)
    (history : RetainedSampleHistory S) (next : Option S) :
    RetainedSampleHistory S :=
  (Function.update history.1 i next, next)

theorem measurable_retainedSampleHistoryUpdate
    {S : Type*} [MeasurableSpace S] (i : ℕ) :
    Measurable fun value : RetainedSampleHistory S × Option S =>
      retainedSampleHistoryUpdate i value.1 value.2 := by
  apply Measurable.prodMk
  · refine measurable_pi_lambda _ fun j => ?_
    by_cases hji : j = i
    · subst j
      simpa [retainedSampleHistoryUpdate] using
        (measurable_snd : Measurable fun value :
          RetainedSampleHistory S × Option S => value.2)
    · convert ((measurable_pi_apply j).comp
        (measurable_fst.comp measurable_fst) :
          Measurable fun value : RetainedSampleHistory S × Option S =>
            value.1.1 j) using 1
      funext value
      simp [retainedSampleHistoryUpdate, Function.update, hji]
  · exact measurable_snd

/-- One step of the coordinate-recording shadow. -/
noncomputable def retainedSampleHistoryKernel
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (i : ℕ) :
    RetainedSampleHistory S → Measure (RetainedSampleHistory S) :=
  fun history => (K history.2).map
    (retainedSampleHistoryUpdate i history)

theorem retainedSampleHistoryKernel_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state)) (i : ℕ) :
    Measurable (retainedSampleHistoryKernel K i) ∧
      ∀ history, IsProbabilityMeasure
        (retainedSampleHistoryKernel K i history) := by
  have hupdate : Measurable fun value :
      RetainedSampleHistory S × Option S =>
        retainedSampleHistoryUpdate i value.1 value.2 :=
    measurable_retainedSampleHistoryUpdate i
  constructor
  · unfold retainedSampleHistoryKernel
    exact measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun history => hKprob history.2) hupdate
  · intro history
    unfold retainedSampleHistoryKernel
    let _ : IsProbabilityMeasure (K history.2) := hKprob history.2
    exact Measure.isProbabilityMeasure_map
      (hupdate.comp (measurable_const.prodMk measurable_id)).aemeasurable

/-- Forget the coordinate record and keep the retained optional state. -/
def retainedSampleHistoryState {S : Type*} :
    RetainedSampleHistory S → Option S := Prod.snd

/-- Recording sample coordinates does not alter the retained optional-state
chain at any finite horizon. -/
theorem map_iterated_retainedSampleHistoryKernel_state
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (initial : Measure (RetainedSampleHistory S)) : ∀ steps,
    (iteratedKernelLaw (fun i => retainedSampleHistoryKernel K i)
      initial steps).map retainedSampleHistoryState =
    iteratedKernelLaw (fun _ => K)
      (initial.map retainedSampleHistoryState) steps := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, iteratedKernelLaw_succ]
      let old := iteratedKernelLaw
        (fun i => retainedSampleHistoryKernel K i) initial steps
      have hrecord := retainedSampleHistoryKernel_measurable_and_probability
        K hK hKprob steps
      have hpoint : (fun history : RetainedSampleHistory S =>
          (retainedSampleHistoryKernel K steps history).map
            retainedSampleHistoryState) =
          K ∘ retainedSampleHistoryState := by
        funext history
        unfold retainedSampleHistoryKernel retainedSampleHistoryState
        have hupdate : Measurable fun next : Option S =>
            retainedSampleHistoryUpdate steps history next :=
          (measurable_retainedSampleHistoryUpdate steps).comp
            (measurable_const.prodMk measurable_id)
        rw [Measure.map_map measurable_snd hupdate]
        change Measure.map id (K history.2) = K history.2
        exact Measure.map_id
      calc
        (old.bind (retainedSampleHistoryKernel K steps)).map
              retainedSampleHistoryState =
            old.bind fun history =>
              (retainedSampleHistoryKernel K steps history).map
                retainedSampleHistoryState :=
          map_bind_eq_bind_map_of_measurable old hrecord.1 measurable_snd
        _ = old.bind (K ∘ retainedSampleHistoryState) := by rw [hpoint]
        _ = (old.map retainedSampleHistoryState).bind K :=
          (map_bind_eq_bind_comp_state old measurable_snd hK).symm
        _ = (iteratedKernelLaw (fun _ => K)
            (initial.map retainedSampleHistoryState) steps).bind K := by rw [ih]

/-- The observation stored in coordinate `i`, assigning zero to death. -/
def retainedSampleObservation {S : Type*} (weight : S → ℝ) (i : ℕ)
    (history : RetainedSampleHistory S) : ℝ :=
  retainedOptionWeight weight (history.1 i)

theorem measurable_retainedSampleObservation
    {S : Type*} [MeasurableSpace S] {weight : S → ℝ}
    (hweight : Measurable weight) (i : ℕ) :
    Measurable (retainedSampleObservation weight i) := by
  exact (measurable_retainedOptionWeight hweight).comp <|
    (measurable_pi_apply i).comp measurable_fst

/-- Project a coordinate history to its accumulated prefix total and current
retained state. -/
def retainedSampleHistoryToSum {S : Type*} (weight : S → ℝ) (steps : ℕ)
    (history : RetainedSampleHistory S) : ℝ × Option S :=
  (∑ i ∈ Finset.range steps, retainedSampleObservation weight i history,
    history.2)

theorem measurable_retainedSampleHistoryToSum
    {S : Type*} [MeasurableSpace S] {weight : S → ℝ}
    (hweight : Measurable weight) (steps : ℕ) :
    Measurable (retainedSampleHistoryToSum weight steps) := by
  exact ((Finset.range steps).measurable_fun_sum fun i _ =>
    measurable_retainedSampleObservation hweight i).prodMk measurable_snd

/-- The newly written observation is precisely the zero-filled weight of the
new retained state. -/
@[simp] theorem retainedSampleObservation_update_same
    {S : Type*} (weight : S → ℝ) (i : ℕ)
    (history : RetainedSampleHistory S) (next : Option S) :
    retainedSampleObservation weight i
        (retainedSampleHistoryUpdate i history next) =
      retainedOptionWeight weight next := by
  change retainedOptionWeight weight
      (Function.update history.1 i next i) = retainedOptionWeight weight next
  simp [Function.update]

/-- Writing coordinate `i` leaves every earlier coordinate unchanged. -/
@[simp] theorem retainedSampleObservation_update_of_lt
    {S : Type*} (weight : S → ℝ) {j i : ℕ} (hji : j < i)
    (history : RetainedSampleHistory S) (next : Option S) :
    retainedSampleObservation weight j
        (retainedSampleHistoryUpdate i history next) =
      retainedSampleObservation weight j history := by
  change retainedOptionWeight weight
      (Function.update history.1 i next j) =
    retainedOptionWeight weight (history.1 j)
  simp [Function.update, hji.ne]

/-- Updating coordinate `i` extends the recorded prefix sum by exactly the
new zero-filled observation. -/
theorem retainedSampleHistory_prefixSum_update
    {S : Type*} (weight : S → ℝ) (i : ℕ)
    (history : RetainedSampleHistory S) (next : Option S) :
    (∑ j ∈ Finset.range (i + 1),
        retainedSampleObservation weight j
          (retainedSampleHistoryUpdate i history next)) =
      (∑ j ∈ Finset.range i,
        retainedSampleObservation weight j history) +
        retainedOptionWeight weight next := by
  rw [Finset.sum_range_succ, retainedSampleObservation_update_same]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact retainedSampleObservation_update_of_lt weight
    (Finset.mem_range.mp hj) history next

/-- At every horizon, projecting the coordinate-recording shadow to its
prefix sum gives exactly the retained-sum shadow.  Thus the individual
coordinates used by the approximate-independence calculation represent the
same executable collector total, rather than an auxiliary estimator. -/
theorem map_iterated_retainedSampleHistoryKernel_sum
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (RetainedSampleHistory S)) : ∀ steps,
    (iteratedKernelLaw (fun i => retainedSampleHistoryKernel K i)
      initial steps).map (retainedSampleHistoryToSum weight steps) =
    iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      (initial.map (retainedSampleHistoryToSum weight 0)) steps := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, iteratedKernelLaw_succ]
      let old := iteratedKernelLaw
        (fun i => retainedSampleHistoryKernel K i) initial steps
      have hrecord := retainedSampleHistoryKernel_measurable_and_probability
        K hK hKprob steps
      have hsum := retainedSumKernel_measurable_and_probability
        K hK hKprob weight hweight
      have htoOld := measurable_retainedSampleHistoryToSum hweight steps
      have htoNew := measurable_retainedSampleHistoryToSum hweight (steps + 1)
      have hpoint : (fun history : RetainedSampleHistory S =>
          (retainedSampleHistoryKernel K steps history).map
            (retainedSampleHistoryToSum weight (steps + 1))) =
          (fun history => retainedSumKernel K weight
            (retainedSampleHistoryToSum weight steps history)) := by
        funext history
        unfold retainedSampleHistoryKernel retainedSumKernel
        have hupdateHistory : Measurable fun next : Option S =>
            retainedSampleHistoryUpdate steps history next :=
          (measurable_retainedSampleHistoryUpdate steps).comp
            (measurable_const.prodMk measurable_id)
        rw [Measure.map_map htoNew hupdateHistory]
        apply Measure.map_congr
        filter_upwards with next
        apply Prod.ext
        · exact retainedSampleHistory_prefixSum_update weight steps history next
        · rfl
      calc
        (old.bind (retainedSampleHistoryKernel K steps)).map
              (retainedSampleHistoryToSum weight (steps + 1)) =
            old.bind fun history =>
              (retainedSampleHistoryKernel K steps history).map
                (retainedSampleHistoryToSum weight (steps + 1)) :=
          map_bind_eq_bind_map_of_measurable old hrecord.1 htoNew
        _ = old.bind fun history => retainedSumKernel K weight
              (retainedSampleHistoryToSum weight steps history) := by
          rw [hpoint]
        _ = (old.map (retainedSampleHistoryToSum weight steps)).bind
              (retainedSumKernel K weight) :=
          (map_bind_eq_bind_comp_state old htoOld hsum.1).symm
        _ = (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
            (initial.map (retainedSampleHistoryToSum weight 0)) steps).bind
              (retainedSumKernel K weight) := by rw [ih]

#print axioms retainedSampleHistoryKernel_measurable_and_probability
#print axioms map_iterated_retainedSampleHistoryKernel_state
#print axioms retainedSampleHistory_prefixSum_update
#print axioms map_iterated_retainedSampleHistoryKernel_sum

end ArlibCommunity.Algorithms.CV18
