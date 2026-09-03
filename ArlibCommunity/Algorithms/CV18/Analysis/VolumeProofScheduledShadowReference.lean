/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofHistoryPreservingSampleReset
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCollectorPrefixIndependence

/-!
# An exact-shadow reference step for the scheduled collector

This file instantiates the history-preserving reset construction for one
tail sample of the scheduled retained collector.  The reference records an
exact truncated-Gaussian shadow at the new coordinate while preserving the
executable retained state used by the following walk block.

This is deliberately a one-coordinate statement.  Exact coordinate
marginals do not by themselves assert that all shadow coordinates are
independent.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- The exact retained target for a Gaussian cooling sample. -/
noncomputable def scheduledRetainedExactSome
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measure (Option (AmbientSpace q.n)) :=
  (truncatedGaussianProbability q I (scheduleValue q phase)
    (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some

theorem scheduledRetainedExactSome_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    IsProbabilityMeasure (scheduledRetainedExactSome q I phase) := by
  unfold scheduledRetainedExactSome
  exact Measure.isProbabilityMeasure_map measurable_some.aemeasurable

/-- Updating one coordinate of the recorded part of a retained history is
measurable as a two-argument operation. -/
theorem measurable_uncurry_update_retainedHistoryCoordinate
    {S : Type*} [MeasurableSpace S] (i : ℕ) :
    Measurable (Function.uncurry fun history : ℕ → Option S =>
      Function.update history i) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hji : j = i
  · subst j
    simpa [Function.uncurry, Function.update] using
      (measurable_snd : Measurable fun value :
        (ℕ → Option S) × Option S => value.2)
  · simpa [Function.uncurry, Function.update, hji] using
      (show Measurable fun value : (ℕ → Option S) × Option S =>
          value.1 j from by
        convert (measurable_pi_apply j).comp measurable_fst using 1
        funext value
        rfl)

/-- The generic transition-then-record kernel is the collector's ordinary
coordinate-recording kernel. -/
theorem historyOperationalRecordKernel_update_eq_retainedSampleHistoryKernel
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (i : ℕ) :
    historyOperationalRecordKernel K
        (fun history next => Function.update history i next) id =
      retainedSampleHistoryKernel K i := by
  funext history
  rfl

/-- One executable scheduled tail step admits a reference law whose newly
recorded coordinate is exactly distributed as the truncated Gaussian while
the next operational retained-state marginal is unchanged. -/
theorem exists_initializedScheduledRetainedShadowReference
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ) :
    ∃ reference : Measure (RetainedSampleHistory (AmbientSpace q.n)),
      IsProbabilityMeasure reference ∧
      MeasureLeUpTo
        (initializedScheduledRetainedHistoryLaw q I phase (i + 1))
        reference (scheduledRetainedEndpointError q (i + 1)) ∧
      reference.map (fun history => history.1 (i + 1)) =
        scheduledRetainedExactSome q I phase ∧
      reference.map retainedSampleHistoryState =
        (initializedScheduledRetainedHistoryLaw q I phase (i + 1)).map
          retainedSampleHistoryState := by
  let prefixLaw := initializedScheduledRetainedHistoryLaw q I phase i
  let K := figureOneFinalScheduledRetainedOptionKernel q I
    (scheduleValue q phase)
  let target := scheduledRetainedExactSome q I phase
  let record : (ℕ → Option (AmbientSpace q.n)) →
      Option (AmbientSpace q.n) → ℕ → Option (AmbientSpace q.n) :=
    fun history next => Function.update history (i + 1) next
  let readNew : (ℕ → Option (AmbientSpace q.n)) →
      Option (AmbientSpace q.n) := fun history => history (i + 1)
  have hK :=
    figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
      q I (scheduleValue_pos q phase)
  let _ : IsProbabilityMeasure prefixLaw := by
    simpa [prefixLaw] using
      initializedScheduledRetainedHistoryLaw_isProbabilityMeasure
        q I phase i
  let _ : IsProbabilityMeasure target := by
    simpa [target] using
      scheduledRetainedExactSome_isProbabilityMeasure q I phase
  have hiterProb : IsProbabilityMeasure
      (iteratedKernelLaw (fun _ => K) target (i + 1)) := by
    exact iteratedKernelLaw_isProbabilityMeasure (fun _ => K) target
      (by infer_instance) (fun _ => hK.1) (fun _ => hK.2) (i + 1)
  let _ : IsProbabilityMeasure
      (iteratedKernelLaw (fun _ => K) target (i + 1)) := hiterProb
  let _ : IsProbabilityMeasure
      (iteratedKernelLaw
        (fun _ => figureOneFinalScheduledRetainedOptionKernel q I
          (scheduleValue q phase))
        ((truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n)).map some)
        (i + 1)) := by
    simpa [K, target, scheduledRetainedExactSome] using hiterProb
  have hrecord : Measurable (Function.uncurry record) := by
    simpa [record] using
      (measurable_uncurry_update_retainedHistoryCoordinate
        (S := AmbientSpace q.n) (i + 1))
  have hreadNew : Measurable readNew := by
    simpa [readNew] using
      (measurable_pi_apply (i + 1) :
        Measurable fun history : ℕ → Option (AmbientSpace q.n) =>
          history (i + 1))
  have hnext : TVLe
      ((prefixLaw.bind (historyRawNextWithCopyKernel K)).map Prod.snd)
      target (scheduledRetainedEndpointError q (i + 1)) := by
    rw [map_bind_historyRawNextWithCopyKernel_snd prefixLaw K hK.1 hK.2]
    rw [show prefixLaw.map Prod.snd =
        iteratedKernelLaw (fun _ => K)
          (scheduledRetainedExactSome q I phase) i by
      simpa [prefixLaw, K, scheduledRetainedExactSome,
        retainedSampleHistoryState] using
        map_initializedScheduledRetainedHistoryLaw_state q I phase i]
    rw [← iteratedKernelLaw_succ]
    have hendpoint : MeasureLeUpTo
        (iteratedKernelLaw (fun _ => K) target (i + 1)) target
        (scheduledRetainedEndpointError q (i + 1)) := by
      simpa [K, target, scheduledRetainedExactSome,
        scheduledRetainedEndpointError] using
        (iterated_figureOneFinalScheduledRetainedOptionKernel_from_truncated_exact_leUpTo
          q I phase (i + 1))
    exact hendpoint.to_tvLe
  obtain ⟨reference, hreferenceProb, hmlu, hcoordinate, hstate⟩ :=
    exists_shadowRecordedReference_of_nextMarginal_tvLe
      prefixLaw K record id target readNew hK.1 hK.2 hrecord
      measurable_id hreadNew (by
        intro history next
        simp [record, readNew, Function.update]) hnext
  refine ⟨reference, hreferenceProb, ?_, ?_, ?_⟩
  · rw [initializedScheduledRetainedHistoryLaw,
      iteratedKernelLaw_succ]
    change MeasureLeUpTo
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1)))
      reference (scheduledRetainedEndpointError q (i + 1))
    change MeasureLeUpTo
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1)))
      reference (scheduledRetainedEndpointError q (i + 1)) at hmlu
    exact hmlu
  · rw [Measure.map_id] at hcoordinate
    change reference.map (fun history => history.1 (i + 1)) = target at hcoordinate
    simpa only [target] using hcoordinate
  · rw [initializedScheduledRetainedHistoryLaw,
      iteratedKernelLaw_succ]
    change reference.map Prod.snd =
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1))).map Prod.snd
    change reference.map Prod.snd =
      (prefixLaw.bind (retainedSampleHistoryKernel K (i + 1))).map Prod.snd
      at hstate
    exact hstate

#print axioms scheduledRetainedExactSome_isProbabilityMeasure
#print axioms measurable_uncurry_update_retainedHistoryCoordinate
#print axioms historyOperationalRecordKernel_update_eq_retainedSampleHistoryKernel
#print axioms exists_initializedScheduledRetainedShadowReference

end

end ArlibCommunity.Algorithms.CV18
