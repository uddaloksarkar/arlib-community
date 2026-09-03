/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.FiniteReferenceSequence
import ArlibCommunity.Algorithms.CV18.Analysis.Background.HistoryPreservingReset
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofResetReferenceBaseCapstone
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianResetJoint
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTerminalResetJoint

/-!
# A chronological reset reference for the scheduled trace

This file performs the outer, phase-by-phase exact-chance construction used
in CV18.  A first reset supplies the equation-(6) law of the empirical phase
average.  A second history-preserving reset changes only the retained endpoint
to the accepted stationary law from which the following scheduled phase is
run.  Thus old phase scores and the new score marginal are preserved exactly.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib
open scoped ENNReal

noncomputable section

/-- Forget the failure wrapper while retaining both the live scalar output
and optional endpoint.  On the reference laws below the endpoint is almost
surely present. -/
def scheduledResetPairOutput
    (result : Option (ℝ × AmbientSpace n)) : ℝ × Option (AmbientSpace n) :=
  (figureOneScheduledTraceLiveRawOutput result, optionSnd result)

theorem measurable_scheduledResetPairOutput :
    Measurable (scheduledResetPairOutput (n := n)) :=
  measurable_figureOneScheduledTraceLiveRawOutput.prodMk measurable_optionSnd

/-- Reassemble a phase result after resetting its optional endpoint. -/
def scheduledResetPairToResult
    (result : ℝ × Option (AmbientSpace n)) :
    Option (ℝ × AmbientSpace n) :=
  result.2.map fun point => (result.1, point)

theorem measurable_scheduledResetPairToResult :
    Measurable (scheduledResetPairToResult (n := n)) := by
  unfold scheduledResetPairToResult
  convert Measurable.optionCases
    (0 : AmbientSpace n)
    (noneValue := fun _ : ℝ => (none : Option (ℝ × AmbientSpace n)))
    (someValue := fun result : ℝ × AmbientSpace n =>
      some (result.1, result.2))
    measurable_const
    (measurable_some.comp (measurable_fst.prodMk measurable_snd)) using 1
  funext result
  cases result.2 <;> rfl

@[simp] theorem optionSnd_scheduledResetPairToResult
    (result : ℝ × Option (AmbientSpace n)) :
    optionSnd (scheduledResetPairToResult result) = result.2 := by
  unfold scheduledResetPairToResult
  cases result.2 <;> rfl

@[simp] theorem liveRaw_scheduledResetPairToResult
    (result : ℝ × Option (AmbientSpace n)) :
    figureOneScheduledTraceLiveRawOutput
        (scheduledResetPairToResult result) =
      if result.2 = none then 0 else max 0 result.1 := by
  unfold scheduledResetPairToResult
  cases result.2 <;> rfl

/-- The exact Gaussian and normalized accepted endpoint laws differ by the
single stationary-target error already allocated in the scheduled boundary
budget. -/
theorem scheduledRetainedExactSome_tvLe_acceptedSome
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    TVLe (scheduledRetainedExactSome q I phase)
      ((figureOneScheduledAcceptedTargetAt q I phase).map some)
      (scheduledBalancedStationaryTargetError q) := by
  have htv := scheduledBalancedAccuracyGaussianAcceptedTargetLaw_tv
    q I (scheduleValue_pos q phase)
  have hmapped := htv.symm.map measurable_some
  simpa [scheduledRetainedExactSome, figureOneScheduledAcceptedTargetAt,
    figureOneScheduledSpeedyPiAt] using hmapped

/-- Reset only the endpoint of a joint score/endpoint law.  The score
marginal is preserved, while the new endpoint is exactly the accepted target
used by the next scheduled phase. -/
theorem exists_acceptedEndpointResetJoint
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (joint : Measure (Option (ℝ × AmbientSpace q.n)))
    [IsProbabilityMeasure joint]
    (hstate : joint.map optionSnd = scheduledRetainedExactSome q I phase) :
    ∃ target : Measure (ℝ × Option (AmbientSpace q.n)),
      IsProbabilityMeasure target ∧
      MeasureLeUpTo (joint.map scheduledResetPairOutput) target
        (scheduledBalancedStationaryTargetError q) ∧
      target.map Prod.fst =
        joint.map figureOneScheduledTraceLiveRawOutput ∧
      target.map Prod.snd =
        (figureOneScheduledAcceptedTargetAt q I phase).map some := by
  let paired := joint.map (scheduledResetPairOutput (n := q.n))
  let accepted := (figureOneScheduledAcceptedTargetAt q I phase).map some
  let _ : IsProbabilityMeasure paired :=
    Measure.isProbabilityMeasure_map
      (measurable_scheduledResetPairOutput (n := q.n)).aemeasurable
  let _ : IsProbabilityMeasure accepted :=
    let _ := figureOneScheduledAcceptedTargetAt_isProbabilityMeasure q I phase
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hpairedState : paired.map Prod.snd =
      scheduledRetainedExactSome q I phase := by
    calc
      paired.map Prod.snd = joint.map optionSnd := by
        rw [Measure.map_map measurable_snd
          (measurable_scheduledResetPairOutput (n := q.n))]
        rfl
      _ = _ := hstate
  have htv : TVLe (paired.map Prod.snd) accepted
      (scheduledBalancedStationaryTargetError q) := by
    rw [hpairedState]
    exact scheduledRetainedExactSome_tvLe_acceptedSome q I phase
  obtain ⟨target, htargetProb, hscore, htargetState, htargetTV⟩ :=
    exists_historyPreservingReset_of_tvLe paired accepted htv
  refine ⟨target, htargetProb, MeasureLeUpTo.of_tvLe htargetTV, ?_,
    htargetState⟩
  calc
    target.map Prod.fst = paired.map Prod.fst := hscore
    _ = joint.map figureOneScheduledTraceLiveRawOutput := by
      rw [Measure.map_map measurable_fst
        (measurable_scheduledResetPairOutput (n := q.n))]
      rfl

#print axioms scheduledRetainedExactSome_tvLe_acceptedSome
#print axioms exists_acceptedEndpointResetJoint

end

end ArlibCommunity.Algorithms.CV18
