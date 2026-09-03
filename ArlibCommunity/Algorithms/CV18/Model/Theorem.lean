/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Prior
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGlobalResetReferenceExists

/-!
# CV18 Theorem 1.1

This is the headline audit surface.  The statement below mentions only
objects defined under `Model/`: the input promise, oracle-program semantics,
success event, schedule certificate, and exact query rate.  Its proof selects
the concrete scheduled implementation whose analysis is developed under
`Analysis/`.

The exact displayed rate retains all protected logarithmic factors.  Removing
them gives the paper's `O*(roundness * n^3 / eps^2)` notation; for a
well-rounded body with universal `roundness`, this is `O*(n^3 / eps^2)`.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- Accuracy and worst-case membership-query guarantee for one uniform
volume algorithm at a specified model-level rate. -/
def VolumeGuarantee (algorithm : VolumeAlgorithm)
    (rate : VolumeParams → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q : VolumeParams) (I : VolumeInput q.n)
      (oracle : MembershipOracle I), WellRounded q I →
        1 - q.p ≤ outcomeProbability
          (volumeAlgorithmLaw algorithm q I oracle) (accurateOutcome q I) ∧
        ∃ calls, (algorithm q).QueryBound calls ∧
          calls ≤ Nat.ceil (C * rate q)

/-- Cousins--Vempala 2018, Theorem 1.1: there is a membership-oracle volume
algorithm succeeding with probability at least `1-p`, with the exact
polylogarithmic refinement of the paper's `O*` query bound.

The schedule is existentially packaged with evidence that its phase count is
the first terminal index; the algorithm is likewise selected before the body
and its membership oracle are quantified. -/
theorem cv18TheoremOneOne :
    ∃ (schedule : (q : VolumeParams) → VolumeTerminalSchedule q)
      (algorithm : VolumeAlgorithm),
      VolumeGuarantee algorithm
        (fun q => scheduledComplexityRate (schedule q)) := by
  let schedule : (q : VolumeParams) → VolumeTerminalSchedule q := fun q =>
    { steps := terminalPhaseSteps q
      reaches := by
        simpa [modelScheduleValue, scheduleValue] using
          scheduleValue_terminalPhaseSteps q
      first := by
        intro k hk
        simpa [modelScheduleValue, scheduleValue] using
          scheduleValue_ne_terminal_of_lt_terminalPhaseSteps q hk }
  let algorithm : VolumeAlgorithm :=
    amplifyOracleProgram figureOneFinalScheduledCappedValueProgram
  refine ⟨schedule, algorithm, ?_⟩
  obtain ⟨C, hC, htheorem⟩ := volumeTheorem_finalScheduled
  refine ⟨C, hC, ?_⟩
  intro q I oracle hrounded
  have hrate : scheduledComplexityRate (schedule q) =
      volumeScheduledBaseComplexityRate q * protectedLog (1 / q.p) := by
    simp only [scheduledComplexityRate, scheduledBaseComplexityRate,
      scheduledAccuracyLog, scheduledSafeRetryCount,
      scheduledPerSampleMixingError, scheduledDependentEpsilon,
      scheduledDependentAlpha, scheduledDependentPhaseCount,
      scheduledMaxSampleCount, scheduledFixedSampleCount,
      scheduledSampleCount, schedule,
      volumeScheduledBaseComplexityRate, figureOneScheduledAccuracyLog,
      figureOneScheduledCoreError, figureOneScheduledRadialError,
      figureOneCorrectedBlockMixingError, figureOneSafeRetryCount,
      figureOnePerSampleMixingError, figureOneDependentEpsilon,
      figureOneDependentAlpha, figureOneDependentPhaseCount,
      figureOneDependentMaxSampleCount, figureOneFixedSampleCount,
      figureOneSampleCount]
  simpa only [algorithm, hrate] using htheorem q I oracle hrounded

#modelClosureOfType cv18TheoremOneOne
#print axioms cv18TheoremOneOne

end ArlibCommunity.Algorithms.CV18
