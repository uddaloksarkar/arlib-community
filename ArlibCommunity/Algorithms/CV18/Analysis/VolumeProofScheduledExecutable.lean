/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduleTargetedKLS
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryProgram

/-! # Executable balanced sampler at schedule-targeted geometry -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

/-- Marked Metropolis proposal using the schedule-targeted radial test. -/
noncomputable def scheduledAccuracyMetropolisMarkedProposalProgram
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .query proposal fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧
          ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖proposal‖ ≤ figureOneScheduledPhaseRadius q sigma2 then
        .pure (true,
          if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
          then proposal else current)
      else .pure (false, current)

noncomputable def scheduledAccuracyMetropolisMarkedBallStep
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .randomPoint
    (uniformClosedBallMeasure q.n current
      (figureOneScheduledProposalRadius q sigma2)) inferInstance fun proposal =>
      scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal

theorem scheduledAccuracyMetropolisMarkedProposalProgram_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal).QueryBound
      1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  split <;> exact .pure _ 0

theorem scheduledAccuracyMetropolisMarkedBallStep_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.randomPoint
  intro proposal
  exact scheduledAccuracyMetropolisMarkedProposalProgram_queryBound
    q sigma2 current proposal

/-- The dummy endpoint observation retained by the proper-proposal clock. -/
noncomputable def scheduledAccuracyZeroObservation
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n ℝ :=
  let target := (accuracyScaleFactor q)⁻¹ • current
  .query target fun _ => .pure 0

theorem scheduledAccuracyZeroObservation_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  exact .pure _ 0

/-- Capped proper-step block at the new body and proposal radius. -/
noncomputable def cappedScheduledAccuracyProperBlockAux
    (q : VolumeParams) (sigma2 : ℝ) (properStride : ℕ) :
    ℕ → ℕ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | 0, _, _ => .pure none
  | rawCap + 1, 0, current =>
      (scheduledAccuracyZeroObservation q sigma2 current).bind fun observed =>
        .pure (some (observed, current))
  | rawCap + 1, remainingProper + 1, current =>
      (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).bind
        fun result =>
          if result.1 then
            match remainingProper with
            | 0 => cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                rawCap 0 result.2
            | nextRemaining + 1 =>
                cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                  rawCap (nextRemaining + 1) result.2
          else cappedScheduledAccuracyProperBlockAux q sigma2 properStride
            rawCap (remainingProper + 1) result.2
termination_by rawCap remainingProper current => rawCap

noncomputable def cappedScheduledAccuracyProperBlock
    (q : VolumeParams) (sigma2 : ℝ) (rawCap properStride : ℕ)
    (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  cappedScheduledAccuracyProperBlockAux q sigma2 properStride
    rawCap properStride current

/-- Schedule-targeted balanced KLS rejection. -/
noncomputable def scheduledBalancedAccuracyGaussianRejectionAttempt
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  let c := accuracyScaleFactor q
  let target := c⁻¹ • current
  .query target fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧
          ‖target‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖target‖ ≤ figureOneScheduledPhaseRadius q sigma2 ∧
          ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ *
            Arlib.MarkovChains.gaussianScaleAcceptance sigma2 c target then
        .pure (true, target)
      else .pure (false, target)

theorem scheduledBalancedAccuracyGaussianRejectionAttempt_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 current).QueryBound
      1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  split <;> exact .pure _ 0

/-- Finite balanced retries whose proper blocks and rejection tests both use
the schedule-targeted geometry. -/
noncomputable def scheduledBalancedAccuracyRetryCollectAux
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ℕ → ℕ → ℝ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | _, 0, total, current => .pure (some (total, current))
  | 0, _ + 1, _, _ => .pure none
  | attempts + 1, samples + 1, total, current =>
      (cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
        properStride current).bind fun block =>
        match block with
        | none => .pure none
        | some (_, mixed) =>
            (scheduledBalancedAccuracyGaussianRejectionAttempt
              q sigma2 mixed).bind fun result =>
                if result.1 then
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit retryLimit samples
                    (total + weight result.2) mixed
                else
                  scheduledBalancedAccuracyRetryCollectAux q sigma2 weight
                    proposalCap properStride retryLimit attempts
                    (samples + 1) total mixed
termination_by attempts samples total current => (samples, attempts)

noncomputable def scheduledBalancedAccuracyRetryCollect
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollectAux q sigma2 weight proposalCap
    properStride retryLimit retryLimit samples 0 current).bind fun result =>
      .pure (balancedAccuracyRetryOutput q result)

#print axioms scheduledAccuracyMetropolisMarkedBallStep_queryBound
#print axioms scheduledBalancedAccuracyGaussianRejectionAttempt_queryBound

end ArlibCommunity.Algorithms.CV18
