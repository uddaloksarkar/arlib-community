/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLazyProperClock

/-!
# A capped executable proper-step walk for CV18

This file exposes the proper-proposal bit in the membership-oracle program
itself and uses it to run a requested number of proper steps subject to a
deterministic raw-query cap.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- The executable proposal program with the proper-proposal bit retained.
A proposal is proper exactly when it lies in the fixed truncated body. A
Metropolis rejection on that branch is still marked proper. -/
noncomputable def truncatedMetropolisMarkedProposalProgram (q : VolumeParams)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .query proposal fun inside =>
    .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
      if inside = true ∧ ‖proposal‖ ≤ Real.sqrt (terminalVariance q) then
        .pure (true,
          if coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
          then proposal else current)
      else .pure (false, current)

/-- One executable lazy Metropolis proposal with its proper bit retained. -/
noncomputable def truncatedMetropolisMarkedBallStep (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
  .randomPoint
    (uniformClosedBallMeasure q.n current (figureOneProposalRadius q sigma2))
    inferInstance fun proposal =>
      truncatedMetropolisMarkedProposalProgram q sigma2 current proposal

/-- Forgetting the mark in the proposal program is definitionally the
existing executable proposal program. -/
theorem truncatedMetropolisMarkedProposalProgram_map_snd
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    (truncatedMetropolisMarkedProposalProgram q sigma2 current proposal).bind
        (fun p => .pure p.2) =
      truncatedMetropolisProposalProgram q sigma2 current proposal := by
  unfold truncatedMetropolisMarkedProposalProgram
    truncatedMetropolisProposalProgram
  simp only [MembershipOracleProgram.bind]
  congr 1
  funext inside
  congr 1
  funext coin
  by_cases hproper :
      inside = true ∧ ‖proposal‖ ≤ Real.sqrt (terminalVariance q)
  · simp [MembershipOracleProgram.bind, hproper]
  · have hfull : ¬ (inside = true ∧
        ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
        coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal) := by
      intro h
      exact hproper ⟨h.1, h.2.1⟩
    simp [MembershipOracleProgram.bind, hproper, hfull]

/-- Forgetting the mark in a complete step is definitionally the existing
Figure-1 step. -/
theorem truncatedMetropolisMarkedBallStep_map_snd
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (truncatedMetropolisMarkedBallStep q sigma2 current).bind
        (fun p => .pure p.2) =
      truncatedMetropolisBallStep q sigma2 current := by
  unfold truncatedMetropolisMarkedBallStep truncatedMetropolisBallStep
    MembershipOracleProgram.bind
  congr 1
  funext proposal
  exact truncatedMetropolisMarkedProposalProgram_map_snd
    q sigma2 current proposal

theorem truncatedMetropolisMarkedProposalProgram_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    (truncatedMetropolisMarkedProposalProgram q sigma2 current proposal).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.query
  intro inside
  apply MembershipOracleProgram.QueryBound.randomReal
  intro coin
  split <;> exact .pure _ 0

theorem truncatedMetropolisMarkedBallStep_queryBound
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (truncatedMetropolisMarkedBallStep q sigma2 current).QueryBound 1 := by
  apply MembershipOracleProgram.QueryBound.randomPoint
  intro proposal
  exact truncatedMetropolisMarkedProposalProgram_queryBound
    q sigma2 current proposal

/-- Run until `properSteps` marked proposals have occurred, but abort with
`none` after `rawCap` raw proposals. -/
noncomputable def cappedProperMetropolisBallWalk (q : VolumeParams)
    (sigma2 : ℝ) : ℕ → ℕ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  | _, 0, current => .pure (some current)
  | 0, _ + 1, _ => .pure none
  | rawCap + 1, properSteps + 1, current =>
      (truncatedMetropolisMarkedBallStep q sigma2 current).bind fun result =>
        cappedProperMetropolisBallWalk q sigma2 rawCap
          (if result.1 then properSteps else properSteps + 1) result.2

/-- The capped proper-step walk makes at most `rawCap` membership queries,
independently of whether it succeeds. -/
theorem cappedProperMetropolisBallWalk_queryBound
    (q : VolumeParams) (sigma2 : ℝ) : ∀ rawCap properSteps current,
    (cappedProperMetropolisBallWalk q sigma2 rawCap properSteps current).QueryBound
      rawCap := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro properSteps current
      cases properSteps <;> exact .pure _ 0
  | succ rawCap ih =>
      intro properSteps current
      cases properSteps with
      | zero => exact .pure _ (rawCap + 1)
      | succ properSteps =>
          simp only [cappedProperMetropolisBallWalk]
          simpa [Nat.add_comm] using
            (truncatedMetropolisMarkedBallStep_queryBound q sigma2 current).bind
              (fun result =>
                ih (if result.1 then properSteps else properSteps + 1) result.2)

end ArlibCommunity.Algorithms.CV18
