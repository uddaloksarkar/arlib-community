/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExpectedQueryCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLazyProperFailure
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledProperSemantics

/-! # Expected cost of the schedule-targeted proper block

This is the operational Bellman bound for the actual scheduled executable.
It is uniform in the syntactic proposal cap; the cap can therefore be chosen
later from the one global soft-O query budget.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib.MarkovChains

theorem scheduledAccuracyMetropolisMarkedProposalProgram_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedProposalProgram q sigma2 current proposal).FixedQueryCount
      1 := by
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  apply MembershipOracleProgram.FixedQueryCount.randomReal
  intro coin
  split <;> exact .pure _

theorem scheduledAccuracyMetropolisMarkedBallStep_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).FixedQueryCount
      1 := by
  apply MembershipOracleProgram.FixedQueryCount.randomPoint
  intro proposal
  exact scheduledAccuracyMetropolisMarkedProposalProgram_fixedQueryCount
    q sigma2 current proposal

theorem scheduledAccuracyMetropolisMarkedBallStep_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyMetropolisMarkedBallStep q sigma2 current).CountedStronglyMeasurable
      oracle.query :=
  (scheduledAccuracyMetropolisMarkedBallStep_fixedQueryCount q sigma2 current).countedStronglyMeasurable
    oracle.query
      (scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
        q I oracle sigma2 current)

theorem scheduledAccuracyZeroObservation_fixedQueryCount
    (q : VolumeParams) (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).FixedQueryCount 1 := by
  unfold scheduledAccuracyZeroObservation
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  exact .pure _

private theorem scheduledAccuracyZeroObservation_stronglyMeasurable_for_cost
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).StronglyMeasurable
      oracle.query := by
  simp [scheduledAccuracyZeroObservation,
    MembershipOracleProgram.StronglyMeasurable,
    MembershipOracleProgram.runEstimate]

theorem scheduledAccuracyZeroObservation_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    (scheduledAccuracyZeroObservation q sigma2 current).CountedStronglyMeasurable
      oracle.query :=
  (scheduledAccuracyZeroObservation_fixedQueryCount q sigma2 current).countedStronglyMeasurable
    oracle.query
      (scheduledAccuracyZeroObservation_stronglyMeasurable_for_cost
        q I oracle sigma2 current)

/-- The scheduled capped proper block has a jointly measurable counted law.
The proof follows its raw-proposal recursion, so no deterministic local-cost
multiplier is introduced. -/
theorem cappedScheduledAccuracyProperBlockAux_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (properStride : ℕ) :
    ∀ rawCap remainingProper,
      (Measurable fun current =>
        (cappedScheduledAccuracyProperBlockAux q sigma2 properStride
          rawCap remainingProper current).run oracle.query) ∧
      (∀ current,
        (cappedScheduledAccuracyProperBlockAux q sigma2 properStride
          rawCap remainingProper current).CountedStronglyMeasurable
            oracle.query) := by
  let Q := lazyProperProposalGaussianAux
    (figureOneScheduledPhaseBody q I sigma2)
    (figureOneScheduledPhaseBody_measurable q I sigma2)
    (figureOneScheduledProposalRadius q sigma2) sigma2
  intro rawCap
  induction rawCap with
  | zero =>
      intro remainingProper
      constructor
      · simp only [cappedScheduledAccuracyProperBlockAux,
          MembershipOracleProgram.run]
        exact Measure.measurable_dirac.comp
          (measurable_const.prodMk measurable_const)
      · intro current
        rw [cappedScheduledAccuracyProperBlockAux]
        trivial
  | succ rawCap ih =>
      intro remainingProper
      cases remainingProper with
      | zero =>
          let observation (current : AmbientSpace q.n) :=
            scheduledAccuracyZeroObservation q sigma2 current
          let next (z : AmbientSpace q.n × ℝ) : MembershipOracleProgram q.n
              (Option (ℝ × AmbientSpace q.n)) :=
            .pure (some (z.2, z.1))
          have hobservationMeas : Measurable fun current =>
              (observation current).run oracle.query := by
            apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
              oracle.query observation 1
            · intro current
              exact scheduledAccuracyZeroObservation_fixedQueryCount
                q sigma2 current
            · intro current
              exact scheduledAccuracyZeroObservation_stronglyMeasurable
                q I oracle sigma2 current
            · rw [show (fun current =>
                    (observation current).runEstimate oracle.query) =
                  fun _ : AmbientSpace q.n => Measure.dirac 0 by
                    funext current
                    exact runEstimate_scheduledAccuracyZeroObservation
                      q I oracle sigma2 current]
              exact measurable_const
          have hnextMeas : Measurable fun z => (next z).run oracle.query := by
            simp only [next, MembershipOracleProgram.run]
            exact Measure.measurable_dirac.comp <|
              (measurable_some.comp <|
                measurable_snd.prodMk measurable_fst).prodMk measurable_const
          constructor
          · simpa only [observation, next,
                cappedScheduledAccuracyProperBlockAux] using
              MembershipOracleProgram.measurable_run_bind_param
                oracle.query observation next hobservationMeas
                (fun current =>
                  scheduledAccuracyZeroObservation_countedStronglyMeasurable
                    q I oracle sigma2 current)
                hnextMeas (fun _ => by trivial)
          · intro current
            simp only [cappedScheduledAccuracyProperBlockAux]
            apply MembershipOracleProgram.CountedStronglyMeasurable.bind
              (scheduledAccuracyZeroObservation_countedStronglyMeasurable
                q I oracle sigma2 current)
              (fun _ => by trivial)
            have hnextAt : Measurable fun observed : ℝ =>
                (next (current, observed)).run oracle.query :=
              hnextMeas.comp
                ((measurable_const : Measurable fun _ : ℝ => current).prodMk
                  measurable_id)
            exact hnextAt
      | succ remainingProper =>
          let step (current : AmbientSpace q.n) :=
            scheduledAccuracyMetropolisMarkedBallStep q sigma2 current
          let next (z : AmbientSpace q.n × (Bool × AmbientSpace q.n)) :=
            if z.2.1 then
              match remainingProper with
              | 0 => cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                  rawCap 0 z.2.2
              | nextRemaining + 1 =>
                  cappedScheduledAccuracyProperBlockAux q sigma2 properStride
                    rawCap (nextRemaining + 1) z.2.2
            else cappedScheduledAccuracyProperBlockAux q sigma2 properStride
              rawCap (remainingProper + 1) z.2.2
          have hstepMeas : Measurable fun current =>
              (step current).run oracle.query := by
            apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
              oracle.query step 1
            · intro current
              exact scheduledAccuracyMetropolisMarkedBallStep_fixedQueryCount
                q sigma2 current
            · intro current
              exact scheduledAccuracyMetropolisMarkedBallStep_stronglyMeasurable
                q I oracle sigma2 current
            · rw [show (fun current => (step current).runEstimate oracle.query) =
                  Q by
                    funext current
                    exact runEstimate_scheduledAccuracyMetropolisMarkedBallStep_eq_lazyProperAux
                      q I oracle hsigma2 current]
              exact Q.measurable
          have hnext : ∀ z, (next z).CountedStronglyMeasurable oracle.query := by
            rintro ⟨current, mark, point⟩
            cases mark with
            | false => exact (ih (remainingProper + 1)).2 point
            | true =>
                cases remainingProper with
                | zero => exact (ih 0).2 point
                | succ nextRemaining => exact (ih (nextRemaining + 1)).2 point
          have hnextMeas : Measurable fun z => (next z).run oracle.query := by
            dsimp only [next]
            rw [show (fun z : AmbientSpace q.n ×
                    (Bool × AmbientSpace q.n) =>
                  (if z.2.1 = true then
                    match remainingProper with
                    | 0 => cappedScheduledAccuracyProperBlockAux q sigma2
                        properStride rawCap 0 z.2.2
                    | nextRemaining + 1 =>
                        cappedScheduledAccuracyProperBlockAux q sigma2
                          properStride rawCap (nextRemaining + 1) z.2.2
                  else cappedScheduledAccuracyProperBlockAux q sigma2
                    properStride rawCap (remainingProper + 1) z.2.2).run
                      oracle.query) =
                fun z => if z.2.1 = true then
                  (match remainingProper with
                  | 0 => cappedScheduledAccuracyProperBlockAux q sigma2
                      properStride rawCap 0 z.2.2
                  | nextRemaining + 1 =>
                      cappedScheduledAccuracyProperBlockAux q sigma2
                        properStride rawCap (nextRemaining + 1) z.2.2).run
                    oracle.query
                else (cappedScheduledAccuracyProperBlockAux q sigma2
                  properStride rawCap (remainingProper + 1) z.2.2).run
                    oracle.query by
                      funext z
                      split <;> rfl]
            apply Measurable.ite
            · exact (measurable_fst.comp measurable_snd)
                (measurableSet_singleton true)
            · cases remainingProper with
              | zero => exact (ih 0).1.comp (measurable_snd.comp measurable_snd)
              | succ nextRemaining =>
                  exact (ih (nextRemaining + 1)).1.comp
                    (measurable_snd.comp measurable_snd)
            · exact (ih (remainingProper + 1)).1.comp
                (measurable_snd.comp measurable_snd)
          constructor
          · simp only [cappedScheduledAccuracyProperBlockAux]
            change Measurable fun current =>
              ((step current).bind fun result => next (current, result)).run
                oracle.query
            exact MembershipOracleProgram.measurable_run_bind_param
              oracle.query step next hstepMeas
              (fun current =>
                scheduledAccuracyMetropolisMarkedBallStep_countedStronglyMeasurable
                  q I oracle sigma2 current)
              hnextMeas hnext
          · intro current
            simp only [cappedScheduledAccuracyProperBlockAux]
            apply MembershipOracleProgram.CountedStronglyMeasurable.bind
              (scheduledAccuracyMetropolisMarkedBallStep_countedStronglyMeasurable
                q I oracle sigma2 current)
              (fun result => hnext (current, result))
            exact hnextMeas.comp (measurable_const.prodMk measurable_id)

theorem cappedScheduledAccuracyProperBlock_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (rawCap properStride : ℕ) :
    (Measurable fun current =>
      (cappedScheduledAccuracyProperBlock q sigma2 rawCap properStride current).run
        oracle.query) ∧
    (∀ current,
      (cappedScheduledAccuracyProperBlock q sigma2 rawCap properStride current).CountedStronglyMeasurable
        oracle.query) :=
  cappedScheduledAccuracyProperBlockAux_countedMeasurable
    q I oracle hsigma2 properStride rawCap properStride

end ArlibCommunity.Algorithms.CV18
