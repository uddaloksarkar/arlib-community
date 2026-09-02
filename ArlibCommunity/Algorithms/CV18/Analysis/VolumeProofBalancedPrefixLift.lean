/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProgramPrefix

/-!
# Prefix invisibility through the balanced retry stack

This strengthens local-cap equality to compositional `QueryPrefixEq`, so the
fact can be transported through balanced retries and cooling binds.
-/

namespace ArlibCommunity.Algorithms.CV18

open MembershipOracleProgram

theorem cappedAccuracyProperCollectWeightsAux_queryPrefixEq_of_lt
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ∀ budget rawCap₁ rawCap₂ remainingProper samples total current,
      budget < rawCap₁ → budget < rawCap₂ →
      QueryPrefixEq budget
        (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
          rawCap₁ remainingProper samples total current)
        (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
          rawCap₂ remainingProper samples total current) := by
  intro budget
  induction budget with
  | zero =>
      intro rawCap₁ rawCap₂ remainingProper samples total current hcap₁ hcap₂
      obtain ⟨rawCap₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₁ ≠ 0)
      obtain ⟨rawCap₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₂ ≠ 0)
      cases samples with
      | zero =>
          rw [cappedAccuracyProperCollectWeightsAux,
            cappedAccuracyProperCollectWeightsAux]
          exact .pure 0 _
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyImportanceObservation, MembershipOracleProgram.bind]
              exact .queryZero _ _ _ _
          | succ remainingProper =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyMetropolisMarkedBallStep,
                accuracyMetropolisMarkedProposalProgram,
                MembershipOracleProgram.bind]
              apply QueryPrefixEq.randomPoint
              intro proposal
              exact .queryZero _ _ _ _
  | succ budget ih =>
      intro rawCap₁ rawCap₂ remainingProper samples total current hcap₁ hcap₂
      obtain ⟨rawCap₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₁ ≠ 0)
      obtain ⟨rawCap₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₂ ≠ 0)
      have hcap₁' : budget < rawCap₁ := by omega
      have hcap₂' : budget < rawCap₂ := by omega
      cases samples with
      | zero =>
          rw [cappedAccuracyProperCollectWeightsAux,
            cappedAccuracyProperCollectWeightsAux]
          exact .pure (budget + 1) _
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyImportanceObservation, MembershipOracleProgram.bind]
              apply QueryPrefixEq.querySucc
              intro inside
              exact ih rawCap₁ rawCap₂ properStride samples _ current
                hcap₁' hcap₂'
          | succ remainingProper =>
              cases remainingProper with
              | zero =>
                  simp only [cappedAccuracyProperCollectWeightsAux,
                    accuracyMetropolisMarkedBallStep,
                    accuracyMetropolisMarkedProposalProgram,
                    MembershipOracleProgram.bind]
                  apply QueryPrefixEq.randomPoint
                  intro proposal
                  apply QueryPrefixEq.querySucc
                  intro inside
                  apply QueryPrefixEq.randomReal
                  intro coin
                  split_ifs <;> simp only [MembershipOracleProgram.bind]
                  all_goals apply ih <;> assumption
              | succ nextRemaining =>
                  simp only [cappedAccuracyProperCollectWeightsAux,
                    accuracyMetropolisMarkedBallStep,
                    accuracyMetropolisMarkedProposalProgram,
                    MembershipOracleProgram.bind]
                  apply QueryPrefixEq.randomPoint
                  intro proposal
                  apply QueryPrefixEq.querySucc
                  intro inside
                  apply QueryPrefixEq.randomReal
                  intro coin
                  split_ifs <;> simp only [MembershipOracleProgram.bind]
                  all_goals apply ih <;> assumption

theorem cappedAccuracyProperCollectWeights_queryPrefixEq_of_le
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride samples : ℕ)
    (current : AmbientSpace q.n) {budget proposalCap₁ proposalCap₂ : ℕ}
    (hcap₁ : budget ≤ proposalCap₁) (hcap₂ : budget ≤ proposalCap₂) :
    QueryPrefixEq budget
      (cappedAccuracyProperCollectWeights q sigma2 weight
        (proposalCap₁ + 1) properStride samples current)
      (cappedAccuracyProperCollectWeights q sigma2 weight
        (proposalCap₂ + 1) properStride samples current) := by
  unfold cappedAccuracyProperCollectWeights
  apply cappedAccuracyProperCollectWeightsAux_queryPrefixEq_of_lt
  · omega
  · omega

end ArlibCommunity.Algorithms.CV18
