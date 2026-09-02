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

/-- Changing the artificial local proposal cap above the outer budget is
invisible through all balanced retries. -/
theorem balancedAccuracyRetryCollectAux_queryPrefixEq_of_le
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride retryLimit : ℕ) :
    ∀ samples attempts total current budget proposalCap₁ proposalCap₂,
      budget ≤ proposalCap₁ → budget ≤ proposalCap₂ →
      QueryPrefixEq budget
        (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap₁
          properStride retryLimit attempts samples total current)
        (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap₂
          properStride retryLimit attempts samples total current) := by
  intro samples
  induction samples using Nat.strong_induction_on with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          intro attempts total current budget proposalCap₁ proposalCap₂ hcap₁ hcap₂
          rw [balancedAccuracyRetryCollectAux,
            balancedAccuracyRetryCollectAux]
          exact .pure budget _
      | succ future =>
          intro attempts
          induction attempts with
          | zero =>
              intro total current budget proposalCap₁ proposalCap₂ hcap₁ hcap₂
              rw [balancedAccuracyRetryCollectAux,
                balancedAccuracyRetryCollectAux]
              exact .pure budget _
          | succ attempts ihAttempts =>
              intro total current budget proposalCap₁ proposalCap₂ hcap₁ hcap₂
              simp only [balancedAccuracyRetryCollectAux]
              have hblock := cappedAccuracyProperCollectWeights_queryPrefixEq_of_le
                q sigma2 (fun _ => 0) properStride 1 current hcap₁ hcap₂
              apply hblock.bind
              intro block
              cases block with
              | none => exact .pure budget _
              | some value =>
                  rcases value with ⟨ignored, mixed⟩
                  apply (QueryPrefixEq.refl budget
                    (balancedAccuracyGaussianRejectionAttempt q sigma2 mixed)).bind
                  intro result
                  by_cases hresult : result.1 = true
                  · simp only [hresult, if_true]
                    exact ihSamples future (by omega) retryLimit
                      (total + weight result.2) mixed budget proposalCap₁
                        proposalCap₂ hcap₁ hcap₂
                  · have hfalse : result.1 = false :=
                      Bool.eq_false_of_not_eq_true hresult
                    simp only [hfalse, Bool.false_eq_true, if_false]
                    exact ihAttempts total mixed budget proposalCap₁ proposalCap₂
                      hcap₁ hcap₂

theorem balancedAccuracyRetryCollect_queryPrefixEq_of_le
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) {budget proposalCap₁ proposalCap₂ : ℕ}
    (hcap₁ : budget ≤ proposalCap₁) (hcap₂ : budget ≤ proposalCap₂) :
    QueryPrefixEq budget
      (balancedAccuracyRetryCollect q sigma2 weight proposalCap₁
        properStride retryLimit samples current)
      (balancedAccuracyRetryCollect q sigma2 weight proposalCap₂
        properStride retryLimit samples current) := by
  unfold balancedAccuracyRetryCollect
  apply (balancedAccuracyRetryCollectAux_queryPrefixEq_of_le
    q sigma2 weight properStride retryLimit samples retryLimit 0 current budget
      proposalCap₁ proposalCap₂ hcap₁ hcap₂).bind
  intro result
  exact .pure budget _

end ArlibCommunity.Algorithms.CV18
