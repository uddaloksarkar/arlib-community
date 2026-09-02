/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedBaseCounted

/-!
# Local proposal caps are invisible below the global cutoff

The finite balanced syntax uses a local raw-proposal counter solely to make
each retry structurally finite.  CV18 instead stops the complete execution at
one global query budget.  This file records the basic operational prefix fact:
two local caps larger than the remaining outer budget give exactly the same
globally capped proper collector.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- An outer query cutoff cannot observe the precise value of a larger local
raw-proposal cap. -/
theorem cappedAccuracyProperCollectWeightsAux_withQueryCap_eq_of_lt
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride : ℕ) :
    ∀ budget rawCap₁ rawCap₂ remainingProper samples total current,
      budget < rawCap₁ → budget < rawCap₂ →
      (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
        rawCap₁ remainingProper samples total current).withQueryCap budget =
      (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
        rawCap₂ remainingProper samples total current).withQueryCap budget := by
  intro budget
  induction budget with
  | zero =>
      intro rawCap₁ rawCap₂ remainingProper samples total current hcap₁ hcap₂
      obtain ⟨rawCap₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₁ ≠ 0)
      obtain ⟨rawCap₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₂ ≠ 0)
      cases samples with
      | zero =>
          simp only [cappedAccuracyProperCollectWeightsAux]
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyImportanceObservation, MembershipOracleProgram.bind,
                MembershipOracleProgram.withQueryCap]
          | succ remainingProper =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyMetropolisMarkedBallStep,
                accuracyMetropolisMarkedProposalProgram,
                MembershipOracleProgram.bind, MembershipOracleProgram.withQueryCap]
  | succ budget ih =>
      intro rawCap₁ rawCap₂ remainingProper samples total current hcap₁ hcap₂
      obtain ⟨rawCap₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₁ ≠ 0)
      obtain ⟨rawCap₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rawCap₂ ≠ 0)
      have hcap₁' : budget < rawCap₁ := by omega
      have hcap₂' : budget < rawCap₂ := by omega
      cases samples with
      | zero =>
          simp only [cappedAccuracyProperCollectWeightsAux]
      | succ samples =>
          cases remainingProper with
          | zero =>
              simp only [cappedAccuracyProperCollectWeightsAux,
                accuracyImportanceObservation, MembershipOracleProgram.bind,
                MembershipOracleProgram.withQueryCap]
              congr 1
              funext inside
              exact ih rawCap₁ rawCap₂ properStride samples
                (total + if inside = true ∧
                    ‖(accuracyScaleFactor q)⁻¹ • current‖ ≤
                      Real.sqrt (terminalVariance q) ∧
                    ‖(accuracyScaleFactor q)⁻¹ • current‖ ≤
                      accuracyPhaseRadius q sigma2 then
                    (Arlib.MarkovChains.gaussianScaleAcceptance sigma2
                      (accuracyScaleFactor q)
                      ((accuracyScaleFactor q)⁻¹ • current)).toReal *
                        weight ((accuracyScaleFactor q)⁻¹ • current)
                  else 0) current hcap₁' hcap₂'
          | succ remainingProper =>
              cases remainingProper with
              | zero =>
                  simp only [cappedAccuracyProperCollectWeightsAux,
                    accuracyMetropolisMarkedBallStep,
                    accuracyMetropolisMarkedProposalProgram,
                    MembershipOracleProgram.bind,
                    MembershipOracleProgram.withQueryCap]
                  congr 1
                  funext proposal
                  congr 1
                  funext inside
                  congr 1
                  funext coin
                  split_ifs <;> simp only [MembershipOracleProgram.bind]
                  all_goals apply ih <;> assumption
              | succ nextRemaining =>
                  simp only [cappedAccuracyProperCollectWeightsAux,
                    accuracyMetropolisMarkedBallStep,
                    accuracyMetropolisMarkedProposalProgram,
                    MembershipOracleProgram.bind,
                    MembershipOracleProgram.withQueryCap]
                  congr 1
                  funext proposal
                  congr 1
                  funext inside
                  congr 1
                  funext coin
                  split_ifs <;> simp only [MembershipOracleProgram.bind]
                  all_goals apply ih <;> assumption

/-- In particular, the concrete local cap `B + 1` is indistinguishable from
any still larger cap under the one outer budget `B`. -/
theorem cappedAccuracyProperCollectWeightsAux_globalPrefix
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ) (properStride budget extra : ℕ)
    (remainingProper samples : ℕ) (total : ℝ)
    (current : AmbientSpace q.n) :
    (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
      (budget + 1) remainingProper samples total current).withQueryCap budget =
    (cappedAccuracyProperCollectWeightsAux q sigma2 weight properStride
      (budget + 1 + extra) remainingProper samples total current).withQueryCap
        budget := by
  apply cappedAccuracyProperCollectWeightsAux_withQueryCap_eq_of_lt
  · omega
  · omega

end ArlibCommunity.Algorithms.CV18
