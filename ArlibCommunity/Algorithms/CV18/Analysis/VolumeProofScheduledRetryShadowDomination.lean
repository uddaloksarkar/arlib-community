/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledChainCost

/-! # Domination of finite scheduled retries by a fixed-trial shadow -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Number of live trials still possible in the lexicographic retry state. -/
def balancedRemainingTrials (retryLimit attempts samples : ℕ) : ℕ :=
  match samples with
  | 0 => 0
  | future + 1 => future * retryLimit + attempts

@[simp] theorem balancedRemainingTrials_zero
    (retryLimit attempts : ℕ) :
    balancedRemainingTrials retryLimit attempts 0 = 0 := rfl

@[simp] theorem balancedRemainingTrials_succ
    (retryLimit attempts future : ℕ) :
    balancedRemainingTrials retryLimit attempts (future + 1) =
      future * retryLimit + attempts := rfl

theorem balancedRemainingTrials_accept
    (retryLimit attempts future : ℕ) :
    balancedRemainingTrials retryLimit retryLimit future ≤
      balancedRemainingTrials retryLimit (attempts + 1) (future + 1) - 1 := by
  cases future with
  | zero => simp [balancedRemainingTrials]
  | succ future =>
      simp only [balancedRemainingTrials, Nat.succ_mul]
      omega

theorem balancedRemainingTrials_reject
    (retryLimit attempts future : ℕ) :
    balancedRemainingTrials retryLimit attempts (future + 1) =
      balancedRemainingTrials retryLimit (attempts + 1) (future + 1) - 1 := by
  simp [balancedRemainingTrials]

/-- Monotonicity of the numerical fixed-chain shadow in its horizon. -/
theorem finiteKilledChainExpectedCost_mono
    {S : Type*} [MeasurableSpace S]
    (next : S → Measure S) (trialCost : S → ENNReal) :
    Monotone fun trials => finiteKilledChainExpectedCost next trialCost trials := by
  intro first second hle
  intro current
  induction second generalizing first current with
  | zero =>
      have : first = 0 := Nat.eq_zero_of_le_zero hle
      subst first
      exact le_rfl
  | succ second ih =>
      cases first with
      | zero => exact bot_le
      | succ first =>
          simp only [finiteKilledChainExpectedCost]
          exact add_le_add le_rfl (lintegral_mono fun state =>
            ih (Nat.le_of_succ_le_succ hle) state)

end ArlibCommunity.Algorithms.CV18
