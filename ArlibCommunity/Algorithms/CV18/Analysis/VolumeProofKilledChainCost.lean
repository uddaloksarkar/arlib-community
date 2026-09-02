/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryWarmCost

/-! # Expected cost of a fixed-length killed transition chain -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Expected accumulated trial cost along at most `trials` transitions of a
possibly killed (subprobability) transition law. -/
noncomputable def finiteKilledChainExpectedCost
    {S : Type*} [MeasurableSpace S]
    (next : S → Measure S) (trialCost : S → ENNReal) : ℕ → S → ENNReal
  | 0, _ => 0
  | trials + 1, current => trialCost current +
      ∫⁻ nextState, finiteKilledChainExpectedCost next trialCost trials nextState
        ∂next current

theorem measurable_finiteKilledChainExpectedCost
    {S : Type*} [MeasurableSpace S]
    {next : S → Measure S} (hnext : Measurable next)
    {trialCost : S → ENNReal} (htrial : Measurable trialCost) :
    ∀ trials, Measurable (finiteKilledChainExpectedCost next trialCost trials) := by
  intro trials
  induction trials with
  | zero => exact measurable_const
  | succ trials ih =>
      simp only [finiteKilledChainExpectedCost]
      exact htrial.add ((Measure.measurable_lintegral ih).comp hnext)

/-- A fixed-length shadow execution costs linearly when every killed endpoint
law preserves the same warmness invariant.  This is the expectation argument
behind replacing the nested retry control flow by at most
`samples * retryLimit` live trials. -/
theorem lintegral_finiteKilledChainExpectedCost_le
    {S : Type*} [MeasurableSpace S]
    {next : S → Measure S} (hnext : Measurable next)
    {trialCost : S → ENNReal} (htrial : Measurable trialCost)
    {pi : Measure S} {M C : ENNReal}
    (hcost : ∀ mu : Measure S, _root_.Arlib.IsWarm M mu pi →
      ∫⁻ current, trialCost current ∂mu ≤ C)
    (hwarmNext : ∀ mu : Measure S, _root_.Arlib.IsWarm M mu pi →
      _root_.Arlib.IsWarm M (mu.bind next) pi) :
    ∀ (trials : ℕ) (mu : Measure S), _root_.Arlib.IsWarm M mu pi →
      ∫⁻ current, finiteKilledChainExpectedCost next trialCost trials current ∂mu ≤
        (trials : ENNReal) * C := by
  intro trials
  induction trials with
  | zero =>
      intro mu hwarm
      simp [finiteKilledChainExpectedCost]
  | succ trials ih =>
      intro mu hwarm
      have hmeas := measurable_finiteKilledChainExpectedCost hnext htrial trials
      calc
        (∫⁻ current,
            finiteKilledChainExpectedCost next trialCost (trials + 1) current
            ∂mu) =
            (∫⁻ current, trialCost current ∂mu) +
              ∫⁻ current,
                (∫⁻ nextState,
                  finiteKilledChainExpectedCost next trialCost trials nextState
                    ∂next current) ∂mu := by
              simp only [finiteKilledChainExpectedCost]
              rw [lintegral_add_left htrial]
        _ = (∫⁻ current, trialCost current ∂mu) +
              ∫⁻ nextState,
                finiteKilledChainExpectedCost next trialCost trials nextState
                  ∂(mu.bind next) := by
              congr 1
              rw [Measure.lintegral_bind hnext.aemeasurable hmeas.aemeasurable]
        _ ≤ C + (trials : ENNReal) * C :=
          add_le_add (hcost mu hwarm) (ih (mu.bind next) (hwarmNext mu hwarm))
        _ = (trials + 1 : ℕ) * C := by
          push_cast
          ring

end ArlibCommunity.Algorithms.CV18
