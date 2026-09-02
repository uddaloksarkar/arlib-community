/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledCostChain
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledAbortCost

/-! # Expected cost of the paper-faithful aborting scheduled executable -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Structural whole-program cost bound after interpreting the executable
cooling program by its chronological retained-state trace. -/
theorem figureOneFinalScheduledAbortBaseProgram_cost_le_retained
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    countedQueryCost
        ((figureOneFinalScheduledAbortBaseProgram q).run oracle.query) ≤
      1 + (figureOneFinalScheduledGaussianPhaseCostTail q I oracle 0
          (terminalPhaseSteps q) +
        figureOneFinalScheduledTerminalExpectedCost q I oracle) := by
  calc
    _ ≤ 1 + ∫⁻ point, countedQueryCost
          ((scheduledBalancedFigureOnePointContinuation
            figureOneFinalScheduledBalancedParameters q point).run oracle.query)
        ∂(truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q)) :=
      figureOneFinalScheduledAbortBaseProgram_countedQueryCost_le_initial_add
        q I oracle
    _ = _ := by
      rw [lintegral_scheduledBalancedFigureOnePointContinuation_cost_eq
        q I oracle]

#print axioms figureOneFinalScheduledAbortBaseProgram_cost_le_retained

end ArlibCommunity.Algorithms.CV18
