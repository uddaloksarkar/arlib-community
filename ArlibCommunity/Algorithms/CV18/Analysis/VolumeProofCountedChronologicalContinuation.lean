/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCountedMarginalCompletion
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExpectedQueryCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCollectSemantics

/-! # Marginal and cost laws for chronological counted continuations -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Forgetting the accumulated count after a counted continuation gives the
ordinary estimate kernel, independently of the incoming count. -/
theorem MembershipOracleProgram.countedContinuation_fst
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (next : A → MembershipOracleProgram n B)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle)
    (first : A × ℕ) :
    (countedContinuation oracle next first).fst =
      (next first.1).runEstimate oracle := by
  unfold Measure.fst countedContinuation
  rw [Measure.map_map measurable_fst (by fun_prop)]
  rw [(next first.1).runEstimate_eq_map_fst_run oracle
    (hnext first.1).executionMeasurable]
  congr 1

/-- The endpoint marginal of applying a counted continuation depends only on
the endpoint marginal of the incoming counted law. -/
theorem MembershipOracleProgram.fst_bind_countedContinuation
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (rho : Measure (A × ℕ))
    (next : A → MembershipOracleProgram n B)
    (hnextRun : Measurable fun result => (next result).run oracle)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle) :
    (rho.bind (countedContinuation oracle next)).fst =
      rho.fst.bind fun result => (next result).runEstimate oracle := by
  have hcont : Measurable (countedContinuation oracle next) :=
    measurable_countedContinuation oracle next hnextRun hnext
  have hestimate : Measurable fun result => (next result).runEstimate oracle := by
    rw [show (fun result => (next result).runEstimate oracle) =
        fun result => ((next result).run oracle).map Prod.fst by
      funext result
      exact (next result).runEstimate_eq_map_fst_run oracle
        (hnext result).executionMeasurable]
    exact (Measure.measurable_map _ measurable_fst).comp hnextRun
  unfold Measure.fst
  rw [map_bind_eq_bind_map_of_measurable rho hcont measurable_fst]
  rw [Measure.map_bind_eq_bind_comp rho measurable_fst hestimate]
  apply Measure.bind_congr_right
  filter_upwards with first
  exact MembershipOracleProgram.countedContinuation_fst oracle next hnext first

/-- Exact expected-count law for applying a counted continuation to an
arbitrary incoming joint law.  This is the measure-level counterpart of
`countedQueryCost_bind_eq_add`; it applies to the artificial reference laws
used by chronological completion. -/
theorem MembershipOracleProgram.countedQueryCost_bind_countedContinuation
    {n : ℕ} {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (oracle : AmbientSpace n → Bool)
    (rho : Measure (A × ℕ))
    (next : A → MembershipOracleProgram n B)
    (hnextRun : Measurable fun result => (next result).run oracle)
    (hnext : ∀ result, (next result).CountedStronglyMeasurable oracle) :
    countedQueryCost (rho.bind (countedContinuation oracle next)) =
      countedQueryCost rho +
        ∫⁻ result, countedQueryCost ((next result).run oracle) ∂rho.fst := by
  have hcont : Measurable (countedContinuation oracle next) :=
    measurable_countedContinuation oracle next hnextRun hnext
  have hphaseCost : Measurable fun result =>
      countedQueryCost ((next result).run oracle) :=
    (Measure.measurable_lintegral measurable_countedQueryCost_integrand).comp
      hnextRun
  unfold countedQueryCost
  rw [Measure.lintegral_bind hcont.aemeasurable
    measurable_countedQueryCost_integrand.aemeasurable]
  have hpoint : (∫⁻ first, ∫⁻ outcome, (outcome.2 : ENNReal)
        ∂countedContinuation oracle next first ∂rho) =
      ∫⁻ first, (first.2 : ENNReal) +
        countedQueryCost ((next first.1).run oracle) ∂rho := by
    apply lintegral_congr
    intro first
    exact lintegral_countedContinuation_queryCount oracle next hnext first
  rw [hpoint, lintegral_add_left measurable_countedQueryCost_integrand]
  congr 1
  unfold Measure.fst
  rw [lintegral_map]
  · rfl
  · exact hphaseCost
  · fun_prop

/-- A phase endpoint approximation and an ideal-marginal phase cost bound
give precisely the uniform reference-prefix premise required by
`exists_countedReference_iteratedKernelLaw`. -/
theorem MembershipOracleProgram.countedContinuation_step
    {n : ℕ} {A : Type} [MeasurableSpace A]
    (oracle : AmbientSpace n → Bool)
    (rho : Measure (A × ℕ)) (ideal nextIdeal : Measure A)
    (program : A → MembershipOracleProgram n A)
    (hprogramRun : Measurable fun result => (program result).run oracle)
    (hprogram : ∀ result, (program result).CountedStronglyMeasurable oracle)
    {delta phaseCost : ENNReal} (hmarginal : rho.fst = ideal)
    (hendpoint : MeasureLeUpTo
      (ideal.bind fun state => (program state).runEstimate oracle)
      nextIdeal delta)
    (hcost : (∫⁻ state, countedQueryCost ((program state).run oracle) ∂ideal) ≤
      phaseCost) :
    MeasureLeUpTo
        ((rho.bind (countedContinuation oracle program)).fst)
        nextIdeal delta ∧
      countedQueryCost (rho.bind (countedContinuation oracle program)) ≤
        countedQueryCost rho + phaseCost := by
  constructor
  · rw [MembershipOracleProgram.fst_bind_countedContinuation oracle rho
      program hprogramRun hprogram, hmarginal]
    exact hendpoint
  · rw [MembershipOracleProgram.countedQueryCost_bind_countedContinuation
      oracle rho program hprogramRun hprogram, hmarginal]
    gcongr

#print axioms MembershipOracleProgram.countedContinuation_fst
#print axioms MembershipOracleProgram.fst_bind_countedContinuation
#print axioms MembershipOracleProgram.countedQueryCost_bind_countedContinuation
#print axioms MembershipOracleProgram.countedContinuation_step

end ArlibCommunity.Algorithms.CV18
