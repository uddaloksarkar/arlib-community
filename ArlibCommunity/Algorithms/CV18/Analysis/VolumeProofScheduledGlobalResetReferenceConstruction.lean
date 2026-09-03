/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGlobalResetReferenceWitnessConstructor
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalPreservation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledInitialAcceptedReference

/-!
# Finite invariant for the global chronological reset reference

This module fixes the induction invariant used by the final CV18 reference
construction.  It is stated directly with the chronological truncations and
the total coordinate extension consumed by `GlobalResetReferenceWitness`.
The empty initial accepted trace satisfies it, and a completed invariant at
the dependent phase count immediately yields the final witness.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

noncomputable section

/-- Moment and Lemma 7.17(c) facts accumulated through the first `phase`
chronological coordinates of a reset-reference trace. -/
structure ScheduledGlobalResetPrefixInvariant
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (reference : Measure (ScheduledBalancedCoolingTrace q.n)) : Prop where
  valid : ∀ᵐ trace ∂reference,
    ScheduledBalancedCoolingTraceValid phase trace
  coordinates_nonnegative : ∀ᵐ trace ∂reference,
    ScheduledBalancedCoolingTraceCoordinatesNonnegative phase trace
  coordinate_memLp : ∀ j, 1 ≤ j → j ≤ phase →
    MemLp (scheduledBalancedTracePhaseVariable q j) 2 reference
  coordinate_mean : ∀ j, 1 ≤ j → j ≤ phase →
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ∂reference) =
      figureOneChronologicalRawMean q I j
  coordinate_second : ∀ j, 1 ≤ j → j ≤ phase →
    (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂reference) ≤
      (figureOneChronologicalMomentFactor q j +
          figureOneExecutableMomentSlack q / 8) *
        figureOneChronologicalRawMean q I j ^ 2
  approxIndep : ∀ i, i < phase →
    ApproxIndepFun
      ((5 / 2 : ℝ) * figureOneDependentEpsilon q)
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I reference
          (figureOneScheduledReferenceCoordinateExtension q I))
        (figureOneChronologicalTruncatedPhase q I
          (figureOneScheduledReferenceCoordinateExtension q I)) i)
      (figureOneChronologicalTruncatedPhase q I
        (figureOneScheduledReferenceCoordinateExtension q I) (i + 1))
      reference

/-- During the Gaussian prefix, the retained endpoint is the accepted target
needed to start the next operational phase.  The `phase - 1` convention also
handles the empty prefix: both phase zero and the result of Gaussian phase
zero retain accepted target zero. -/
structure ScheduledGlobalGaussianPrefixInvariant
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (reference : Measure (ScheduledBalancedCoolingTrace q.n)) : Prop
    extends ScheduledGlobalResetPrefixInvariant q I phase reference where
  retained : reference.map scheduledBalancedTraceRetainedOption =
    (figureOneScheduledAcceptedTargetAt q I (phase - 1)).map some

/-- The accepted initial trace is the base case of the chronological
Gaussian recurrence. -/
theorem scheduledBalancedInitialAcceptedTraceReference_prefixInvariant
    (q : VolumeParams) (I : VolumeInput q.n) :
    ScheduledGlobalGaussianPrefixInvariant q I 0
      (scheduledBalancedInitialAcceptedTraceReference q I) := by
  refine
    { valid := scheduledBalancedInitialAcceptedTraceReference_ae_valid q I
      coordinates_nonnegative :=
        scheduledBalancedInitialAcceptedTraceReference_ae_coordinatesNonnegative
          q I
      coordinate_memLp := ?_
      coordinate_mean := ?_
      coordinate_second := ?_
      approxIndep := ?_
      retained := ?_ }
  · intro j hj1 hj0
    omega
  · intro j hj1 hj0
    omega
  · intro j hj1 hj0
    omega
  · intro i hi
    omega
  · simpa using
      map_scheduledBalancedInitialAcceptedTraceReference_retainedOption q I

/-- Structural induction step for the recurrence invariant.  Exact prefix
preservation carries every earlier moment and independence fact; the caller
only supplies the newly created coordinate facts and the new support. -/
theorem ScheduledGlobalResetPrefixInvariant.extend
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (source reference : Measure (ScheduledBalancedCoolingTrace q.n))
    (hsource : ScheduledGlobalResetPrefixInvariant q I phase source)
    (hprefix : reference.map (scheduledResetPrefixCoordinates q phase) =
      source.map (scheduledResetPrefixCoordinates q phase))
    (hnewMem : MemLp (scheduledBalancedTracePhaseVariable q (phase + 1))
      2 reference)
    (hnewMean : (∫ trace,
        scheduledBalancedTracePhaseVariable q (phase + 1) trace
          ∂reference) = figureOneChronologicalRawMean q I (phase + 1))
    (hnewSecond : (∫ trace,
        scheduledBalancedTracePhaseVariable q (phase + 1) trace ^ 2
          ∂reference) ≤
      (figureOneChronologicalMomentFactor q (phase + 1) +
          figureOneExecutableMomentSlack q / 8) *
        figureOneChronologicalRawMean q I (phase + 1) ^ 2)
    (hnewInd : ApproxIndepFun
      ((5 / 2 : ℝ) * figureOneDependentEpsilon q)
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I reference
          (figureOneScheduledReferenceCoordinateExtension q I))
        (figureOneChronologicalTruncatedPhase q I
          (figureOneScheduledReferenceCoordinateExtension q I)) phase)
      (figureOneChronologicalTruncatedPhase q I
        (figureOneScheduledReferenceCoordinateExtension q I) (phase + 1))
      reference)
    (hsupport : ∀ᵐ trace ∂reference,
      ScheduledBalancedCoolingTraceValid (phase + 1) trace ∧
        ScheduledBalancedCoolingTraceCoordinatesNonnegative
          (phase + 1) trace) :
    ScheduledGlobalResetPrefixInvariant q I (phase + 1) reference := by
  have holdMoments : ∀ j, 1 ≤ j → j ≤ phase →
      MemLp (scheduledBalancedTracePhaseVariable q j) 2 reference ∧
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace
          ∂reference) =
        ∫ trace, scheduledBalancedTracePhaseVariable q j trace ∂source ∧
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
          ∂reference) =
        ∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
          ∂source := by
    intro j hj1 hjphase
    let F := scheduledResetPrefixPhaseVariable phase j
    have hfactor : scheduledBalancedTracePhaseVariable q j =
        F ∘ scheduledResetPrefixCoordinates q phase := by
      funext trace
      exact (scheduledResetPrefixPhaseVariable_apply q phase j hj1 hjphase
        trace).symm
    have hlaw : reference.map (scheduledBalancedTracePhaseVariable q j) =
        source.map (scheduledBalancedTracePhaseVariable q j) := by
      rw [hfactor, ← Measure.map_map
        (measurable_scheduledResetPrefixPhaseVariable phase j)
        (measurable_scheduledResetPrefixCoordinates q phase), hprefix,
        Measure.map_map (measurable_scheduledResetPrefixPhaseVariable phase j)
          (measurable_scheduledResetPrefixCoordinates q phase)]
    exact coordinate_moments_of_map_eq source reference
      (scheduledBalancedTracePhaseVariable q j)
      (scheduledBalancedTracePhaseVariable q j)
      (measurable_scheduledBalancedTracePhaseVariable q j)
      (measurable_scheduledBalancedTracePhaseVariable q j) hlaw
      (hsource.coordinate_memLp j hj1 hjphase)
  refine
    { valid := by
        filter_upwards [hsupport] with trace htrace
        exact htrace.1
      coordinates_nonnegative := by
        filter_upwards [hsupport] with trace htrace
        exact htrace.2
      coordinate_memLp := ?_
      coordinate_mean := ?_
      coordinate_second := ?_
      approxIndep := ?_ }
  · intro j hj1 hjnext
    by_cases hj : j = phase + 1
    · simpa [hj] using hnewMem
    · exact (holdMoments j hj1 (by omega)).1
  · intro j hj1 hjnext
    by_cases hj : j = phase + 1
    · simpa [hj] using hnewMean
    · exact (holdMoments j hj1 (by omega)).2.1.trans
        (hsource.coordinate_mean j hj1 (by omega))
  · intro j hj1 hjnext
    by_cases hj : j = phase + 1
    · simpa [hj] using hnewSecond
    · rw [(holdMoments j hj1 (by omega)).2.2]
      exact hsource.coordinate_second j hj1 (by omega)
  · intro i hinext
    by_cases hi : i = phase
    · simpa [hi] using hnewInd
    · exact ApproxIndepFun.chronological_extension_of_resetPrefix_map_eq
        q I phase i hphase.le (by omega) source reference hprefix
          (hsource.approxIndep i (by omega))

/-- Once the finite recurrence has supplied all chronological coordinates,
the remaining global trace comparison is exactly the input expected by the
single final witness constructor. -/
noncomputable def GlobalResetReferenceWitness.of_completed_prefixInvariant
    (q : VolumeParams) (I : VolumeInput q.n)
    (reference : Measure (ScheduledBalancedCoolingTrace q.n))
    (hreference : IsProbabilityMeasure reference)
    (hinvariant : ScheduledGlobalResetPrefixInvariant q I
      (figureOneDependentPhaseCount q) reference)
    (htrace : MeasureLeUpTo
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q))
      reference (figureOneScheduledGlobalOuterStepError q)) :
    GlobalResetReferenceWitness q I := by
  exact GlobalResetReferenceWitness.of_finite_trace_reference
    q I reference hreference hinvariant.coordinate_memLp
      hinvariant.coordinate_mean hinvariant.coordinate_second
      (mul_nonneg (by norm_num) (figureOneDependentEpsilon_nonneg q))
      le_rfl hinvariant.approxIndep htrace

#print axioms
  scheduledBalancedInitialAcceptedTraceReference_prefixInvariant
#print axioms ScheduledGlobalResetPrefixInvariant.extend
#print axioms GlobalResetReferenceWitness.of_completed_prefixInvariant

end

end ArlibCommunity.Algorithms.CV18
