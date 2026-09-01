/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPrimitives
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStationary
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMarkovEmpirical

/-! # Exact law of the executable CV18 weight collector -/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- Front-recursive law of a Markov-chain weight collector.  Its coordinates
match the executable collector: accumulated weight first, last state second. -/
noncomputable def frontMarkovCollectLaw {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (f : S → ℝ) : ℕ → S → Measure (ℝ × S)
  | 0, current => Measure.dirac (0, current)
  | samples + 1, current =>
      (P current).bind fun next =>
        (frontMarkovCollectLaw P f samples next).map fun tail =>
          (f next + tail.1, tail.2)

/-- The front-recursive collector law is a measurable probability kernel in
its initial state. -/
theorem frontMarkovCollectLaw_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ} (hf : Measurable f) :
    ∀ samples,
      Measurable (frontMarkovCollectLaw P f samples) ∧
      ∀ current, IsProbabilityMeasure
        (frontMarkovCollectLaw P f samples current) := by
  intro samples
  induction samples with
  | zero =>
      constructor
      · exact Measure.measurable_dirac.comp
          (measurable_const.prodMk measurable_id)
      · intro current
        change IsProbabilityMeasure (Measure.dirac ((0 : ℝ), current))
        infer_instance
  | succ samples ih =>
      let tailLaw : S → Measure (ℝ × S) := fun next =>
        (frontMarkovCollectLaw P f samples next).map fun tail =>
          (f next + tail.1, tail.2)
      have htail : Measurable tailLaw := by
        apply measurable_measure_map_param_variable ih.1 ih.2
        exact ((hf.comp measurable_fst).add
          (measurable_fst.comp measurable_snd)).prodMk
            (measurable_snd.comp measurable_snd)
      have htailProb : ∀ next, IsProbabilityMeasure (tailLaw next) := by
        intro next
        dsimp [tailLaw]
        let _ : IsProbabilityMeasure
            (frontMarkovCollectLaw P f samples next) := ih.2 next
        exact Measure.isProbabilityMeasure_map (by fun_prop)
      constructor
      · change Measurable fun current => (P current).bind tailLaw
        exact measurable_measure_bind_param_variable P.measurable
          (fun current => IsMarkovKernel.isProbabilityMeasure current)
          (htail.comp measurable_snd)
      · intro current
        change IsProbabilityMeasure ((P current).bind tailLaw)
        exact MeasureTheory.isProbabilityMeasure_bind htail.aemeasurable <|
          ae_of_all _ htailProb

/-- The actual `collectWalkWeights` program has exactly the front-recursive
law for the block kernel consisting of `walkSteps` raw lazy steps. -/
theorem runEstimate_collectWalkWeights_eq_frontMarkovCollectLaw
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (weight : AmbientSpace q.n → ℝ)
    (hweight : Measurable weight) (walkSteps : ℕ) : ∀ samples current,
    (collectWalkWeights q sigma2 walkSteps weight samples current).runEstimate
        oracle.query =
      frontMarkovCollectLaw
        (truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps)
        weight samples current := by
  intro samples
  induction samples with
  | zero =>
      intro current
      rfl
  | succ samples ih =>
      intro current
      let P : Kernel (AmbientSpace q.n) (AmbientSpace q.n) :=
        truncatedMetropolisKernel q I oracle sigma2 ^ walkSteps
      let tailProgram : AmbientSpace q.n →
          MembershipOracleProgram q.n (ℝ × AmbientSpace q.n) := fun point =>
        (collectWalkWeights q sigma2 walkSteps weight samples point).bind fun tail =>
          .pure (weight point + tail.1, tail.2)
      have hcollect := collectWalkWeights_measurable_and_strong
        q I oracle sigma2 walkSteps weight hweight samples
      have htailOutput : ∀ point, Measurable fun tail : ℝ × AmbientSpace q.n =>
          (.pure (weight point + tail.1, tail.2) :
            MembershipOracleProgram q.n (ℝ × AmbientSpace q.n)).runEstimate
              oracle.query := by
        intro point
        simp only [MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp
          ((measurable_const.add measurable_fst).prodMk measurable_snd)
      have htailStrong : ∀ point,
          (tailProgram point).StronglyMeasurable oracle.query := by
        intro point
        exact (hcollect.2 point).bind (fun _ => by trivial) (htailOutput point)
      have htailRun : Measurable fun point =>
          (tailProgram point).runEstimate oracle.query := by
        have hsource : Measurable fun point =>
            (collectWalkWeights q sigma2 walkSteps weight samples point).runEstimate
              oracle.query := hcollect.1
        have hprob : ∀ point, IsProbabilityMeasure
            ((collectWalkWeights q sigma2 walkSteps weight samples point).runEstimate
              oracle.query) := fun point =>
          MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
            (hcollect.2 point).estimateMeasurable
        have htransform : Measurable fun p :
            AmbientSpace q.n × (ℝ × AmbientSpace q.n) =>
              (weight p.1 + p.2.1, p.2.2) :=
          ((hweight.comp measurable_fst).add
            (measurable_fst.comp measurable_snd)).prodMk
              (measurable_snd.comp measurable_snd)
        rw [show (fun point => (tailProgram point).runEstimate oracle.query) =
            fun point =>
              ((collectWalkWeights q sigma2 walkSteps weight samples point).runEstimate
                oracle.query).map fun tail =>
                  (weight point + tail.1, tail.2) by
          funext point
          unfold tailProgram
          rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
            (hcollect.2 point) (fun _ => by trivial) (htailOutput point)]
          simp only [MembershipOracleProgram.runEstimate]
          rw [Measure.bind_dirac_eq_map _ (by fun_prop)]]
        exact measurable_measure_map_param_variable hsource hprob htransform
      have hwalk := truncatedMetropolisBallWalk_measurable_and_strong
        q I oracle sigma2 walkSteps
      simp only [collectWalkWeights]
      rw [MembershipOracleProgram.runEstimate_bind oracle.query _ tailProgram
        (hwalk.2 current) htailStrong htailRun]
      rw [runEstimate_truncatedMetropolisBallWalk_eq_kernel_pow
        q I oracle sigma2 walkSteps current]
      simp_rw [show ∀ point, (tailProgram point).runEstimate oracle.query =
          (frontMarkovCollectLaw P weight samples point).map fun tail =>
            (weight point + tail.1, tail.2) by
        intro point
        unfold tailProgram
        rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
          (hcollect.2 point) (fun _ => by trivial) (htailOutput point), ih point]
        simp only [MembershipOracleProgram.runEstimate]
        rw [Measure.bind_dirac_eq_map _ (by fun_prop)]]
      rfl

end ArlibCommunity.Algorithms.CV18

#print axioms ArlibCommunity.Algorithms.CV18.runEstimate_collectWalkWeights_eq_frontMarkovCollectLaw
