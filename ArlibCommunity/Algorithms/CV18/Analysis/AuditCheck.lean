/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAnalyticCore
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLazyProperProgram
import ArlibCommunity.Algorithms.CV18.Analysis.TheoremProof

/-!
# CV18 audit checks

The current public frontier is conditional on the single quantitative walk
input that remains to be formalized. These checks ensure the discharged
algorithmic and probability-theoretic chain itself uses only standard axioms.
-/

namespace ArlibCommunity.Algorithms.CV18

#print axioms figureOne_base_accuracy_of_analytic_inputs
#print axioms figureOneSharpAcceleratedMoments
#print axioms figureOneRadialTruncationBound
#print axioms Arlib.MarkovChains.gaussian_rejectedMass_le_direct
#print axioms Arlib.MarkovChains.half_mul_lintegral_gaussianWeight_le_ellGaussianMeasure_univ_direct
#print axioms Arlib.MarkovChains.half_mul_mul_measure_properProposalTotalCost_ge_le_LVStep
#print axioms Arlib.MarkovChains.map_state_eval_pathMeasure_lazyProperProposalGaussianLift
#print axioms Arlib.MarkovChains.map_lazyProperProposalCostedExecution_output
#print axioms Arlib.MarkovChains.half_mul_mul_measure_lazyProperProposalTotalCost_ge_le_LVStep
#print axioms map_state_eval_lazyProperProposalGaussianLift_figureOne
#print axioms truncatedMetropolisMarkedBallStep_map_snd
#print axioms runEstimate_truncatedMetropolisMarkedBallStep_eq_lazyProperAux
#print axioms cappedProperMetropolisBallWalk_queryBound
#print axioms half_mul_lintegral_gaussianWeight_le_figureOne
#print axioms figureOne_base_accuracy_of_mixing
#print axioms figureOne_base_query_cost
#print axioms volume_proof_amplification
#print axioms volumeTheorem_of_postInitialMixing

end ArlibCommunity.Algorithms.CV18
