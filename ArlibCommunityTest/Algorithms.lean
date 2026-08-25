/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Using `ArlibCommunity.Algorithms`

TPA's analysis, consumed through its public imports and namespace.
-/
import ArlibCommunity.Algorithms

namespace ArlibCommunityTest.Algorithms

open ArlibCommunity.Algorithms.TPA

example (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ((MeasureTheory.Measure.pi (fun _ : Fin m => unifUnit))
        {u : Fin m → ℝ | c < ∏ i, u i}).toReal
      - ((MeasureTheory.Measure.pi (fun _ : Fin (m + 1) => unifUnit))
        {u : Fin (m + 1) → ℝ | c < ∏ i, u i}).toReal
      = Arlib.Probability.poissonPMF (-Real.log c) m :=
  prob_exactly_eq_poissonPMF m hc hc1

example {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun m => tpaTail m c) Filter.atTop (nhds 0) :=
  tendsto_tpaTail_atTop hc

example {A Ahat eps : ℝ} (heps : 0 < eps)
    (h : |Ahat - A| ≤ Real.log (1 + eps)) :
    (1 + eps)⁻¹ ≤ Real.exp Ahat / Real.exp A ∧
      Real.exp Ahat / Real.exp A ≤ 1 + eps :=
  relative_error_of_log_error heps h

end ArlibCommunityTest.Algorithms
