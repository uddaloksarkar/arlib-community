# CV18 analysis

This directory contains the currently discharged portion of Cousins and
Vempala's accelerated Gaussian-cooling volume algorithm [CV18].

The executable membership-oracle program, continuous semantics, cooling
schedule, query accounting, restricted-Gaussian stationarity, warm starts,
fixed-rate and terminal moment bounds, ideal-product calculation, initial
coupling, and median amplification are formalized.

The strongest public accuracy theorem is
`figureOne_base_accuracy_of_truncation_and_mixing`. It is conditional on
exactly two propositions:

- `FigureOneRadialTruncationBound` — preservation of ordinary volume after
  radial truncation;
- `FigureOnePostInitialMixingBound` — the dependent lazy ball-walk sampling
  error bound.

`FigureOneSharpAcceleratedMoments`, the phase-sensitive accelerated
localization estimate, is now proved unconditionally in
`VolumeProofSharpMoments.lean`. Its compact-convex localization dependency is
vendored under `ArlibCommunity/External/Kr25`; the adapter covers the exact
first-hit schedule, including the terminally clipped accelerated step.

The source snapshot in the original CV18 workspace asserted their conjunction
with a `sorry`. That declaration and the unconditional capstone are omitted
here so that arlib-community's no-`sorry` axiom invariant remains intact.

## Vempala optimization-book cross-check

The local optimization-book source is useful background but did not by itself
discharge the original three obligations. `annealing_volume.tex`, Lemma
`lem:chebychev_ratio`, proves the classical fixed-rate logconcave-power ratio
bound. The accelerated `O*(n^3)` CV theorem is then only stated and cited.
`ball_walk.tex` develops warm-start conductance-to-mixing and states Gaussian
restricted isoperimetry, but does not specialize the whole chain to CV18's
truncated Gaussian Metropolis program or its dependent product failure event.
No matching radial truncation-volume theorem with CV18's present radius was
found. The later dyadic proof has a larger logarithmic-radius constant and
therefore cannot discharge the current predicate without changing the
algorithm and its cost constants.

## Existing formal overlap in arlib-community

The HitAndRun background is closer to the missing mixing proof than the book
text alone. `SharpIsoperimetryConcave.lean` proves a Gaussian-restricted
isoperimetric inequality, while `BallWalk.lean`, `BallWalkConductance.lean`,
`Warmness.lean`, and `ConductanceToTV.lean` provide a kernel, reversibility,
lazy conductance, warm-start, and total-variation chain.

They do not yet prove `FigureOnePostInitialMixingBound`: the ball-walk modules
treat an unweighted uniform target, whereas CV18 executes a Gaussian-weighted
Metropolis step and needs the speedy/average-local-conductance analysis. The
existing conductance module also documents a weaker overlap estimate and only
an exponentially small unconditional local-conductance witness. These modules
are reusable infrastructure, not a drop-in discharge of the remaining
dependent-program obligation.
