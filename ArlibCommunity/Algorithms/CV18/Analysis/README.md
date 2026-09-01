# CV18 analysis

This directory contains the currently discharged portion of Cousins and
Vempala's accelerated Gaussian-cooling volume algorithm [CV18].

The executable membership-oracle program, continuous semantics, cooling
schedule, query accounting, restricted-Gaussian stationarity, warm starts,
fixed-rate and terminal moment bounds, ideal-product calculation, initial
coupling, and median amplification are formalized.

The strongest assembled result is `volumeTheorem_of_postInitialMixing`.  It
contains both the advertised accuracy conclusion and the explicit
membership-query bound, and is conditional on exactly one proposition:

- `FigureOnePostInitialMixingBound` — the dependent lazy ball-walk sampling
  error bound.

`FigureOneRadialTruncationBound` is now proved from `WellRounded` by
`figureOneRadialTruncationBound`.  Thus radial truncation is no longer an
assumption of the assembled theorem.

`FigureOneSharpAcceleratedMoments`, the phase-sensitive accelerated
localization estimate, is now proved unconditionally in
`VolumeProofSharpMoments.lean`. Its compact-convex localization dependency is
vendored under `ArlibCommunity/External/Kr25`; the adapter covers the exact
first-hit schedule, including the terminally clipped accelerated step.

The source snapshot in the original CV18 workspace asserted the former bundle
with a `sorry`.  The unconditional capstone remains omitted so that
arlib-community's no-`sorry` axiom invariant remains intact.

## Vempala optimization-book cross-check

The local optimization-book source is useful background but does not discharge
the remaining walk obligation. `annealing_volume.tex`, Lemma
`lem:chebychev_ratio`, proves the classical fixed-rate logconcave-power ratio
bound. The accelerated `O*(n^3)` CV theorem is then only stated and cited.
`ball_walk.tex` develops warm-start conductance-to-mixing and states Gaussian
restricted isoperimetry, but does not specialize the whole chain to CV18's
truncated Gaussian Metropolis program or its dependent product failure event.
The radial truncation proof now uses an explicit dyadic localization tail with
the correspondingly enlarged terminal-radius constant.

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

## Exact sampling mismatch to resolve

The paper's Figure 1 requests a fixed number of **proper** steps and, at phase
variance `sigma2`, targets `K ∩ 4 * sqrt(sigma2 * n) Bₙ`.  Its proof then
converts the expected number of raw ball-walk proposals into an executable
cutoff/restart procedure.  The current executable Lean program instead runs a
fixed number of raw proposals against the single terminal truncation
`truncatedBody q I`.

Consequently neither the optimization-book warm-start theorem nor the paper's
speedy-walk conductance theorem has the conclusion required by the current
kernel.  An unconditional proof must do one of the following, together with
the sequential TV composition already formalized here:

1. formalize phase truncation, proper-step execution, and the global
   cutoff/restart argument from CV18; or
2. prove a new exceptional-set/s-conductance theorem directly for the current
   fixed-terminal-truncation, fixed-raw-step kernel.

Importing a speedy-walk mixing theorem alone is insufficient: its stationary
law is proportional to local conductance times the Gaussian density, not the
target truncated Gaussian, and it does not identify a fixed raw-step law with
the required sample law.

## Proper-step bridge progress

`VolumeProofProperStep.lean` now supplies the first operational part of option
1.  The speedy-walk and holding-time developments have been ported into this
CV18 tree without imports from the stale workspace.  In addition, the new
`geometricCostKernel` constructs the joint law of the number of raw trials and
the next proper state.  The following are proved:

- the exact geometric cost/state rectangle probabilities;
- the returned-state marginal is exactly the requested next-state kernel;
- the expected trials-through-success cost is exactly the reciprocal of the
  success probability, hence exactly `1 / ell K delta x` for the ball walk;
- the costed kernel is Markov whenever the success probability is pointwise
  nonzero; and
- specializing the success probability to `ell K delta` makes the returned
  state exactly one `speedyWalk K delta` step.

This first specialization is the uniform ball-walk proposal component.  CV18's
actual returned-state kernel additionally applies the Gaussian Metropolis
filter after a proposal has landed in the body.  The generic cost kernel can be
reused unchanged once that Gaussian speedy kernel is ported.

The next missing results are therefore the Gaussian-Metropolis specialization
and the iterated bridge: accumulate these costs over `t` state-dependent proper
steps, identify the state marginal with the `t`-fold Gaussian speedy walk, and
identify that costed execution with the concrete raw proposal loop.  The
average-local-conductance expectation and cutoff/restart bounds can then be
applied to that accumulated cost.
