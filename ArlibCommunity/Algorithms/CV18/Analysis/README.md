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

The Gaussian Metropolis and speedy-Gaussian kernels have now also been ported.
`gaussianProperStepWithCost` specializes the same construction to CV18's
actual proper step: the proposal must land in the body, while a failed
Metropolis test remains a self-loop inside the returned speedy-Gaussian step.
The file proves that its state marginal is exactly
`speedyMetropolisGaussian`, that its expected raw-proposal cost is exactly
`1 / ell K delta x`, and the exact mixture identity expressing one ordinary
Gaussian Metropolis step as a proper speedy step or an improper self-loop.

The iterated bridge is now also formalized.  A totalized cost kernel handles
zero-local-conductance ambient states without the false assumption that
`ell > 0` everywhere, and agrees with the genuine geometric waiting law at
every non-stuck state.  `accumulatedCostStep_pow_snd` proves generically that,
after any `t` cost-accumulating steps, forgetting the cost gives exactly the
`t`-fold state-kernel iterate.  Its Gaussian specialization identifies the
state marginal with the `t`-fold `speedyMetropolisGaussian` kernel.

The raw-trajectory side is now formalized as well.  A Boolean-marked Gaussian
Metropolis chain exposes whether each actual proposal landed in the body;
forgetting the mark recovers the ordinary Gaussian Metropolis chain at every
deterministic time.  Stopping at the first `true` mark gives exactly one speedy
Gaussian step, and the first-proper waiting time has the exact geometric tail
and mean `1 / ell`.  Independent stopped trajectories are then restarted for
`t` proper steps.  Their output law is exactly the `t`-step speedy Gaussian
law, while their expected total proposal count is bounded by the explicit sum
of per-state exit-time integrals along the speedy marginals.

The warm-start and cutoff algebra is now proved for the correct proper-proposal
cost.  The `ell` factor in the speedy stationary density cancels `1 / ell`
exactly, and `mul_lintegral_properProposalTotalCost_le` bounds the honest
trajectory's expected total raw-proposal cost.  Markov's inequality then gives
`mul_mul_measure_properProposalTotalCost_ge_le`, the cutoff/restart failure
bound.  Both theorems depend only on the paper's weighted
average-local-conductance lower bound `lambda` and the phase warm-start bound;
no extra Metropolis-acceptance penalty is needed because a rejected
Metropolis test is still a proper proposal.

The next missing analytic results are therefore (1) the quantitative weighted
average-local-conductance lower bound for CV18's phase step size and body, and
(2) the speedy Gaussian mixing estimate.  These instantiate the now-proved
cost/cutoff theorem and combine its failure probability with the target
truncated-Gaussian sampling error.
