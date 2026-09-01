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

`VolumeProofAverageConductance.lean` now proves an unconditional version of
the weighted average-local-conductance estimate at the smaller step size
`delta ≤ 1/(2n)`.  The proof uses the homothetic core
`(1 - 1/(2n)) • K`: convexity and the unit-ball inclusion make every proposal
from the core proper, while Gaussian scaling and Bernoulli's inequality show
that the core retains at least half the Gaussian mass.  Consequently Lean now
proves `lambda = 1/2`, discharges both normalization guards for a finite-volume
body, and derives concrete expected-cost and cutoff theorems for the restarted
proper-proposal execution.

The speedy-Gaussian conductance and mixing chain is now also ported and proved
without a stale-directory import.  In particular,
`conductance_speedyMetropolisGaussian_ge_uncond` gives the paper-shaped
conductance lower bound
`delta * log 2 / (640 * sigma * sqrt n)`, and
`mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` converts it to the
explicit warm-start mixing count for the lazy speedy Metropolis-Gaussian walk.
The axiom audits of these capstones contain only Lean's standard `propext`,
choice, and quotient axioms.

These results still do not prove CV18 Theorem 1.1 with its advertised
`O*(n^3)` complexity.  Figure 1 uses the phase step
`min{sigma,1}/(4096 * sqrt(n * log(n/epsilon)))`.  The paper's smoothing lemma
is intended to prove average local conductance at this scale.  The elementary
homothetic-core proof above applies only when that step also satisfies
`delta ≤ 1/(2n)`; using `1/(2n)` as a uniform replacement loses the required
asymptotic mixing exponent.  The remaining work is now:

1. prove the weighted average-local-conductance/smoothing estimate, hence the
   raw-proposal cutoff, at that larger phase-dependent step;
2. align the proved lazy speedy-chain law with the formal proper-step execution
   and transfer its stationary law proportional to `ell * gaussianWeight` to
   the phase's restricted-Gaussian target; and
3. instantiate those facts phase by phase and compose them into
   `FigureOnePostInitialMixingBound` for the executable dependent program.
