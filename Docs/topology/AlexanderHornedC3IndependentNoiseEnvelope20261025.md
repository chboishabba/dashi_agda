# Alexander horned C3 — analytic finite-gate noise envelope (2026-10-25)

Scope: an independently derived expectation for the noise distribution actually used in
`scripts/alexander_horned_c3_finite_SU2_gauge_simulator.py`.
This is a **new analytic audit**, not a measurement, proof of a physical wild
embedding, or a theorem about arbitrary correlated hardware noise.

## Assumptions and proof

The simulator inserts at each elementary SU(2) gate an independent unit
quaternion perturbation
`N_j = cos(theta_j/2) + a_j sin(theta_j/2)`, with uniformly isotropic
unit axis `a_j`, independent Gaussian angle `theta_j ~ N(0,sigma²)`,
and a deterministic ideal gate `G_j`. The isotropic axis has zero mean,
and the Gaussian characteristic function gives
`E[N_j] = exp(-sigma²/8) I`.
Matrix independence, including the interspersed deterministic gates,
therefore gives
`E[N_1 G_1 ... N_L G_L] = exp(-L sigma²/8) G_1...G_L`.
The chosen root-cube ideal product is `-I`; at binary depth `n`
its fully expanded word has `L=3*4^n` gates. Consequently:

```text
E[normalized Wilson halftrace at depth n]
  = -exp(-3*4^n*sigma_rad²/8).
maximum sigma_degrees for abs(mean) >= tau
  = (180/pi) * sqrt(-8*log(tau)/(3*4^n)), 0 < tau <= 1.
```

The expectation of the Bernoulli interferometric readout has the same
value, provided the readout is unbiased conditional on its true trace.
Finite shots add sampling variance; this expression alone does not
specify a confidence interval for an individual experimental run.
The 0.9-signal maximum allowable sigma halves with each additional
binary refinement. Every predicted signal is strictly negative at finite
depth and finite sigma under the model; approaching zero is attenuation,
not topological trivialization.

## Reproducible local check and prediction

`python scripts/alexander_horned_c3_independent_noise_envelope.py --audit`
checks the formula against a distinct Monte Carlo quaternion composition
and tests the exact threshold inversion. Independent locally executed
equivalent script PASS with six thousand trials at each of depths 0–3,
plus inversion tests. It does not run Agda or CI.

At sigma=1.5 degrees:

| depth | elementary gates | exact model mean |
|---:|---:|---:|
| 0 | 3 | -0.999743 |
| 1 | 12 | -0.998972 |
| 2 | 48 | -0.995896 |
| 3 | 192 | -0.983685 |
| 4 | 768 | -0.936321 |
| 5 | 3072 | -0.768596 |

Compare to the previously reported simulated depth-5 shot estimate
approximately -0.803. Such a stochastic finite-sample discrepancy is
not automatically a bug; use repeated independent seed runs and their
uncertainty before making a statistical judgement.

## Experimental acceptance and falsification

* At each depth benchmark the **sample mean** against the analytic
  prediction over independent trials, with proper shot-and-run uncertainty.
* Vary the injected angular RMS error and test the log-linear law
  `log(abs(mean)) = -L*sigma_rad²/8`.
* Repeat with deliberately correlated errors. If observed attenuation
  differs, do not describe the independent noise model as a fit.
* Compare the scrambled-relation control, commuting control, Q8
  one-step control, and compatible 2I recursion.
* Track physical compiler and calibration errors independently: none
  of these statistical predictions by itself demonstrates a flat
  SU(2) connection on a wild 3D exterior.

## Critical-path impact

The gate depth of the naive expanded-word protocol grows exponentially,
so the main physical bottleneck is now concrete: gate compression or
error mitigation **with a separate equivalence certificate**, rather
than adding new algebraic carriers. Geometric same-object infinite maps
and relative collar maps are independently outstanding for full kernel
formalization. Classical proof inputs remain attributed to
Alexander (1924), Hatcher (*Algebraic Topology*, Ex. 2B.2), Lippert
(*Alexander Horned Sphere and Bing's Hooked Rug*); no original
wild-sphere discovery is claimed.
