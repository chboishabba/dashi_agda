# NS canonical Gamma-gap adversarial audit

> **Status:** finite, empirical, fail-closed, non-promoting.

## Purpose

The current Agda lane proves the exact finite identity

\[
\Gamma_K
=
E_{K,+}\frac{A_K}{2\nu D_K}
=
\frac{\max(Q_K,0)}{2\nu D_K},
\]

and reduces a pointwise strict bound to the required interval estimate.  The
remaining theorem is to obtain one `eta > 0` uniformly over cutoffs and
normalized critical profiles.

`scripts/ns_triad_gamma_gap_adversarial_audit.py` is the next executable step.
It does not pretend to prove the missing estimate.  It tries to break proposed
versions of it and records which factor is responsible when a sampled profile
is subcritical:

- canonical cancellation through `E_{K,+}`;
- envelope-to-dissipation subcriticality through `A_K/(2 nu D_K)`;
- or a genuinely combined product margin.

## Exact finite computation

For a probability profile `p`, the audit uses amplitudes `a_i = sqrt(p_i)`.
Each input triad carries a signed coefficient `c_t` and contributes

\[
q_t(p)=c_t\,a_i a_j a_k.
\]

Triads are grouped before taking absolute values by the canonical orbit under:

1. all permutations of the three zero-sum wavevectors; and
2. simultaneous sign reversal.

For orbit blocks `B`, the script computes

\[
Q_K=\sum_B q_B,
\qquad
A_K=\sum_B |q_B|,
\qquad
E_{K,+}=\frac{\max(Q_K,0)}{A_K},
\]

with the zero-envelope convention `E_{K,+}=0`.  It then checks the machine
identity

\[
E_{K,+}\frac{A_K}{2\nu D_K}
=
\frac{\max(Q_K,0)}{2\nu D_K}
\]

for every sampled profile.

## Adversarial search

The candidate set contains:

- the uniform profile;
- equal-mass seeds on every individual triad;
- profiles supplied in the input JSON;
- Dirichlet samples over several concentration scales; and
- local mass-transfer improvements started from the worst feasible samples.

Optional concentration restrictions are explicit CLI inputs:

- `--max-neff`;
- `--max-radial-variance`;
- `--min-peak-mass`;
- `--max-dissipation`.

No default restriction is silently called “critical.”  The output distinguishes
`target-counterexample`, `cancellation-depleted`, `envelope-subcritical`, and
`combined-subcritical` rows.

For input trajectories, positive `duration` weights are used to scan contiguous
windows and compute

\[
\frac{1}{|I|}\sum_{t\in I}\Delta t\,\Gamma_K(t).
\]

## Explicit-transfer JSON mode

The preferred mode accepts coefficients that already represent the intended
signed finite transfer field, excluding only the amplitude product:

```bash
python scripts/ns_triad_gamma_gap_adversarial_audit.py \
  --input-json scripts/data/examples/ns_triad_gamma_gap_example.json \
  --output-json /tmp/ns-gamma-audit.json \
  --target-eta 0.05 \
  --random-samples 2000 \
  --local-steps 500 \
  --max-neff 16 \
  --max-radial-variance 1.0 \
  --pretty
```

The JSON contract is:

```json
{
  "problem_id": "...",
  "viscosity": 1.0,
  "convention": "left_plus_right_equals_out",
  "coefficient_semantics": "explicit_signed_transfer_coefficient",
  "modes": [
    {"wavevector": [1, 0, 0], "dissipation_weight": 1.0}
  ],
  "triads": [
    {"left": 0, "right": 1, "out": 2, "coefficient": 0.25}
  ],
  "profiles": [
    {
      "profile_id": "t0",
      "trajectory_id": "run-a",
      "time": 0.0,
      "duration": 0.01,
      "cutoff": 8,
      "probability": [0.2, 0.3, 0.5]
    }
  ]
}
```

If `dissipation_weight` is omitted, `|k|^2` is used.

A top-level `problems` list may be used when the signed coefficients or mode
carrier vary with time.  Give each time slice one input profile with a shared
`trajectory_id` and `cutoff`; the output aggregates those observed rows into
duration-weighted windows across problem boundaries.  Repeated equal profile
vectors at different times are deliberately preserved.

## Existing raw-frame surrogate mode

The script can also reuse the current N128 phase-coherence carrier:

```bash
python scripts/ns_triad_gamma_gap_adversarial_audit.py \
  --raw-archive /path/to/ns3d_archive.npz \
  --viscosity 0.001 \
  --shell 2 --shell 3 --shell 4 --shell 5 \
  --frame-limit 4 \
  --output-json /tmp/ns-gamma-coherence-scout.json \
  --random-samples 1000 \
  --pretty
```

This adapter freezes the observed phase-coherence coefficient

\[
\cos(\phi_i+\phi_j-\phi_k)
\]

and searches amplitudes around it.  It is useful for discovering and falsifying
candidate concentration alternatives, but it is not the physical Fourier
transfer coefficient and therefore cannot discharge the Agda theorem.

## Reading the output

The key fields are:

- `worst_profile.gamma`;
- `observed_pointwise_eta_margin = 1 - max(gamma)`;
- `worst_window.average_gamma`;
- top-level `worst_observed_window.average_gamma`;
- `target_counterexample_count`;
- `sampled_interval_counterexample_count`;
- `max_finite_identity_residual`;
- `no_counterexample_sampled`.

`no_counterexample_sampled = true` is evidence about the finite search only. It
is not a lower bound, a compactness theorem, a cutoff-uniform result, or a Clay
promotion.

## What this implementation can decide next

This audit gives a concrete way to choose the next analytic lemma rather than
adding more status records:

1. If concentrated counterexamples repeatedly have `E_{K,+}` near one but a
   small envelope ratio, pursue the envelope/coercivity route.
2. If the envelope ratio stays large but `E_{K,+}` is depleted, pursue canonical
   orbit cancellation/coherence.
3. If neither factor is separately small but the product is, formulate a
   coupled inequality rather than a false disjunction.
4. If sampled `Gamma_K` crosses one, the tested candidate profile class or
   coefficient model is falsified and must be narrowed or corrected before any
   formal proof effort.

The continuum, cutoff-uniform, profile-compactness and residence-time arguments
remain the mathematical frontier.
