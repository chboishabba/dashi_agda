# Exact Galerkin coherence-budget audit

This tranche repairs the chronology, gauge, degeneracy, derivative, and
cross-cutoff validation problems identified after the first N32 coherence run.

## Strict chronology and interval residence

`scripts/ns_shell_angle_residence_audit.py` delegates to a strict v2 audit.
Every checkpoint must have an explicit physical timestamp in either its export
receipt or NPZ state. Times must be unique and receipt order must be strictly
increasing unless `--allow-reorder` is explicitly supplied.

Only adjacent states define an interval. A terminal snapshot receives no
invented duration. For threshold `lambda`, an interval is classified as:

```text
certainly dangerous: min(Gamma_start, Gamma_end) >= lambda
certainly safe:      max(Gamma_start, Gamma_end) < lambda
unresolved crossing: otherwise
```

The audit reports lower and upper dangerous-residence bounds rather than
pretending a crossing interval has a known interior. A tight terminal checkpoint
above the smallest threshold fails closed by default and requests an additional
state. `--allow-terminal-danger` writes the request without treating the
terminal state as a residence interval.

New physical exports can carry time at source:

```bash
python scripts/ns_triad_gamma_gap_raw_hat_export_timed.py \
  --state state-0.npz --state state-1.npz --state state-2.npz \
  --times 0.0,0.01,0.02 \
  --trajectory-id run-N32 \
  --target-shell 2 \
  --aggregate-only \
  --output-json timed-transfer.json
```

Legacy exports can instead be migrated explicitly:

```bash
python scripts/ns_attach_explicit_timeline.py \
  --input-json legacy.json \
  --output-json timed.json \
  --times 0.0,0.01,0.02,0.03 \
  --trajectory-id run-N32
```

Crossing intervals and terminal excursions can be converted to a solver-facing
schedule without interpolating states:

```bash
python scripts/ns_adaptive_checkpoint_plan.py \
  --residence-json residence.json \
  --output-json checkpoint-plan.json \
  --depth 2 \
  --pretty
```

## Exact finite-Galerkin derivative

`scripts/ns_galerkin_coherence_core.py` reconstructs the dealiased,
divergence-free Galerkin state and splits the target-packet momentum RHS into:

```text
self advective
self pressure
cross-shell advective
cross-shell pressure
viscous
```

The component sum is checked against the direct packet-projected Leray RHS.

For a globally differentiable alignment budget it uses the smooth spectral
projector

```text
P_beta(S) = exp(beta S) / trace(exp(beta S)),
E_K = mean |omega_K|^2,
N_K = mean omega_K^T P_beta(S_K) omega_K,
A_K = N_K / E_K.
```

The Frechet derivative of `P_beta` is evaluated by spectral divided differences,
including the repeated-eigenvalue limit. The code computes exact tangent
derivatives of `E_K`, `N_K`, and `A_K` from every declared Galerkin RHS
component. It checks the component sum, quotient rule, and a central finite
difference of the complete derivative.

The hard top-eigenvector budget is retained separately. On the simple-spectrum
region its full component derivative uses

```text
2 (omega.e1) [omega_dot.e1
  + sum_{j != 1} (omega.ej)
    (ej^T Sdot e1)/(lambda1-lambdaj)].
```

Every eigenvector sign appears twice, so the scalar is invariant under
independent sign changes of `e1`, `e2`, and `e3`. No positive part of the
sign-dependent raw mixing coefficient is used. Near collisions the output
reports simple, top-pair-degenerate, and triple-degenerate regions; the smooth
spectral budget supplies the global derivative.

## Empirical absorption and coefficient fitting

`scripts/ns_packet_coherence_budget_audit.py` delegates to an exact v2 audit. It
reports

```text
local geometric depletion  = negative self-advective A-dot contribution
pressure remainder         = positive pressure A-dot contribution
commutator remainder       = positive cross-shell advective contribution
viscous remainder          = positive viscous A-dot contribution
theta_emp                  = integrated positive remainder / integrated depletion
```

These names are candidate analytic identifications, not theorem conclusions.
The audit also fits the smallest nonnegative coefficients dominating

```text
max(A_dot + kappa 1_{Gamma >= lambda}, 0)
```

on the sampled checkpoints. Terminal Gamma excursions are tested pointwise, so
the former start-of-interval loophole is removed.

## Projective direction coherence

`scripts/ns_log_bmo_vorticity_direction_audit.py` treats vorticity direction as
a line field. For each periodic cube it computes

```text
M_r = E_r[xi xi^T],
osc_projective = sqrt(1 - lambda_max(M_r)).
```

This is invariant under `xi -> -xi`. Vector and projective weighted median,
90th percentile, 99th percentile, and maximum statistics are emitted
separately. A single saturated maximum therefore no longer licenses a claim of
typical decorrelation.

## Scalable shell-pair transfer

The N32 atomwise census showed shell locality but scales poorly with cutoff.
`scripts/ns_shell_pair_transfer_audit.py` instead evaluates every ordered
bilinear shell pair

```text
P_K[(u_a . grad)u_b]
```

and takes absolute target-mode transfer only after aggregation within the shell
pair. It checks that the signed shell-pair sum reconstructs the full packet
transfer. Its gross quantity is deliberately labelled as shell-pair aggregate
gross and is not claimed equal to the earlier atomwise gross census.

## Matched N32/N48/N64 trajectories and held-out validation

The same analytic divergence-free initial flow can be integrated at all three
cutoffs with explicit times and denser output near Gamma excursions:

```bash
python scripts/ns_generate_matched_galerkin_trajectories.py \
  --cutoffs 32,48,64 \
  --output-dir /tmp/ns-matched-states \
  --manifest-json /tmp/ns-matched-manifest.json
```

The complete baseline—trajectory generation, shell-pair Gamma/tightness, exact
alignment derivatives, and one unchanged coefficient set held out on the
largest-cutoff trajectory—is:

```bash
python scripts/ns_run_matched_coherence_baseline.py \
  --cutoffs 32,48,64 \
  --workdir /tmp/ns-matched \
  --output-json /tmp/ns-matched-baseline.json
```

CI runs a short N32/N48/N64 baseline and requires both complete cutoff coverage
and at least one coefficient set to survive the held-out trajectory. This is an
empirical reproducibility gate, not a cutoff-uniform theorem.

For independently generated datasets, the standalone validator is:

```bash
python scripts/ns_multicutoff_coherence_validation.py \
  --input-json N32-budget.json \
  --input-json N48-budget.json \
  --input-json N64-budget.json \
  --holdout-trajectory heldout-flow \
  --required-cutoffs 32,48,64 \
  --output-json multicutoff-validation.json \
  --pretty
```

## Formal quotient-rule reduction

`DASHI/Physics/Closure/NSNormalizedAlignmentBudgetDerivative.agda` proves the
division-free quotient-rule identity. From

```text
N = A E
N' = A' E + A E'
```

it derives

```text
N' E = (A' E) E + N E'.
```

The remaining analytic leaves are the physical identification and bounds for
the local depletion, pressure, viscous, and commutator terms; strict integrated
absorption; dangerous-transfer expenditure; and cutoff-uniform compactness.
