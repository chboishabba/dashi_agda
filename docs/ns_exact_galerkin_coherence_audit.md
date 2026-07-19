# Exact Galerkin coherence-budget audit

This tranche repairs the chronology, gauge, degeneracy, and derivative problems
identified after the first N32 coherence run.

## Strict chronology and interval residence

`scripts/ns_shell_angle_residence_audit.py` now delegates to a strict v2 audit.
Every checkpoint must have an explicit physical timestamp in either its export
receipt or NPZ state.  Times must be unique and receipt order must be strictly
increasing unless `--allow-reorder` is explicitly supplied.

Only adjacent states define an interval.  A terminal snapshot receives no
invented duration.  For threshold `lambda`, an interval is classified as:

```text
certainly dangerous: min(Gamma_start, Gamma_end) >= lambda
certainly safe:      max(Gamma_start, Gamma_end) < lambda
unresolved crossing: otherwise
```

A tight terminal checkpoint above the smallest threshold fails closed by
default and requests an additional state.  `--allow-terminal-danger` writes the
adaptive follow-up request without treating the terminal state as a residence
interval.

Legacy exports can be migrated with explicit times:

```bash
python scripts/ns_attach_explicit_timeline.py \
  --input-json legacy.json \
  --output-json timed.json \
  --times 0.0,0.01,0.02,0.03 \
  --trajectory-id run-N32
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

The sum is checked against the direct packet-projected Leray RHS.

For a globally differentiable alignment budget it uses the smooth spectral
projector

```text
P_beta(S) = exp(beta S) / trace(exp(beta S)),
E_K = mean |omega_K|^2,
N_K = mean omega_K^T P_beta(S_K) omega_K,
A_K = N_K / E_K.
```

The Frechet derivative of `P_beta` is evaluated by spectral divided differences,
including the repeated-eigenvalue limit.  The script computes exact tangent
derivatives of `E_K`, `N_K`, and `A_K` from each declared Galerkin RHS component,
and checks the component sum and quotient rule numerically.

The hard top-eigenvector budget is retained as a diagnostic.  Its pressure term
is reported only on the simple-spectrum region using the gauge-invariant scalar

```text
2 (omega.e1) sum_{j != 1} (omega.ej)
  (ej^T Sdot_pressure e1) / (lambda1-lambdaj).
```

No positive part of the gauge-dependent raw mixing coefficient is used.  Near
eigenvalue collisions, the output reports top-pair and triple-degenerate
fractions and uses the smooth projector budget for the global derivative.

## Empirical absorption and coefficient fitting

`scripts/ns_packet_coherence_budget_audit.py` now delegates to an exact v2
audit.  It reports

```text
local geometric depletion  = negative self-advective A-dot contribution
pressure remainder         = positive pressure A-dot contribution
commutator remainder       = positive cross-shell advective contribution
viscous remainder          = positive viscous A-dot contribution
theta_emp                  = integrated positive remainder / integrated depletion
```

The names are candidate identifications, not analytic theorems.  The output
also fits the smallest nonnegative coefficients dominating

```text
max(A_dot + kappa 1_{Gamma >= lambda}, 0)
```

on the sampled checkpoints.  Unlike the old start-of-interval audit, terminal
excursions are tested pointwise.

## Projective direction coherence

`scripts/ns_log_bmo_vorticity_direction_audit.py` now treats vorticity
direction as a line field.  For each periodic cube it computes

```text
M_r = E_r[xi xi^T],
osc_projective = sqrt(1 - lambda_max(M_r)).
```

This is invariant under `xi -> -xi`.  Vector and projective weighted median,
90th percentile, 99th percentile, and maximum statistics are emitted
separately, along with logarithmically weighted projective summaries.

## Matched-cutoff held-out validation

One coefficient set must survive independent trajectories and cutoffs:

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

The validator fits coefficients on training trajectories and applies them
unchanged to the held-out rows.  Missing N32/N48/N64 coverage is explicit and
never promoted to cutoff-uniform authority.

## Formal quotient-rule reduction

`DASHI/Physics/Closure/NSNormalizedAlignmentBudgetDerivative.agda` proves the
division-free quotient-rule identity.  From

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
