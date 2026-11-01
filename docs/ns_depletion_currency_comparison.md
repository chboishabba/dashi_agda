# Navier–Stokes replacement depletion-currency comparison

The first non-vacuous matched-cutoff experiment falsified

```text
max(-A_dot_self_advective, 0)
```

as the local depletion currency for the current smooth alignment budget.  The
positive-transfer triad had dangerous packet transfer but essentially no
negative self-packet alignment derivative.

This tranche compares four replacement currencies without promoting any of
them to the analytic depletion term required by the continuum theorem.

## Candidate currencies

All rates are dimensionless after division by the target-shell parabolic rate

```text
nu 2^(2K).
```

### 1. Gauge-invariant vorticity-direction turnover

For nonzero packet vorticity,

```text
xi_dot = (I - xi xi^T) omega_dot / |omega|.
```

The currency is the enstrophy-weighted RMS value of `|xi_dot|` divided by the
parabolic rate.  Parallel changes in vorticity magnitude contribute exactly
zero.  The quantity does not use an eigenvector sign convention.

### 2. Smooth spectral-projector turnover

For

```text
P_beta(S) = exp(beta S) / trace(exp(beta S)),
```

we compute the exact Galerkin tangent `P_dot` by spectral divided differences,
including repeated eigenvalues.  The currency is the enstrophy-weighted RMS
Frobenius speed of `P_dot`, divided by the parabolic rate.

This is an infinitesimal projector path-length rate.  It is deliberately not
reported as an endpoint geodesic distance.

### 3. Cross-shell coherence activity

The exact alignment derivative already splits into self-packet and cross-shell
pieces.  The candidate rate is

```text
abs(A_dot_cross-shell-advective + A_dot_cross-shell-pressure)
```

in parabolic time.  Its interval integral is reported as the cumulative
cross-shell coherence budget.

This is unsigned activity, not automatically dissipation.  A later theorem
would still have to prove that dangerous transfer spends this activity in the
correct one-sided way.

### 4. Positive middle-eigenvalue alignment on the simple-spectrum region

On points where both adjacent strain eigenvalue gaps exceed the declared
relative floor, the currency is

```text
max(lambda2, 0) alpha2 / (nu 2^(2K)),
alpha2 = (xi . e2)^2.
```

The weighted contribution is set to zero on unresolved eigenspace collisions.
That makes the reported quantity a fail-closed simple-spectrum lower candidate
rather than a regularized signed eigenvector quotient.  The audit separately
reports the enstrophy fraction covered by the simple-middle branch.

## Pointwise and integrated tests

For each currency, threshold `lambda`, and candidate cost `kappa`, the held-out
comparison evaluates

```text
currency_K(t) - kappa
```

only at checkpoints with `Gamma_K >= lambda`.  A pass requires dangerous
checkpoints in both the training and held-out trajectories.  A no-excursion run
cannot pass.

For every physical interval `[t_i,t_{i+1}]`, the audit also trapezoidally
integrates each currency and the existing positive remainder.  It reports

```text
theta_emp(currency)
  = integrated positive remainder / integrated currency.
```

Thresholded interval totals include only certainly dangerous intervals,

```text
min(Gamma_i, Gamma_{i+1}) >= lambda.
```

Unresolved crossings are recorded but not silently charged to either side.
Terminal snapshots receive no duration.

## Commands

The standalone comparison consumes an exact budget JSON:

```bash
python scripts/ns_depletion_currency_audit.py \
  --budget-json exact-budget.json \
  --required-cutoffs 32,48,64 \
  --holdout-trajectory matched-N64 \
  --output-json depletion-currencies.json \
  --pretty
```

The matched baseline now runs the comparison automatically:

```bash
python scripts/ns_run_matched_coherence_baseline.py \
  --cutoffs 32,48,64 \
  --workdir /tmp/ns-matched \
  --output-json /tmp/ns-matched-baseline.json
```

## Formal handoff

`DASHI/Physics/Closure/NSDepletionCurrencyFork.agda` proves that whichever
candidate is eventually supplied with both

```text
dangerCost * dangerousResidence <= selectedCurrency
```

and

```text
absorptionMargin * selectedCurrency <= budgetUpper,
```

it composes with the existing verified residence reduction.  The Agda module
does not assert that any empirical currency satisfies either inequality.

## Authority boundary

The comparison is finite-Galerkin and empirical.  A sampled positive margin is
not a theorem that dangerous transfer forces depletion.  Agreement across
N32/N48/N64 is not cutoff-uniform compactness, and none of the outputs carries
BKM, global-regularity, or Clay authority.
