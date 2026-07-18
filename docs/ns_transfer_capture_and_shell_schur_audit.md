# NS transfer capture and coarse Schur audits

> **Status:** finite, empirical, fail-closed, non-promoting.

These tools implement the next executable diagnostics after the selected finite
Gamma carrier was shown to capture only a small fraction of gross packet
transfer.

They do not prove the profile-uniform Gamma gap, the concrete rectangular
pair-incidence Schur theorem, `C_err < 4`, BKM continuation, or Navier--Stokes
regularity.

## 1. Exact transfer-rank capture curve

`scripts/ns_triad_transfer_rank_capture_curve.py` enumerates the same
Leray-projected ordered Fourier interactions used by the physical `raw_hat`
exporter.  It keeps the exact largest requested prefix in a bounded NumPy
structured array.

For every checkpoint it reports:

- full signed and gross packet transfer;
- repeated-input and distinct-input accounting;
- exact top-rank gross-activity capture values;
- the first atom rank reaching 50%, 90%, or other requested fractions when that
  rank lies inside the retained prefix;
- otherwise a rigorous finite lower bound on the required atom rank;
- the number of reality-closed Fourier modes induced by each leading atom
  prefix.

Example:

```bash
python scripts/ns_triad_transfer_rank_capture_curve.py \
  --state /path/to/checkpoint0.npz \
  --state /path/to/checkpoint1.npz \
  --target-shell 2 \
  --rank-counts 1,8,64,512,4096,32768,262144 \
  --capture-targets 0.5,0.9 \
  --output-json /tmp/ns-transfer-capture.json
```

The retained prefix is exact: the script uses `argpartition` only to discard
values known to lie below the requested maximum rank.  A target marked
`reached_within_retained_prefix = true` therefore has an exact finite atom rank.
A target marked false gives only a lower bound.

The reality-closed mode count is the union of the `k`, `p`, and `q` modes of the
leading atoms, quotiented by simultaneous sign reversal and then doubled.  It is
a carrier-size diagnostic, not a closure theorem.

## 2. Coarse shell/angle weighted Schur audit

`scripts/ns_shell_angle_weighted_schur_audit.py` consumes the aggregate receipts
from:

```bash
python scripts/ns_triad_gamma_gap_raw_hat_export.py \
  --state /path/to/checkpoint.npz \
  --selection transfer \
  --aggregate-only \
  --target-shell 2 \
  --output-json /tmp/ns-shell-angle-aggregate.json
```

It forms the normalized nonnegative matrix

```text
K[p-shell, (q-shell, angle-bin)] = gross transfer mass fraction
```

and evaluates

```text
C_R = max_s sum_t K(s,t) w_T(t) / w_S(s)
C_C = max_t sum_s K(s,t) w_S(s) / w_T(t)
```

for shell weights

```text
w_S(p) = 2^(-alpha |p|)
w_T(q,angle) = 2^(-beta |q|).
```

Example:

```bash
python scripts/ns_shell_angle_weighted_schur_audit.py \
  --input-json /tmp/ns-shell-angle-aggregate.json \
  --output-json /tmp/ns-shell-angle-schur.json \
  --source-exponents 0,0.25,0.5,1,2 \
  --target-exponents 0,0.25,0.5,1,2 \
  --pretty
```

The output includes checkpointwise candidates and a minimax choice across all
checkpoints.

## Interpretation boundary

The shell/angle matrix is a projection of observed gross transfer mass.  It is
**not** the concrete Stage-3 rectangular pair-incidence kernel named in
`ns_plan.txt`.  In particular:

- it loses mode-level incidence information;
- it contains empirical state-dependent transfer weights;
- it does not establish equality with the formal operator;
- its Schur product does not determine `C_err`;
- a numerically small product is discovery evidence only.

The correct use is to identify candidate analytic shell weights and to falsify
weight choices before attempting the concrete Agda theorem.

## Current mathematical frontier

The first theorem still requiring new mathematics is

```text
sum_t K(s,t) w_T(t) <= C_R w_S(s)
sum_s K(s,t) w_S(s) <= C_C w_T(t)
```

for the repository's concrete rectangular incidence kernel, followed by an
operator handoff strong enough to prove `C_err < 4`.  These scripts narrow that
search; they do not close it.
