# Clay Sprint 48 Replenishment Decomposition

Date: 2026-06-04

Sprint 48 keeps the Sprint 47 physical packet persistence result but splits
the remaining source term into its actual replenishment channels.

## Output Contract

The NS diagnostic harness adds:

```text
--replenishment-decomposition-audit
--replay-packet-summary <existing ns_packet_transition_summary.csv>
ns_replenishment_decomposition.csv
ns_replenishment_summary.json
```

`--replenishment-decomposition-audit` reuses the Sprint 47 coarse packet
summary rows. If `--packet-lineage-audit` is not explicitly set, the harness
still computes the packet summary because the decomposition depends on it.

For lightweight replay, use `--replay-packet-summary`. This skips truth loading,
FFT shell projection, strain computation, and packet generation. It consumes an
existing Sprint 47 `ns_packet_transition_summary.csv` and writes only the
Sprint 48 replenishment decomposition artifacts plus replay governance files.

The decomposition CSV emits:

```text
K
t
Rminus_K
Rzero_K
Rplus_K
M_plus_plus
M_plus_zero
M_plus_minus
source_from_plus
source_from_zero
source_from_minus
source_new_unmatched
source_total_eff
weighted_zero_source
weighted_minus_source
weighted_new_source
weighted_total_source
sigma_zero_fit
sigma_minus_fit
sigma_new_fit
sigma_total_fit
```

## Diagnostic Meaning

The recurrence remains:

```text
Rplus_(K+1) <= M_plus_plus(K) * Rplus_K + s_eff_K
```

where:

```text
s_eff_K =
  M_plus_zero(K)  * Rzero_K
  + M_plus_minus(K) * Rminus_K
  + source_new_unmatched_K
```

`source_from_plus = M_plus_plus * Rplus_K` is reported for accounting, but it
is the contracted old-red term, not replenishment credit.

For each snapshot, the harness fits observed-prefix slopes:

```text
source_i(K) ~ 2^(-sigma_i K)
```

The target is:

```text
sigma_zero > 1/2
sigma_minus > 1/2
sigma_new > 1/2
```

or directly:

```text
sum_K 2^(K/2) * s_eff_K < infinity
```

## Boundary

Sprint 48 is diagnostic only. It does not certify advected material parents,
true BT lanes, braid words, independent source decay, weighted source
summability, stretch absorption, no finite-time blowup, or Clay
Navier-Stokes regularity. All promotion flags remain false.
