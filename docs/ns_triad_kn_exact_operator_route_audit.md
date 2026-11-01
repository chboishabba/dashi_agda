# NS triad exact-operator route audit

Date: 2026-06-25

## Status

The route has now been resumed through the four requested gates and written
back as one fail-closed audit:

1. Exact-script row/column theorem: open.
2. `SchurResidueScale` transfer to `q_gap(N) >= c_gap / N^2`: open.
3. Structural BKM projection smallness: open.
4. Residence-time exclusion: open.

## Why Gate 1 Is Still Open

The checked exact-script families are asymmetric rather than profile-uniform.

- Forced-tail rows behave like `row_sum_sup ~ N^0` and `column_sum_sup ~ N^-2`.
- Uniform-geometry adversarial rows behave like `row_sum_sup ~ N^-2` and
  `column_sum_sup ~ N^-1`.

That preserves the sampled `N^-1` Schur scale, but it does not close a
profile-independent theorem.

## Downstream State

The diagonal-residue bridge remains candidate-only even though `N^2 * q_gap`
stays in a stable sampled range. The BKM projection remains telemetry-only. The
Sprint 99 residence receipt still records missing analytic objects and false
closure flags.

This leaves the lane in the strongest available pre-theorem state, not a
promoted theorem state.
