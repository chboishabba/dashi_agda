# NS triad exact pair-incidence row/column audit

Date: 2026-06-25

## Status

The exact scripted pair-incidence operator now has an explicit row/column audit
for the checked normalization used by the live proof artifact.

For the forced-tail sampled family:

- `row_sum_sup` is approximately constant in `N`.
- `column_sum_sup` is approximately `N^-2`.
- `||L_FT,script^N||_op` therefore stays on the sampled `N^-1` Schur scale.

For the uniform-geometry adversarial family:

- `row_sum_sup` is approximately `N^-2`.
- `column_sum_sup` is approximately `N^-1`.

## What This Closes

It closes a normalization ambiguity in the discussion around Gate 1.

The checked exact-script artifact does not support the alternate claim that the
canonical exact-script column supremum is `O(1)`. In the current object,
`N^2 * column_sum_sup` is the stable forced-tail quantity.

## What It Does Not Close

This is still not a profile-independent theorem. The two sampled families scale
differently, so the live obstruction is not “missing telemetry”; it is the lack
of a profile-uniform row/column argument for the exact scripted operator.

Theorem authority, full-NS promotion, BKM exclusion, and Clay promotion remain
false.
