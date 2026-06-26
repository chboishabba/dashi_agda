# NS triad K_N `L_FT^+` definition reconciliation

Date: 2026-06-24

## Question

Does the sampled Schur-test `L_FT^+` object coincide with the separate bare
positive shell-geometry proxy

`G_+(k,p) = max(cos(theta_kp),0) * |k x p| / |k|^2`

on the same finite/tail mode split?

## Compared objects

1. Exact script object:
   the sparse pair-incidence cross block assembled by
   `scripts/ns_triad_kn_acl_schur_test_proof.py` from
   `(sqrt(pi_i*pi_j*pi_l)/3) * max(cos(phi_i+phi_j-phi_l),0)`.
2. Bare proxy object:
   the direct shell-geometry proxy `G_+(k,p)` above.

Both are evaluated on the same `N=6,8,10,12` shell carriers, with the same
finite/tail split `K=N-1`, for:

1. the forced-tail profile used by the sampled Schur witness;
2. the equal-mass support profile on the worst tail extracted from the uniform
   geometry sweep.

## Result

The verdict is:

`different_object`

for every sampled row.

The decisive discrepancy is matrix-level, not cosmetic:

1. the exact script object has forced-tail column sums decaying with `N`;
2. the bare shell-geometry proxy has forced-tail column sums growing with `N`;
3. support overlap is sparse rather than near-identical;
4. the entrywise ratio on overlapping support is not close to a fixed bounded
   normalization.

Therefore the sampled Schur witness applies to the exact pair-incidence matrix
that the script reconstructs. It does not automatically promote to the separate
bare shell-geometry proxy.

## Artifact

- JSON:
  `scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_lft_definition_reconciliation_20260624/summary.json`
- Markdown:
  `scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_lft_definition_reconciliation_20260624/summary.md`

## Consequence

Until a theorem-level carrier is identified and matched to the sampled matrix,
the old `N^-0.91` sampled Schur decay must remain candidate-only runtime
evidence. It is not yet theorem evidence for the separate bare positive-sector
geometry.
