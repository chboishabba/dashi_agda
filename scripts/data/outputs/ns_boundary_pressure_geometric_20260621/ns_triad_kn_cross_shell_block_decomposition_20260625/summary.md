# NS Triad K_N(A) Cross-Shell Block Decomposition

- status: `ok`
- candidate only: `True`
- theorem promoted: `False`
- full NS promoted: `False`
- Clay promoted: `False`

## Rows

| N | block λ | Δ = λ_block − λ_global | leakage_shift | mass_l2 | B_cross | comp cert | block modes | comp modes | verdict |
|---:|---:|---:|---:|---:|---:|---|---:|---|
| 6 | 0.172016 | 0.00479531 | 0 | 0.9697 | 0 | empty_subspace | 1494 | 702 | leakage_small |
| 8 | 0.175021 | 0.0076191 | 0 | 0.9808 | 0 | empty_subspace | 2742 | 2170 | leakage_small |
| 10 | 0.174431 | 0.00762016 | 0 | 0.9668 | 0 | empty_subspace | 4374 | 4886 | leakage_small |
| 12 | 0.158031 | 2.21606e-05 | 0 | 0.9678 | 0 | lobpcg | 6390 | 9234 | leakage_small |

## Interpretation

Cross-shell block leakage audit: the global minimizer is carried by the 1-(N-1)-N seam, and the Rayleigh decomposition quantifies the leakage into the complement. Block lambda_min spans 0.158031..0.175021; delta_lambda = block_lambda - global_lambda spans 2.21606e-05..0.00762016; leakage_shift_vs_projection spans 0..0; block_mass_l2 spans 0.966755..0.980845; B_cross_fraction spans 0..0. Observed verdicts: ['leakage_small']. The leakage terms are the theorem-relevant quantity for Weyl/min-max closure.
