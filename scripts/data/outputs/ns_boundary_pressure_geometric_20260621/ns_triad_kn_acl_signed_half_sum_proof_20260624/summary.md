# NS Triad K_N ACL Signed Half-Sum Proof

- status: `ok`
- shell: `10`
- candidate_only: `True`
- fail_closed: `True`
- started_at: `2026-06-24T11:39:14.780470+00:00`
- finished_at: `2026-06-24T11:39:15.619221+00:00`
- elapsed_ms: `838.77`

## Analysis

Fork decision: signed ACL cancellation is exact on the corrected first harmonic over the sampled same-shell transverse sets, but it does not control the positive block. Across representatives the transverse counts are 88..880, the imbalance ratios are 0..1.87e-15, and the positive-mass ratios are 0.500000..0.500000.  Therefore S_+ = S_abs/2 on this carrier, so Fork A is dead and the live route is direct positive-sector magnitude/counting control.

## Rows

| k | transverse count | closure signed/abs | ACL signed_sum | positive_sum | negative_sum | imbalance_ratio | positive_mass_ratio |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `(0, 10, 0)` | 880 | 1 | -2.42861286637e-15 | 94.9485717155 | 94.9485717155 | 1.87086209651e-15 | 0.5 |
| `(7, 7, 0)` | 430 | 1 | 4.45476988631e-15 | 24.6075253864 | 24.6075253864 | 1.4437508945e-16 | 0.5 |
| `(5, 8, 3)` | 88 | 1 | 4.28129753871e-15 | 9.30471802825 | 9.30471802825 | 0 | 0.5 |
| `(3, 9, 2)` | 92 | 1 | 5.96744875736e-16 | 9.95279405078 | 9.95279405078 | 2.67717310888e-16 | 0.5 |
