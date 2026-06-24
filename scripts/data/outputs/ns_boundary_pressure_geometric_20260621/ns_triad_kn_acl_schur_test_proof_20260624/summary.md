# NS Triad K_N ACL Schur-Test Proof

- status: `ok`
- candidate only: `True`
- theorem promoted: `False`
- full NS promoted: `False`
- BKM exclusion proved: `False`
- Clay promoted: `False`

## Statement

`||L_FT^+||_op^2 <= (sup_k sum_p |L_FT^+(k,p)|) * (sup_p sum_k |L_FT^+(k,p)|)`

## Proof Shape

1. Reconstruct the exact positive-sector cross block `L_FT^+` for each sampled shell.
2. Use that every cross entry is nonpositive, so absolute row/column sums equal weighted cross-incidence sums.
3. Apply the matrix Schur test to the explicit finite matrix.
4. Record the resulting sampled `N^-1` operator-norm scale without theorem promotion.

## Rows

| N | K | core modes | tail modes | row sup | column sup | sqrt(row*col) | N*bound | N²*col | q_gap | D*q_gap |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 6 | 5 | 728 | 1468 | 0.0114691 | 0.000340859 | 0.00197721 | 0.0118633 | 0.0122709 | 0.000528544 | 0.00455725 |
| 8 | 7 | 2196 | 2716 | 0.0114983 | 0.000190048 | 0.00147825 | 0.011826 | 0.0121631 | 0.000270782 | 0.00409517 |
| 10 | 9 | 4912 | 4348 | 0.0116587 | 0.000139883 | 0.00127705 | 0.0127705 | 0.0139883 | 0.000173949 | 0.0041094 |
| 12 | 11 | 9260 | 6364 | 0.0116101 | 9.17093e-05 | 0.00103187 | 0.0123824 | 0.0132061 | 0.000113552 | 0.0038749 |

## Readout

Finite-shell Schur-test proof readout: the exact mixed-tail positive cross block has row/output absolute-sum supremum in 0.0114691..0.0116587, column/input absolute-sum supremum in 9.17093e-05..0.000340859, and therefore Schur bound ||L_FT^+||_op <= sqrt(row_sup * col_sup) in 0.00103187..0.00197721.  The sampled normalization is consistent with N * ||L_FT^+||_op staying in 0.011826..0.0127705 while N^2 * column_sum_sup stays in 0.0121631..0.0139883.  This proves the exact finite-shell inequality on the sampled rows only; uniform/profile-independent theorem promotion remains open.

## Scaling

- row sup stats: `{'count': 4, 'min': 0.011469115826422354, 'max': 0.011658669695747196, 'mean': 0.011559044614785905, 'sample_stdev': 9.000944036304578e-05, 'relative_range': 0.01639874882759525}`
- column sup stats: `{'count': 4, 'min': 9.170933372028357e-05, 'max': 0.00034085935063711564, 'mean': 0.00019062510080165493, 'sample_stdev': 0.00010790386001819414, 'relative_range': 1.3070157910425038}`
- Schur bound stats: `{'count': 4, 'min': 0.0010318685100806618, 'max': 0.0019772089856603904, 'mean': 0.0014410951420692484, 'sample_stdev': 0.00040132144106372564, 'relative_range': 0.6559875527873388}`
- N*Schur bound stats: `{'count': 4, 'min': 0.011826038240410694, 'max': 0.012770482924846045, 'mean': 0.012210549300046756, 'sample_stdev': 0.0004514896716907435, 'relative_range': 0.07734661735747915}`
- N²*column sup stats: `{'count': 4, 'min': 0.012163103468635831, 'max': 0.01398832271517856, 'mean': 0.012907126715617848, 'sample_stdev': 0.000859593815943388, 'relative_range': 0.14141173994473777}`
- log-log fit column sup vs N: `{'count': 4, 'log_log_slope': -1.8419624572467745, 'exp_intercept': 0.009152589084452597}`
- log-log fit Schur bound vs N: `{'count': 4, 'log_log_slope': -0.9098652969034343, 'exp_intercept': 0.010041020799012793}`
