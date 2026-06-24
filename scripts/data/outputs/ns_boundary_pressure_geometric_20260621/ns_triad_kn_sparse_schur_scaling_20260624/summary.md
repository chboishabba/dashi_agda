# NS Triad K_N Sparse Schur Scaling

- status: `ok`
- eta: `0.25`
- tail offset: `1`
- rows: `3`
- failed rows: `0`

| N | K | D | R_full | R_tail | q_diag | q_coup | q_schur | q_gap | CG rel residual | BKM tail proj² |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 6 | 5 | 8.62228 | 0.167221 | 0.419575 | 0.0179025 | 0.0122024 | 0.0178526 | 0.000528544 | 7.45862e-09 | 4.85043e-05 |
| 8 | 7 | 15.1235 | 0.167402 | 0.436214 | 0.0158186 | 0.0119425 | 0.0157681 | 0.000270782 | 1.88317e-09 | 5.9914e-05 |
| 10 | 9 | 23.6241 | 0.166811 | 0.426831 | 0.0158872 | 0.0118317 | 0.0158385 | 0.000173949 | 1.54477e-09 | 1.93843e-05 |

## Interpretation

Candidate-only sparse Schur scaling scan. The primary top-tail rows have min R_tail=0.4195752024137984 and min q_gap=0.00017394943515542638. These values are telemetry for TailSubspaceCoercivity and SparseSchurTailRepair; they do not promote a theorem or Clay claim.
