# NS Triad K_N Sparse Schur Scaling

- status: `ok`
- eta: `0.25`
- tail offset: `1`
- rows: `1`
- failed rows: `0`

| N | K | D | R_full | R_tail | q_diag | q_coup | q_schur | q_gap | CG rel residual | BKM tail proj² |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 12 | 11 | 34.1244 | 0.158009 | 0.436254 | 0.0144389 | 0.0116298 | 0.0143955 | 0.000113552 | 2.06826e-09 | 1.29391e-06 |

## Interpretation

Candidate-only sparse Schur scaling scan. The primary top-tail rows have min R_tail=0.4362537552367837 and min q_gap=0.00011355240518763496. These values are telemetry for TailSubspaceCoercivity and SparseSchurTailRepair; they do not promote a theorem or Clay claim.
