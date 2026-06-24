# NS Triad K_N Diagonal Residue Bridge

- status: `partial`
- candidate only: `True`
- theorem promoted: `False`
- full NS promoted: `False`
- BKM exclusion proved: `False`
- Clay promoted: `False`

| N | K | TailDiagonalStable | SchurResidueScale | R_tail | cross L_neg frac | BKM tail proj² |
|---:|---:|---|---|---:|---:|---:|
| 6 | 5 | q_diag(N) >= c_diag > 0 | q_gap(N) >= c_gap / N^2 | 0.419575 | -0.0971208 | 4.85043e-05 |
| 8 | 7 | q_diag(N) >= c_diag > 0 | q_gap(N) >= c_gap / N^2 | 0.436214 | -0.093081 | 5.9914e-05 |
| 10 | 9 | q_diag(N) >= c_diag > 0 | q_gap(N) >= c_gap / N^2 | 0.426831 | -0.0911436 | 1.93843e-05 |

## Readout

Candidate-only diagonal-residue bridge: TailDiagonalStable says the tail block stays on the sampled 10^-2 scale, while SchurResidueScale says the positive gap is a small normalized residue with stable D*q_gap and q_gap ~ N^-2.2.

## Bridge rows

- TailDiagonalStable: q_diag and q_schur remain O(10^-2), with q_schur_subtraction/q_diag staying near 0.3%.
- SchurResidueScale: q_gap stays positive, q_gap/q_diag is small, and D*q_gap remains approximately stable.
