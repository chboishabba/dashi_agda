# NS Triad K_N Sparse Schur Scaling Fit

- status: `ok`
- rows: `4`
- candidate only: `True`
- theorem promoted: `False`
- Clay promoted: `False`

| N | K | D | q_gap | N² q_gap | D q_gap | D/N² | R_tail | BKM tail proj² | cross L_neg frac |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 6 | 5 | 8.62228 | 0.000528544 | 0.0190276 | 0.00455725 | 0.239508 | 0.419575 | 4.85043e-05 | -0.0971208 |
| 8 | 7 | 15.1235 | 0.000270782 | 0.01733 | 0.00409517 | 0.236305 | 0.436214 | 5.9914e-05 | -0.093081 |
| 10 | 9 | 23.6241 | 0.000173949 | 0.0173949 | 0.0041094 | 0.236241 | 0.426831 | 1.93843e-05 | -0.0911436 |
| 12 | 11 | 34.1244 | 0.000113552 | 0.0163515 | 0.0038749 | 0.236975 | 0.436254 | 1.29391e-06 | -0.0932165 |

## Fits

- q_gap vs N: exponent `2.19763`, C `0.026843`, log-space R² `0.999012`
- D vs N: slope `1.9845`, C `0.245347`, log-space R² `0.999942`
- D*q_gap stats: `{'count': 4, 'min': 0.0038749044553088806, 'max': 0.004557249030978871, 'mean': 0.004159180219005459, 'sample_stdev': 0.00028626739824654294, 'relative_range': 0.16405746799621776}`
- N²*q_gap stats: `{'count': 4, 'min': 0.016351546347019436, 'max': 0.019027572331753617, 'mean': 0.017526020202730242, 'sample_stdev': 0.0011090003537135619, 'relative_range': 0.1526887424400723}`

## Interpretation

Candidate-only fitted telemetry for top-tail sparse Schur repair. The merged rows have min R_tail=0.4195752024137984, min q_gap=0.00011355240518763496, and mean D*q_gap=0.004159180219005459. The log-log fit is evidence for a scaling target, not a theorem; all promotion flags remain false.
