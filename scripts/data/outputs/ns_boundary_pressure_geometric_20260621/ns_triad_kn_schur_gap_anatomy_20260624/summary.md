# NS Triad K_N Schur Gap Anatomy

- status: `ok`
- candidate only: `True`
- theorem promoted: `False`
- full NS promoted: `False`
- BKM exclusion proved: `False`
- Clay promoted: `False`

| N | K | q_diag | q_schur | q_schur_subtraction | q_gap | q_gap/q_diag | q_schur_subtraction/q_diag | D | D*q_gap | N²*q_gap | R_tail | cross L_neg frac | BKM tail proj² |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 6 | 5 | 0.0179025 | 0.0178526 | 4.98237e-05 | 0.000528544 | 0.0295235 | 0.00278306 | 8.62228 | 0.00455725 | 0.0190276 | 0.419575 | -0.0971208 | 4.85043e-05 |
| 8 | 7 | 0.0158186 | 0.0157681 | 5.05342e-05 | 0.000270782 | 0.0171179 | 0.0031946 | 15.1235 | 0.00409517 | 0.01733 | 0.436214 | -0.093081 | 5.9914e-05 |
| 10 | 9 | 0.0158872 | 0.0158385 | 4.87047e-05 | 0.000173949 | 0.010949 | 0.00306565 | 23.6241 | 0.0041094 | 0.0173949 | 0.426831 | -0.0911436 | 1.93843e-05 |
| 12 | 11 | 0.0144389 | 0.0143955 | 4.33853e-05 | 0.000113552 | 0.00786434 | 0.00300475 | 34.1244 | 0.0038749 | 0.0163515 | 0.436254 | -0.0932165 | 1.29391e-06 |

## Readout

Candidate-only finite-shell anatomy: q_diag and q_schur stay on the 10^-2 scale (0.0144389..0.0179025, 0.0143955..0.0178526 when available), q_gap stays much smaller (0.000113552..0.000528544) and tracks N^-2.2 in the parent fit, q_gap/q_diag stays around 0.00786434..0.0295235, q_schur_subtraction/q_diag stays around 0.00278306..0.0031946, D*q_gap averages about 0.00415918, and the subtraction remains a small residue rather than a catastrophic cancellation.

## Row stats

- q_gap/q_diag stats: `{'count': 4, 'min': 0.007864335313233937, 'max': 0.029523506088150755, 'mean': 0.01636368987878326, 'sample_stdev': 0.009579622894456845, 'relative_range': 1.323611663100481}`
- q_schur_subtraction/q_diag stats: `{'count': 4, 'min': 0.0027830641220822246, 'max': 0.0031946030425162586, 'mean': 0.003012016422394396, 'sample_stdev': 0.0001719360318482207, 'relative_range': 0.13663236275016125}`
- D*q_gap stats: `{'count': 4, 'min': 0.0038749044553088806, 'max': 0.004557249030978871, 'mean': 0.004159180219005459, 'sample_stdev': 0.00028626739824654294, 'relative_range': 0.16405746799621776}`
- N²*q_gap stats: `{'count': 4, 'min': 0.016351546347019436, 'max': 0.019027572331753617, 'mean': 0.017526020202730242, 'sample_stdev': 0.0011090003537135619, 'relative_range': 0.1526887424400723}`
