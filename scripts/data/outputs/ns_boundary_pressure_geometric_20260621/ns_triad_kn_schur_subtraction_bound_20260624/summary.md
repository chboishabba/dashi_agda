# NS Triad K_N Schur Subtraction Bound

- status: `partial`
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

## Readout

Candidate-only Schur-subtraction bound readout: q_diag and q_schur remain on the 10^-2 scale (0.0158186..0.0179025, 0.0157681..0.0178526), q_sub/q_diag stays around 0.00278306..0.0031946 rather than approaching 1, q_gap remains positive and small (0.000173949..0.000528544), q_gap/q_diag stays around 0.010949..0.0295235, D*q_gap averages about 0.00425394, and N^2*q_gap averages about 0.0179175.

## Row stats

- q_gap/q_diag stats: `{'count': 3, 'min': 0.010948999433374506, 'max': 0.029523506088150755, 'mean': 0.0191968080672997, 'sample_stdev': 0.009460148528399886, 'relative_range': 0.9675830788982315}`
- q_schur_subtraction/q_diag stats: `{'count': 3, 'min': 0.0027830641220822246, 'max': 0.0031946030425162586, 'mean': 0.0030144379177138602, 'sample_stdev': 0.0002104942201916134, 'relative_range': 0.1365226060937237}`
- D*q_gap stats: `{'count': 3, 'min': 0.004095172011266396, 'max': 0.004557249030978871, 'mean': 0.004253938806904319, 'sample_stdev': 0.00026277061301590004, 'relative_range': 0.10862333491081361}`
- N²*q_gap stats: `{'count': 3, 'min': 0.01733001861660528, 'max': 0.019027572331753617, 'mean': 0.017917511487967178, 'sample_stdev': 0.0009618888284549319, 'relative_range': 0.09474271671534072}`
