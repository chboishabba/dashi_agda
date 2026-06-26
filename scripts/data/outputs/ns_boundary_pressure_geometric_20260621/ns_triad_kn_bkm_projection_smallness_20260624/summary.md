# NS Triad K_N BKM Projection Smallness

- status: `ok`
- candidate only: `True`
- theorem promoted: `False`
- full NS promoted: `False`
- BKM exclusion proved: `False`
- Clay promoted: `False`

| N | K | bkm_tail_proj² | bkm_tail_proj² / q_gap | bkm_tail_proj² * N² | bkm_tail_proj * D | q_gap | q_gap * N² | R_tail | cross L_neg frac | eigen_tail_mass |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 6 | 5 | 4.85043e-05 | 0.0917697 | 0.00174615 | 0.000418217 | 0.000528544 | 0.0190276 | 0.419575 | -0.0971208 | 0.573094 |
| 8 | 7 | 5.9914e-05 | 0.221263 | 0.0038345 | 0.000906111 | 0.000270782 | 0.01733 | 0.436214 | -0.093081 | 0.698003 |
| 10 | 9 | 1.93843e-05 | 0.111436 | 0.00193843 | 0.000457936 | 0.000173949 | 0.0173949 | 0.426831 | -0.0911436 | 0.766512 |
| 12 | 11 | 1.29391e-06 | 0.0113948 | 0.000186323 | 4.41538e-05 | 0.000113552 | 0.0163515 | 0.436254 | -0.0932165 | 0.813582 |

## Readout

Candidate-only BKM-projection readout: the squared projection stays tiny across the sampled shells, with a sharp drop by N=12; it is not monotone from N=6 to N=8, but the sampled BKM-tail projection squared fraction fits roughly N^-4.871. The raw squared values span 1.29391e-06..5.9914e-05, bkm^2 / q_gap spans 0.0113948..0.221263, bkm^2 * N^2 spans 0.000186323..0.0038345, bkm*D spans 4.41538e-05..0.000906111, and q_gap * N^2 remains in the same O(10^-2) range for context (0.0163515..0.0190276).

## Fit

- bkm projection vs N fit: `{'fit_available': True, 'point_count': 4, 'x_key': 'N', 'y_key': 'bkm_tail_projection_squared_fraction', 'power_law_form': 'bkm_tail_projection_squared_fraction ~= C * N^slope', 'C': 0.6240534154581225, 'slope': -4.871321039125917, 'decay_exponent_if_y_decays': 4.871321039125917, 'log_intercept': -0.4715193125806163, 'r_squared_log_space': 0.6812155872146298, 'points': [{'x': 6.0, 'y': 4.850428100066944e-05}, {'x': 8.0, 'y': 5.991402692242359e-05}, {'x': 10.0, 'y': 1.9384276900414127e-05}, {'x': 12.0, 'y': 1.293908934758488e-06}]}`
- bkm^2 / q_gap stats: `{'count': 4, 'min': 0.011394817508448384, 'max': 0.22126333547968438, 'mean': 0.10896602530208882, 'sample_stdev': 0.08647281476199783, 'relative_range': 1.9259995708700308}`
- bkm^2 * N^2 stats: `{'count': 4, 'min': 0.00018632288660522226, 'max': 0.0038344977230351097, 'mean': 0.0019263506039264612, 'sample_stdev': 0.0014945833884921656, 'relative_range': 1.89382702660349}`
- bkm*D stats: `{'count': 4, 'min': 4.415382913091828e-05, 'max': 0.0009061114185758504, 'mean': 0.0004566045540087458, 'sample_stdev': 0.0003529151824956392, 'relative_range': 1.8877551305115152}`
