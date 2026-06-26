# NS Triad Exact Pair-Incidence Operator Proof

- status: `ok`
- candidate only: `True`
- theorem promoted: `False`
- full NS promoted: `False`
- BKM exclusion proved: `False`
- Clay promoted: `False`

## Operator

- name: `exact_scripted_pair_incidence_operator`
- statement: The live NS triad Schur object is the exact scripted pair-incidence operator reconstructed from retained resonant triads on the finite-to-tail cross block.
- formula: For a finite mode k and tail mode p, L_FT,script^+(k,p) is the negative sum over retained resonant triads whose pair-incidence edge joins k to p of (sqrt(pi_i*pi_j*pi_l)/3) * max(cos(phi_i+phi_j-phi_l),0).
- live theorem target: `||L_FT,script^N||_op <= C / N`
- reconciliation verdict: `different_object`

## Proof Shape

1. Rebuild the exact finite-to-tail cross block from retained resonant triads.
2. Keep the exact pair-incidence weight formula explicit, including the profile amplitudes and the positive-sector truncation.
3. Match the reconstructed rows against the sampled Schur witness for the same object.
4. Carry forward the open uniform operator theorem target for the exact scripted object only.

## Forced-Tail Rows

| N | K | core modes | tail modes | row sup | column sup | Schur bound | N*bound | active cross pairs |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 6 | 5 | 728 | 1468 | 0.0114691 | 0.000340859 | 0.00197721 | 0.0118633 | 38868 |
| 8 | 7 | 2196 | 2716 | 0.0114983 | 0.000190048 | 0.00147825 | 0.011826 | 71208 |
| 10 | 9 | 4912 | 4348 | 0.0116587 | 0.000139883 | 0.00127705 | 0.0127705 | 114030 |
| 12 | 11 | 9260 | 6364 | 0.0116101 | 9.17093e-05 | 0.00103187 | 0.0123824 | 164598 |

## Adversarial-Support Rows

| N | K | row sup | column sup | Schur bound | N*bound | worst tail mode |
|---:|---:|---:|---:|---:|---:|---|
| 6 | 5 | 0.00411922 | 0.00177946 | 0.0027074 | 0.0162444 | [-1, 5, 0] |
| 8 | 7 | 0.00230246 | 0.00138254 | 0.00178417 | 0.0142733 | [-7, -2, 2] |
| 10 | 9 | 0.00144552 | 0.00110493 | 0.0012638 | 0.012638 | [-9, -1, -2] |
| 12 | 11 | 0.000971186 | 0.000916389 | 0.00094339 | 0.0113207 | [1, 2, -11] |

## Match Against Sampled Schur Script

- forced-tail rows: `{'row_count_match': True, 'all_rows_match_to_1e12': True, 'max_relative_difference': 0.0, 'field_checks': [{'N': 6, 'profile_id': 'forced_tail_K5_eta_0.250', 'row_sum_sup_rel_diff': 0.0, 'column_sum_sup_rel_diff': 0.0, 'schur_bound_rel_diff': 0.0, 'matches_to_1e12': True}, {'N': 8, 'profile_id': 'forced_tail_K7_eta_0.250', 'row_sum_sup_rel_diff': 0.0, 'column_sum_sup_rel_diff': 0.0, 'schur_bound_rel_diff': 0.0, 'matches_to_1e12': True}, {'N': 10, 'profile_id': 'forced_tail_K9_eta_0.250', 'row_sum_sup_rel_diff': 0.0, 'column_sum_sup_rel_diff': 0.0, 'schur_bound_rel_diff': 0.0, 'matches_to_1e12': True}, {'N': 12, 'profile_id': 'forced_tail_K11_eta_0.250', 'row_sum_sup_rel_diff': 0.0, 'column_sum_sup_rel_diff': 0.0, 'schur_bound_rel_diff': 0.0, 'matches_to_1e12': True}]}`
- adversarial rows: `{'row_count_match': True, 'all_rows_match_to_1e12': True, 'max_relative_difference': 0.0, 'field_checks': [{'N': 6, 'profile_id': 'uniform_all_modes_geometry_sweep', 'row_sum_sup_rel_diff': 0.0, 'column_sum_sup_rel_diff': 0.0, 'schur_bound_rel_diff': 0.0, 'matches_to_1e12': True}, {'N': 8, 'profile_id': 'uniform_all_modes_geometry_sweep', 'row_sum_sup_rel_diff': 0.0, 'column_sum_sup_rel_diff': 0.0, 'schur_bound_rel_diff': 0.0, 'matches_to_1e12': True}, {'N': 10, 'profile_id': 'uniform_all_modes_geometry_sweep', 'row_sum_sup_rel_diff': 0.0, 'column_sum_sup_rel_diff': 0.0, 'schur_bound_rel_diff': 0.0, 'matches_to_1e12': True}, {'N': 12, 'profile_id': 'uniform_all_modes_geometry_sweep', 'row_sum_sup_rel_diff': 0.0, 'column_sum_sup_rel_diff': 0.0, 'schur_bound_rel_diff': 0.0, 'matches_to_1e12': True}]}`

## Scaling

- forced row sup stats: `{'count': 4, 'min': 0.011469115826422354, 'max': 0.011658669695747196, 'mean': 0.011559044614785905, 'sample_stdev': 9.000944036304578e-05, 'relative_range': 0.01639874882759525}`
- forced column sup stats: `{'count': 4, 'min': 9.170933372028357e-05, 'max': 0.00034085935063711564, 'mean': 0.00019062510080165493, 'sample_stdev': 0.00010790386001819414, 'relative_range': 1.3070157910425038}`
- forced Schur bound stats: `{'count': 4, 'min': 0.0010318685100806618, 'max': 0.0019772089856603904, 'mean': 0.0014410951420692484, 'sample_stdev': 0.00040132144106372564, 'relative_range': 0.6559875527873388}`
- forced N*Schur bound stats: `{'count': 4, 'min': 0.011826038240410694, 'max': 0.012770482924846045, 'mean': 0.012210549300046756, 'sample_stdev': 0.0004514896716907435, 'relative_range': 0.07734661735747915}`
- adversarial column sup stats: `{'count': 4, 'min': 0.0009163894999913271, 'max': 0.001779464024250605, 'mean': 0.001295832409306775, 'sample_stdev': 0.0003749833289140694, 'relative_range': 0.6660386930135453}`
- adversarial Schur bound stats: `{'count': 4, 'min': 0.00094338975607883, 'max': 0.002707399505976815, 'mean': 0.0016746899483255874, 'sample_stdev': 0.0007707358347628201, 'relative_range': 1.0533351272942806}`
- forced log-log fit column sup vs N: `{'count': 4, 'log_log_slope': -1.8419624572467745, 'exp_intercept': 0.009152589084452597}`
- forced log-log fit Schur bound vs N: `{'count': 4, 'log_log_slope': -0.9098652969034343, 'exp_intercept': 0.010041020799012793}`
- adversarial log-log fit column sup vs N: `{'count': 4, 'log_log_slope': -0.9582838546919872, 'exp_intercept': 0.009999632396412429}`
- adversarial log-log fit Schur bound vs N: `{'count': 4, 'log_log_slope': -1.5197405334074154, 'exp_intercept': 0.04157251287346631}`

## Readout

Pair-incidence live-object readout: the canonical sampled rows are reconstructed directly from the exact scripted pair-incidence operator, and the forced-tail Schur witness matches the sampled Schur script with max relative difference 0.0. For the forced-tail family, N*||L_FT,script^N|| spans 0.011826..0.0127705 while the column supremum spans 9.17093e-05..0.000340859. For the adversarial-support rows, N*||L_FT,script^N|| spans 0.0113207..0.0162444. The reconciliation verdict remains different_object, so the bare shell-geometry proxy stays dead. What remains open is the uniform profile-independent proof of ||L_FT,script^N||_op <= C / N for the exact scripted operator itself.
