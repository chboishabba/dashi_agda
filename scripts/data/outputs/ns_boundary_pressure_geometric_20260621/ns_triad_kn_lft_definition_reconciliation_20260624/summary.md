# NS Triad K_N L_FT Definition Reconciliation

- status: `ok`
- overall verdict: `different_object`
- theorem promoted: `False`
- full NS promoted: `False`
- BKM exclusion proved: `False`
- Clay promoted: `False`

## Compared Objects

- script object: Exact script object: the sampled Schur-test matrix assembled from pair-incidence sums of (sqrt(pi_i*pi_j*pi_l)/3) * max(cos(phi_i+phi_j-phi_l),0).
- bare proxy object: Bare proxy object: shell-geometry positive kernel G_+(k,p) = max(cos(theta_kp),0) * |k x p| / |k|^2, evaluated on the same finite/tail mode split.

## Sampled Rows

| N | profile | verdict | script pairs | bare pairs | overlap | Jaccard | row script | row bare | col script | col bare | N*Schur script | N*Schur bare |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 6 | forced_tail | different_object | 22270 | 520820 | 10524 | 0.0197609 | 0.0114691 | 1964.8 | 0.000340859 | 312.582 | 0.0118633 | 4702.1 |
| 6 | adversarial_worst_tail_support | different_object | 22985 | 520820 | 11292 | 0.0212051 | 0.00209252 | 1964.8 | 0.0100378 | 312.582 | 0.0274983 | 4702.1 |
| 8 | forced_tail | different_object | 41144 | 2945960 | 19702 | 0.00663948 | 0.0114983 | 4919.13 | 0.000190048 | 878.574 | 0.011826 | 16631.2 |
| 8 | adversarial_worst_tail_support | different_object | 188271 | 2945960 | 93548 | 0.0307655 | 0.00111952 | 4919.13 | 0.00530145 | 878.574 | 0.0194896 | 16631.2 |
| 10 | forced_tail | different_object | 66103 | 10595404 | 31950 | 0.00300577 | 0.0116587 | 9940.87 | 0.000139883 | 1886.12 | 0.0127705 | 43300.9 |
| 10 | adversarial_worst_tail_support | different_object | 508820 | 10595404 | 253322 | 0.0233457 | 0.000676797 | 9940.87 | 0.00430472 | 1886.12 | 0.0170688 | 43300.9 |
| 12 | forced_tail | different_object | 96168 | 29305856 | 46751 | 0.00159259 | 0.0116101 | 17581.3 | 9.17093e-05 | 3461.44 | 0.0123824 | 93612.8 |
| 12 | adversarial_worst_tail_support | different_object | 1396265 | 29305856 | 696262 | 0.0232042 | 0.000444794 | 17581.3 | 0.00331887 | 3461.44 | 0.0145799 | 93612.8 |

## Fits

- forced-tail script column fit: `{'count': 4, 'log_log_slope': -1.8419624572467754, 'exp_intercept': 0.009152589084452612}`
- forced-tail bare column fit: `{'count': 4, 'log_log_slope': 3.4708250650094294, 'exp_intercept': 0.6316112535690094}`
- forced-tail script Schur fit: `{'count': 4, 'log_log_slope': -0.9098652969034354, 'exp_intercept': 0.010041020799012819}`
- forced-tail bare Schur fit: `{'count': 4, 'log_log_slope': 3.316509114229427, 'exp_intercept': 2.076287126942052}`

## Readout

Definition-reconciliation decision: different_object. Across the sampled shells, the exact Schur-test matrix and the bare shell-geometry proxy do not agree as the same object: forced-tail column sums span 9.17093e-05..0.000340859 for the script object versus 312.582..3461.44 for the bare proxy, while forced-tail N*Schur spans 0.011826..0.0127705 versus 4702.1..93612.8. On the adversarial-support rows the script column sums span 0.00331887..0.0100378 versus bare 312.582..3461.44. The sampled Schur witness therefore applies to the exact pair-incidence operator it reconstructs, not automatically to the separate bare shell-geometry proxy.
