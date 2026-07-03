# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 6 | 1494 | 26 | 1468 | 1.452413e-05 | — | — | — | 1 | 1.31e-16 | 1.0000 | schur_psd |
| 8 | 2742 | 26 | 2716 | 6.117026e-06 | — | — | — | 1 | 1.16e-16 | 1.0000 | schur_psd |
| 10 | 4374 | 26 | 4348 | 3.334351e-06 | — | — | — | 1 | 2.79e-16 | -1.0000 | schur_psd |

N=6: , nullity_est=1, eval=dense
N=6: max |S_C 1_C|=1.307006e-16, L2 row-sum residual=2.681155e-16
N=6: Gate2A exact_identity=False, linearity_exact=False, abs_bounds=[1.407024e+00, 6.982732e+00], neg_bounds=[1.820854e+00, 4.110218e+01]
N=6: Gate2A transport directional=1.681546e-01, coarse_upper=1.776557e+01, improvement=1.056502e+02, margin_positive=True
N=6: matrix-free rho_sup=6.081569e-01, lambda1(L_good)=1.189330e-04, lambda_max(L_bad)=4.978366e-03, resid=3.68e-06
N=8: , nullity_est=1, eval=dense
N=8: max |S_C 1_C|=1.164433e-16, L2 row-sum residual=2.317873e-16
N=8: Gate2A exact_identity=False, linearity_exact=False, abs_bounds=[1.432510e+00, 7.025018e+00], neg_bounds=[1.826364e+00, 4.146769e+01]
N=8: Gate2A transport directional=1.677930e-01, coarse_upper=1.773990e+01, improvement=1.057249e+02, margin_positive=True
N=8: matrix-free rho_sup=6.128286e-01, lambda1(L_good)=2.064843e-04, lambda_max(L_bad)=5.052573e-03, resid=2.97e-06
N=10: , nullity_est=1, eval=dense
N=10: max |S_C 1_C|=2.786942e-16, L2 row-sum residual=5.267293e-16
N=10: Gate2A exact_identity=False, linearity_exact=False, abs_bounds=[1.434612e+00, 6.878846e+00], neg_bounds=[1.872191e+00, 4.779613e+01]
N=10: Gate2A transport directional=1.678154e-01, coarse_upper=2.049219e+01, improvement=1.221115e+02, margin_positive=True
N=10: matrix-free rho_sup=6.150777e-01, lambda1(L_good)=5.922660e-05, lambda_max(L_bad)=5.088695e-03, resid=9.06e-06

M_GC norms: 3.36e-03, 3.34e-03, 3.33e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.