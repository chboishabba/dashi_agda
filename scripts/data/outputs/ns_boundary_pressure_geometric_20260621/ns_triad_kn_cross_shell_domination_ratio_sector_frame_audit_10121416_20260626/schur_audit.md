# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 10 | 4374 | 26 | 4348 | 3.334351e-06 | -1.852327e-18 | 1.866017e-05 | 1.947443e-05 | 1 | 2.79e-16 | 1.0000 | schur_psd |
| 12 | 6390 | 26 | 6364 | 2.044918e-06 | 1.056257e-18 | 7.995154e-06 | 8.315004e-06 | 1 | 2.27e-16 | 1.0000 | schur_psd |
| 14 | 8790 | 26 | 8764 | 1.543480e-06 | -3.887133e-18 | 1.077726e-05 | 1.156614e-05 | 1 | 3.90e-16 | -1.0000 | schur_psd |
| 16 | 11574 | 26 | 11548 | 1.037211e-06 | -4.606734e-18 | 7.449612e-06 | 7.910530e-06 | 1 | 4.48e-16 | -1.0000 | schur_psd |

N=10: λ0=-1.852327e-18, λ1=1.866017e-05, λ2=1.947443e-05, nullity_est=1, eval=eigsh
N=10: max |S_C 1_C|=2.786942e-16, L2 row-sum residual=5.267293e-16
N=10: matrix-free rho_sup=6.150777e-01, lambda1(L_good)=5.922660e-05, lambda_max(L_bad)=5.088695e-03, resid=9.06e-06
N=12: λ0=1.056257e-18, λ1=7.995154e-06, λ2=8.315004e-06, nullity_est=1, eval=eigsh
N=12: max |S_C 1_C|=2.272488e-16, L2 row-sum residual=5.653588e-16
N=12: matrix-free rho_sup=6.589782e-01, lambda1(L_good)=3.779648e-05, lambda_max(L_bad)=5.074208e-03, resid=1.65e-05
N=14: λ0=-3.887133e-18, λ1=1.077726e-05, λ2=1.156614e-05, nullity_est=1, eval=eigsh
N=14: max |S_C 1_C|=3.899875e-16, L2 row-sum residual=6.991601e-16
N=14: matrix-free rho_sup=5.965422e-01, lambda1(L_good)=1.984516e-05, lambda_max(L_bad)=5.028554e-03, resid=1.05e-06
N=16: λ0=-4.606734e-18, λ1=7.449612e-06, λ2=7.910530e-06, nullity_est=1, eval=eigsh
N=16: max |S_C 1_C|=4.477755e-16, L2 row-sum residual=8.485909e-16
N=16: matrix-free rho_sup=5.811855e-01, lambda1(L_good)=1.967223e-05, lambda_max(L_bad)=5.053541e-03, resid=7.74e-07

M_GC norms: 3.33e-03, 3.33e-03, 3.33e-03, 3.33e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.