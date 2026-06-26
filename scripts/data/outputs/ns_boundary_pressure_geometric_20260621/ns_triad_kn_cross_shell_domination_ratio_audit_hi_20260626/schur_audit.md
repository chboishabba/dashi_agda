# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 12 | 6390 | 26 | 6364 | 2.698284e-06 | 5.002482e-18 | 7.795517e-06 | 7.939439e-06 | 1 | 2.26e-16 | 1.0000 | schur_psd |
| 14 | 8790 | 26 | 8764 | 2.022647e-06 | 4.317901e-18 | 9.821030e-06 | 9.919407e-06 | 1 | 4.39e-16 | 1.0000 | schur_psd |

N=12: λ0=5.002482e-18, λ1=7.795517e-06, λ2=7.939439e-06, nullity_est=1, eval=eigsh
N=12: max |S_C 1_C|=2.255141e-16, L2 row-sum residual=5.124478e-16
N=12: matrix-free rho_sup=6.577474e-01, lambda1(L_good)=2.093080e-05, lambda_max(L_bad)=4.995804e-03, resid=8.84e-06
N=14: λ0=4.317901e-18, λ1=9.821030e-06, λ2=9.919407e-06, nullity_est=1, eval=eigsh
N=14: max |S_C 1_C|=4.386682e-16, L2 row-sum residual=7.198143e-16
N=14: matrix-free rho_sup=5.956359e-01, lambda1(L_good)=2.005096e-05, lambda_max(L_bad)=4.958120e-03, resid=5.69e-07

M_GC norms: 4.34e-03, 4.34e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.