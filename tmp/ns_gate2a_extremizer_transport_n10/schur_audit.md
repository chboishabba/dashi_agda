# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 10 | 4374 | 26 | 4348 | 4.290627e-06 | — | — | — | 1 | 2.38e-16 | -1.0000 | schur_psd |

N=10: , nullity_est=1, eval=dense
N=10: max |S_C 1_C|=2.377113e-16, L2 row-sum residual=5.138709e-16
N=10: Gate2A exact_identity=False, linearity_exact=False, abs_bounds=[1.431504e+00, 6.868565e+00], neg_bounds=[1.874088e+00, 4.671797e+01]
N=10: Gate2A transport directional=1.678166e-01, coarse_upper=2.005134e+01, improvement=1.194837e+02, margin_positive=True
N=10: matrix-free rho_sup=6.144013e-01, lambda1(L_good)=5.035307e-05, lambda_max(L_bad)=5.011315e-03, resid=4.59e-07

M_GC norms: 4.34e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.