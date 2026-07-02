# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 6 | 1494 | 26 | 1468 | 1.736470e-05 | — | — | — | 1 | 1.55e-16 | 1.0000 | schur_psd |

N=6: , nullity_est=1, eval=dense
N=6: max |S_C 1_C|=1.547699e-16, L2 row-sum residual=3.043178e-16
N=6: Gate2A exact_identity=False, linearity_exact=False, abs_bounds=[1.410578e+00, 6.937127e+00], neg_bounds=[1.917877e+00, 4.539338e+01]
N=6: Gate2A transport directional=1.681991e-01, coarse_upper=1.954640e+01, improvement=1.162099e+02, margin_positive=True
N=6: matrix-free rho_sup=6.073952e-01, lambda1(L_good)=1.192017e-04, lambda_max(L_bad)=4.908434e-03, resid=5.70e-07

M_GC norms: 4.36e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.