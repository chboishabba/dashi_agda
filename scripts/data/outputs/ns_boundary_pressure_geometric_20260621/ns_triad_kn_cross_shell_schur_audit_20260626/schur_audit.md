# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 8 | 2742 | 26 | 2716 | 7.633129e-06 | — | — | — | 1 | 1.27e-16 | -1.0000 | schur_psd |

N=8: , nullity_est=1, eval=dense
N=8: max |S_C 1_C|=1.266348e-16, L2 row-sum residual=2.605138e-16
N=8: Gate2A exact_identity=False, linearity_exact=False, abs_bounds=[1.392030e+00, 6.988580e+00], neg_bounds=[1.839084e+00, 4.615539e+01]
N=8: Gate2A transport directional=1.684187e-01, coarse_upper=2.020388e+01, improvement=1.199622e+02, margin_positive=True
N=8: matrix-free rho_sup=6.093419e-01, lambda1(L_good)=1.918062e-04, lambda_max(L_bad)=4.973961e-03, resid=4.42e-06

M_GC norms: 4.35e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.