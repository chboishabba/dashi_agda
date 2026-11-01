# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 16 | 11574 | 26 | 11548 | 1.037211e-06 | -1.826149e-18 | 7.449612e-06 | 7.910530e-06 | 1 | 4.48e-16 | -1.0000 | schur_psd |

N=16: λ0=-1.826149e-18, λ1=7.449612e-06, λ2=7.910530e-06, nullity_est=1, eval=eigsh
N=16: max |S_C 1_C|=4.477755e-16, L2 row-sum residual=8.485909e-16
N=16: matrix-free rho_sup=5.811855e-01, lambda1(L_good)=1.967223e-05, lambda_max(L_bad)=5.053541e-03, resid=7.74e-07

M_GC norms: 3.33e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.