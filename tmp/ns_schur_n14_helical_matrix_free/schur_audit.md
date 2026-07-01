# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 14 | 8790 | 26 | 8764 | 1.543480e-06 | -5.334603e-19 | 1.077726e-05 | 1.156614e-05 | 1 | 3.90e-16 | 1.0000 | schur_psd |

N=14: λ0=-5.334603e-19, λ1=1.077726e-05, λ2=1.156614e-05, nullity_est=1, eval=eigsh
N=14: max |S_C 1_C|=3.899875e-16, L2 row-sum residual=6.991601e-16
N=14: helical coupling kappa=5.948151e-01, bound=9.156400e-06, eval=matrix-free

M_GC norms: 3.33e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.