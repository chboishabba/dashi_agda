# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 10 | 4374 | 26 | 4348 | 3.334351e-06 | 2.174854e-18 | 1.866017e-05 | 1.947443e-05 | 1 | 2.79e-16 | 1.0000 | schur_psd |

N=10: λ0=2.174854e-18, λ1=1.866017e-05, λ2=1.947443e-05, nullity_est=1, eval=eigsh
N=10: max |S_C 1_C|=2.786942e-16, L2 row-sum residual=5.267293e-16
N=10: Q helical-lift offdiag/total=1.272900e-01, basis_relevant=True, blockdiag=False

M_GC norms: 3.33e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.