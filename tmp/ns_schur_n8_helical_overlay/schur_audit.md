# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 8 | 2742 | 26 | 2716 | 6.117026e-06 | — | — | — | 1 | 1.16e-16 | 1.0000 | schur_psd |

N=8: , nullity_est=1, eval=dense
N=8: max |S_C 1_C|=1.164433e-16, L2 row-sum residual=2.317873e-16
N=8: Q helical-lift offdiag/total=1.953136e-01, basis_relevant=True, blockdiag=False

M_GC norms: 3.34e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.