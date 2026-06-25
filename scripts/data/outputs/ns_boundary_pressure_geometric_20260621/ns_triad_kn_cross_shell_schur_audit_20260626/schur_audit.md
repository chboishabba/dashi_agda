# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | corr(balance) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 12 | 6390 | 26 | 6364 | 2.698284e-06 | 9.655696e-18 | 7.795517e-06 | 7.939439e-06 | 1 | -0.0867 | schur_psd |
| 14 | 8790 | 26 | 8764 | 2.022647e-06 | -2.972669e-18 | 9.821030e-06 | 9.919407e-06 | 1 | 0.0739 | schur_psd |

N=12: λ0=9.655696e-18, λ1=7.795517e-06, λ2=7.939439e-06, nullity_est=1, eval=eigsh
N=14: λ0=-2.972669e-18, λ1=9.821030e-06, λ2=9.919407e-06, nullity_est=1, eval=eigsh

M_GC norms: 4.34e-03, 4.34e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.