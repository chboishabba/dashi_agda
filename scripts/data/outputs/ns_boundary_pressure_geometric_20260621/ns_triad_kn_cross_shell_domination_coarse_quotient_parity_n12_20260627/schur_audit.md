# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 12 | 6390 | 26 | 6364 | 2.044918e-06 | 2.459413e-19 | 7.995154e-06 | 8.315004e-06 | 1 | 2.27e-16 | 1.0000 | schur_psd |

N=12: λ0=2.459413e-19, λ1=7.995154e-06, λ2=8.315004e-06, nullity_est=1, eval=eigsh
N=12: max |S_C 1_C|=2.272488e-16, L2 row-sum residual=5.653588e-16
N=12: matrix-free rho_sup=6.589782e-01, lambda1(L_good)=3.779648e-05, lambda_max(L_bad)=5.074208e-03, resid=1.65e-05
N=12: coarse quotient rho_sup=5.068700e-01, class_count=334, rho/full=0.769175687100976, overlap=0.12206361138846478

M_GC norms: 3.33e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.