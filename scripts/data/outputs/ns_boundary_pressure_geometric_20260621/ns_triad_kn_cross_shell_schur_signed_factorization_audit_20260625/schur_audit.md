# NS Triad K_N Cross-Shell Schur Symbolic Audit

- candidate only: `True`
- theorem promoted: `False`
- gate1 closed: `False`
- gate1 supported at tested shells: `True`

## Schur Audit Summary

| N | block | G | C | M_CC λ_min | S_C λ0 | S_C λ1 | S_C λ2 | nullity est | max \|S_C 1\| | corr(constant) | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 6 | 1494 | 26 | 1468 | 1.736470e-05 | — | — | — | 1 | 1.55e-16 | 1.0000 | schur_psd |
| 8 | 2742 | 26 | 2716 | 7.633129e-06 | — | — | — | 1 | 1.27e-16 | -1.0000 | schur_psd |

N=6: , nullity_est=1, eval=dense
N=6: max |S_C 1_C|=1.547699e-16, L2 row-sum residual=3.043178e-16
N=6: sign audit positive_offdiag=716390, negative-edge components=1, route=signed_psd_required
N=6: signed-factorization rho_sup=6.076053e-01, lambda1(L_good)=1.182587e-04, domination=True
N=8: , nullity_est=1, eval=dense
N=8: max |S_C 1_C|=1.266348e-16, L2 row-sum residual=2.605138e-16
N=8: sign audit positive_offdiag=2200624, negative-edge components=1, route=signed_psd_required
N=8: signed-factorization rho_sup=6.256983e-01, lambda1(L_good)=4.361920e-05, domination=True

M_GC norms: 4.36e-03, 4.35e-03
Verdicts: ['schur_psd']
Gate 1 target = S_C ⪰ 0 and dim ker S_C = 1: SUPPORTED at tested N, not proved.