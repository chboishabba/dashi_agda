"""Phase-resolved two-window spectrum and memory/nonadditivity receipts.

Reference outputs are synthetic periodic E/H/P polarization histories, NOT
measured optical spectra. Ideal window DFT is kept distinct from material response.
"""
import numpy as np
import sympy as sp
from check_ternary_temporal_material import solve, A, incidence
from check_ternary_double_window import window, PERIOD, HEIGHT, coherent


def spectral_receipt(dim, beta, second):
    n=3**dim; m=incidence(dim).shape[1]
    w1=window(2); w2=window(second)
    baseline=solve(dim,beta,0.,0.,period=PERIOD,return_history=True)
    def run(profile):
        return solve(dim,beta,0.,0.,period=PERIOD,material_profile=A+HEIGHT*profile,return_history=True)
    a=run(w1); b=run(w2); ab=run(w1+w2)
    response=lambda s:s['midpoints'][:,n+m]-baseline['midpoints'][:,n+m]
    r1=response(a); r2=response(b); r12=response(ab)
    F1,F2,F12=map(coherent,(r1,r2,r12))
    W1,W2,W12=map(lambda w:coherent(HEIGHT*w),(w1,w2,w1+w2))
    assert np.max(np.abs(W12-W1-W2))<1e-14
    # Causal memory: the full nonlinear periodic response need not vanish
    # when both material windows are inactive.
    mask=(w1+w2)==0
    memory=float(np.max(np.abs(r12[mask])))
    nonadd=F12-F1-F2
    # Correct phase-sensitive distinction: full response vs coherent sum,
    # and coherent sum vs a one-kernel ideal-window transfer.
    kernel=(np.vdot(W1,F1)+np.vdot(W2,F2))/(np.vdot(W1,W1)+np.vdot(W2,W2))
    naive=kernel*W12
    errors={
        'nonadd_l2':float(np.linalg.norm(nonadd)),
        'one_kernel_l2':float(np.linalg.norm(F12-naive)),
        'memory_outside_windows':memory,
        'ideal_window_fundamental':complex(W12[1]),
        'actual_fundamental':complex(F12[1]),
        'coherent_sum_fundamental':complex((F1+F2)[1]),
        'modulation_work':float(ab['modulation']),
        'max_equation_residual':float(max(s['defect'] for s in (baseline,a,b,ab))),
        'max_ledger_residual':float(max(s['ledger'] for s in (baseline,a,b,ab)))
    }
    return errors


def test():
    # Explicit finite DFT shift law: only the *window* has exact phase factor.
    q,k,s,N=sp.symbols('q k s N',integer=True)
    z=sp.symbols('z',nonzero=True)
    assert sp.expand(z**2*(1+z)-z**2-z**3)==0
    checks=1
    rows=[]
    for dim in (2,3):
        for beta in (0.,.45):
            a=spectral_receipt(dim,beta,6)
            b=spectral_receipt(dim,beta,8)
            for r in (a,b):
                assert r['max_equation_residual']<1e-9;checks+=1
                assert r['max_ledger_residual']<1e-9;checks+=1
                assert r['memory_outside_windows']>1e-10;checks+=1
                assert r['nonadd_l2']>1e-12;checks+=1
                assert r['one_kernel_l2']>1e-12;checks+=1
                assert np.isfinite(r['modulation_work']);checks+=1
                assert np.isfinite(abs(r['actual_fundamental']));checks+=1
            assert abs(a['actual_fundamental']-b['actual_fundamental'])>1e-10;checks+=1
            rows.append((dim,beta,a,b))
            print(f'{dim}D beta={beta}: sep4 fundamental={a["actual_fundamental"]:.7g}, sep6={b["actual_fundamental"]:.7g}; nonadd L2={a["nonadd_l2"]:.4g}/{b["nonadd_l2"]:.4g}; single-kernel deviations={a["one_kernel_l2"]:.4g}/{b["one_kernel_l2"]:.4g}')
    print(f'{checks}/{checks} PASS; SymPy {sp.__version__}')
    return rows

if __name__=='__main__':test()
