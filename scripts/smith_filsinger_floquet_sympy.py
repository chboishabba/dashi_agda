"""Exact finite periodic response; synthetic, not a measured scattering port."""
import sympy as S

def floquet(maps, lam, source):
    if not maps or lam == 0:
        raise ValueError('nonempty period and nonzero multiplier required')
    lam=S.sympify(lam); N=len(maps); d=maps[0][0].rows
    M=S.eye(d); b=S.zeros(d,1)
    for j,(T,F) in enumerate(maps):
        M=T*M; b=T*b+F*source*lam**j
    L=lam**N*S.eye(d)-M
    if L.det()==0:
        raise ValueError('singular Floquet resolvent')
    z=L.inv()*b
    states=[z]
    for j,(T,F) in enumerate(maps):
        states.append(T*states[-1]+F*source*lam**j)
    return M, states

def two_phase_sidebands(states, lam):
    """DFT of periodic envelope for N=2; exact zero and Nyquist sidebands."""
    if len(states)!=3: raise ValueError('two intervals required')
    a,b=states[0],states[1]/S.sympify(lam)
    return (a+b)/2,(a-b)/2
