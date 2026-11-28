"""Exact enriched Whitney material metric and reciprocal dynamic range.
Normalized kinetic coefficient 1; no physical plasma parameter admission.
"""
import sympy as S
from itertools import combinations
from solar_steelman_seven_edge import run as seven
from solar_spherical_whitney import shell_mesh
from solar_steelman_whitney_lift import solve


def run(d=None):
    if d is None: d=seven()
    M,N,G,C,D,W=d['M'],d['N'],d['G'],d['C'],d['D'],d['W']
    xyz,s,m,_=shell_mesh([1,1.5,2]);piv=list(d['piv'])
    # Actual integral of J.J, including constant/Whitney cross terms.
    H0=S.zeros(W.cols)
    for k,t in enumerate(s[3]):
        a=S.Matrix([[S.Rational(float(v)) for v in xyz[j]] for j in t])
        V=abs((a[1:,:]-S.ones(3,1)*a[0,:]).det())/6
        H0[3*k:3*k+3,3*k:3*k+3]=V*S.eye(3)
    cross=W[piv,:].T
    H=H0.row_join(cross).col_join(cross.T.row_join(M.extract(piv,piv)))
    B=d['Wplus'];assert H==H.T
    # Orthogonalize enrichment against constants, not against the port.
    K=M.extract(piv,piv)-cross.T*H0.inv()*cross
    assert all(K[:j,:j].det()>0 for j in range(1,len(piv)+1))
    # Minimum kinetic-energy current lift, computed with the actual Gram.
    # R=B H^-1 B^T, x*=H^-1 B^T R^-1 j; all null currents retained.
    Hinv=H0.inv();F=Hinv*cross;Ki=K.inv()
    U0=Hinv*W.T;U1=Ki*(B[:,W.cols:].T-cross.T*U0)
    U=(U0-F*U1).col_join(U1);assert H*U==B.T
    R=B*U;assert R==R.T
    print("PASS block Gram inverse",flush=True)
    for p,trace in [(d['high'][0],d['mid']),(d['low'][0],d['inner'])]:
        j=trace.T*p;lam=S.I*solve(R,S.im(j));z=U*lam
        assert (B*z-j).applyfunc(S.simplify)==S.zeros(M.rows,1)
        assert (H*z-B.T*lam).applyfunc(S.simplify)==S.zeros(B.cols,1)
        assert S.simplify((z.H*H*z)[0]-(j.H*lam)[0])==0
    # Actual reciprocal lossless linear material dynamics:
    # M Edot=C^T N b-B z+f, bdot=-C E, H zdot=B^T E.
    # Block structure proves exact skew energy pairing, including Gauss.
    A=S.zeros(M.rows+N.rows+H.rows)
    a=M.rows;b=a+N.rows
    A[:a,a:b]=C.T*N;A[a:b,:a]=-N*C
    A[:a,b:]=-B;A[b:,:a]=B.T
    assert A+A.T==S.zeros(A.rows)
    # Charge continuity: qdot=G^T(f-Bz); magnetic divergence invariant.
    assert G.T*C.T==S.zeros(G.cols,C.rows)
    assert D*C==S.zeros(D.rows,C.cols)
    # Crucial dynamic compatibility: at harmonic w and prescribed field E,
    # unconstrained lossless Drude response is z=B^T E/(iw) in H metric.
    # Full rank alone does NOT imply ability to choose current independently.
    # With E=0, nonzero required harmonic current needs another reaction.
    assert H.rows==147  # SPD established by the block Schur complement
    print('PASS actual kinetic Gram SPD, minimum kinetic lift at both bands, reciprocal energy and charge identity')
    print('Dynamic constitutive and HF reaction still required; no physical unity promotion')
    return dict(d=d,H=H,B=B,U=U,R=R)
if __name__=='__main__':run()
