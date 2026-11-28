"""F8 nonzero spatial-mode scalar geometry: exact transverse reduction.
Einstein-frame radion and Israel boundary; no scalar coercivity/existence claim.
"""
import sympy as s
from itertools import product

def ricci(g,coords):
    n=g.rows; ix=range(n); gi=g.inv()
    G={(a,b,c):sum(gi[a,l]*(g[l,c].diff(coords[b])+g[l,b].diff(coords[c])-g[b,c].diff(coords[l]))/2 for l in ix) for a,b,c in product(ix,repeat=3)}
    R=s.Matrix(n,n,lambda i,j:sum(G[k,i,j].diff(coords[k])-G[k,i,k].diff(coords[j]) for k in ix)+sum(G[k,k,l]*G[l,i,j]-G[k,j,l]*G[l,i,k] for k,l in product(ix,repeat=2)))
    return R,G

def exact():
    t,n,x,y,z=s.symbols('t n x y z',real=True); X=(t,n,x); ix=range(3)
    a=s.Function('a')(t,n); N=s.Function('N')(t,n); p=s.Function('p')(t,n,x)
    g=s.diag(-N*N,1,a*a); gi=g.inv(); dp=s.Matrix([p.diff(c) for c in X]); norm=(dp.T*gi*dp)[0]
    R,G=ricci(g,X); H=s.Matrix(3,3,lambda i,j:p.diff(X[i],X[j])-sum(G[k,i,j]*dp[k] for k in ix)); box=s.trace(gi*H)
    # Verify exact 5D warped Ricci on a nontrivial variable radion and base.
    R5,_=ricci(s.diag(-N*N,1,a*a,s.exp(2*p),s.exp(2*p)),(t,n,x,y,z))
    zero=lambda A:A.applyfunc(s.simplify)==s.zeros(*A.shape)
    assert zero(R5[:3,:3]-R+2*(H+dp*dp.T))
    assert s.simplify(s.exp(-2*p)*R5[3,3]+box+2*norm)==0
    assert zero(R5[:3,3:5]) and s.simplify(R5[3,3]-R5[4,4])==0
    # 3D Einstein-frame conformal identity gE=e^(4p)g.
    ge=s.exp(4*p)*g; RE,GE=ricci(ge,X)
    assert zero(RE-R+2*H+2*g*box-4*dp*dp.T+4*g*norm)
    HE=s.Matrix(3,3,lambda i,j:p.diff(X[i],X[j])-sum(GE[k,i,j]*dp[k] for k in ix))
    assert s.simplify(s.trace(ge.inv()*HE)-s.exp(-4*p)*(box+2*norm))==0
    # Vacuum original Ric5+4g5=0 gives R_E=6 dp dp -12 e^-4p gE.
    B0=s.symbols("B0"); want=2*(H+dp*dp.T)-4*g-2*H-2*g*B0+4*dp*dp.T-4*g*norm
    assert zero(want.subs(B0,4-2*norm)-6*dp*dp.T+12*g)
    # Original full Israel, including tension, with 2x2 base stress and two equal transverse rows.
    S=s.Matrix(2,2,s.symbols('S:4')); P=s.symbols('P'); scale=s.symbols('c',positive=True)
    tr=S.trace()+2*P; kb=-3*S+tr*s.eye(2); pn=-3*P+tr
    ke=scale*(kb+2*pn*s.eye(2)); pne=scale*pn
    assert s.expand(pne-scale*(S.trace()-P))==0
    assert (ke-ke.trace()*s.eye(2)+3*scale*S).applyfunc(s.expand)==s.zeros(2)
    # 3D Einstein action kinetic and potential EL sign.
    f=s.symbols('f',real=True); assert s.diff(12*s.exp(-4*f),f)==-48*s.exp(-4*f)
    print('9 grouped exact warped Ricci / Einstein-frame / Israel checks PASS')

if __name__=='__main__':exact()
