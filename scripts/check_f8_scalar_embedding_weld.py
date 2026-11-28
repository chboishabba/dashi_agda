"""Exact moving scalar Israel row elimination; not a coercivity theorem.
Uses normal-parallel frame convention of check_f8_coupled_collar.py.
"""
import sympy as s

def exact():
    b,B=s.symbols('b B',positive=True); k=s.symbols('k',real=True)
    F,G,u,fn,gn,un,f,ft,ftt=s.symbols('F G u Fn Gn un f ft ftt')
    W,Wt,lapse=s.symbols('W Wt lapse')
    eta=s.diag(-1,1,1,1); K=s.diag(-1/B,-B,-B,-B)
    # Use independent frame jets; do not identify coordinate and parallel jets.
    l,X,Y,ln,Xn,Yn=s.symbols('l X Y ln Xn Yn')
    h=s.diag(l,X,Y,Y); dh=s.diag(ln,Xn,Yn,Yn)
    D=s.zeros(4); D[0,0]=Wt; D[1,0]=s.I*k*b*W
    for i in range(1,4): D[i,i]=-b*W
    metric=eta*(dh-D-D.T-h*K+K*h-lapse*eta*K)/2
    Hess=s.diag(-ftt,-k*k*b*b*f-b*ft,-b*ft,-b*ft)
    Hess[0,1]=-s.I*k*b*(ft-b*f); Hess[1,0]=-Hess[0,1]
    bend=-Hess+f*(s.eye(4)-K*K)
    total=metric+bend
    rho,p,j0,jx,jy,jm=s.symbols('rho p j0 jx jy jm')
    # Scalar isotropic linear material: Israel diagonal (2rho+3p,-rho,...).
    stress=s.diag(2*rho+3*p,-rho,-rho,-rho)
    assert s.expand(total[1,1]-total[2,2]-(Xn-Yn)/2-k*k*b*b*f)==0
    qn=s.symbols('Zn'); diff=s.expand((total[1,1]-total[2,2]).subs(Xn,Yn-6*qn))
    assert s.solve(diff-jx+jy,qn)==[(b*b*f*k*k-jx+jy)/3]
    # Transverse row gives material density; temporal row gives embedding acceleration.
    density=s.solve(total[2,2]-stress[2,2]-jy,rho)[0]
    acceleration=s.solve((total[0,0]-stress[0,0]-j0).subs(rho,density),ftt)[0]
    assert s.expand((total[2,2]-stress[2,2]-jy).subs(rho,density))==0
    assert s.simplify((total[0,0]-stress[0,0]-j0).subs(rho,density).subs(ftt,acceleration))==0
    assert s.expand(total[0,1]-s.I*k*b*(W/2+ft-b*f))==0
    # Mixed row must be checked, not inferred from diagonal elimination.
    assert s.simplify(total[0,1]+total[1,0])==0
    # Original material coefficients positive for 0<b<=1: B<=sqrt2<2.
    # Kclock=b²/(3B)-b⁴/12 >= b²/12, w=b⁴/12>0.
    assert s.simplify(b*b/6-b**4/12-b*b/12)==b*b*(1-b*b)/12
    print('7 exact moving-wall row / coefficient checks PASS')
    print('density:',density,'\nembedding acceleration:',acceleration)
    return density,acceleration

if __name__=='__main__': exact()
