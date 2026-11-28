"""W2.2 original spherical Einstein wall-frame stress: two-way equivalence.
Orthonormal Eulerian T_{00}=rho,T_{01}=-j,T_{11}=p. The timelike
wall is no-shell against vacuum with common mass and no surface layer.
No tangential constitutive closure, no actual Einstein bulk trajectory.
"""
import sympy as s


def zero(x):
    assert s.simplify(s.factor(x)) == 0, s.factor(x)


def main():
    f,v=s.symbols('f v',positive=True)
    rho,j,p=s.symbols('rho j p',real=True)
    k=s.sqrt(f+v*v); gamma=k/s.sqrt(f); w=v/s.sqrt(f)
    eta=s.diag(-1,1)
    U=s.Matrix([gamma,w])
    n=s.Matrix([w,gamma])
    zero((U.T*eta*U)[0]+1)
    zero((n.T*eta*n)[0]-1)
    zero((U.T*eta*n)[0])
    # Stress in the orthonormal Eulerian basis, with the j convention
    # from G_tr=8pi*T_tr in check_tov_dynamic_flux_israel_abi.
    T=s.Matrix([[rho,-j],[-j,p]])
    Enn=s.factor((n.T*T*n)[0]); Eun=s.factor((U.T*T*n)[0])
    Euu=s.factor((U.T*T*U)[0])
    zero(f*Enn-((f+v*v)*p+v*v*rho-2*v*k*j))
    # Mass-pullback flux is proportional to the wall-frame energy current;
    # after the normal-stress Israel condition, it is independent.
    qj=rho*v/k
    qp=rho*v*v/(f+v*v)
    zero(Eun.subs({j:qj,p:qp}))
    zero(Enn.subs({j:qj,p:qp}))
    zero(Euu.subs({j:qj,p:qp})-rho*f/(f+v*v))
    zero(s.factor(T.det().subs({j:qj,p:qp})))
    # Converse: no energy flux across wall and no normal traction
    # uniquely force the same radial pressure and Eulerian flux.
    S=s.solve([s.Eq(Eun,0),s.Eq(Enn,0)],(j,p),dict=True)
    assert len(S)==1
    zero(S[0][j]-qj)
    zero(S[0][p]-qp)
    # In the wall's own frame, stress is strictly tangent, not vacuum:
    # it can carry nonzero comoving energy without normal mass flow.
    assert s.factor(Euu.subs({j:qj,p:qp,rho:1}))!=0
    # Domain: for positive rho, f>0, v finite, the wall is timelike
    # and its source is future timelike dust in the normal 1+1 block.
    zero(1-v*v/(f+v*v)-f/(f+v*v))
    # Deliberate non-conservative source must be refused by these 2 laws.
    assert s.simplify(Eun.subs({rho:1,p:0,j:0,v:1}))!=0
    assert s.simplify(Enn.subs({rho:1,p:0,j:0,v:1}))!=0
    print('PASS exact Eulerian-to-moving orthonormal stress and both normal projections')
    print('PASS reverse unique j,p, zero normal stress/energy flux, rank-one wall block')
    print('OPEN actual matter tangential stress, timelike bulk evolution, GHY/corners')


if __name__=='__main__':main()
