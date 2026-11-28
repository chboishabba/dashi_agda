"""Two-face original TOV Israel/GHY canonical second-boundary jets.

Common induced metric and moved embedding required. Independent K jets are
not presumed equal; the surviving jump is an explicit obstruction.
Pointwise timelike-boundary algebra, not a completed bulk EH/GHY/corner action.
"""
import sympy as s


def zero(m):
    return m.applyfunc(s.factor)==s.zeros(*m.shape)


def main():
    e=s.symbols('eps',real=True)
    g=s.diag(-2,3,5)
    k=s.Matrix([[1,2,0],[2,3,1],[0,1,4]])/7
    h=s.Matrix([[3,1,2],[1,-2,3],[2,3,1]])/11
    q=s.Matrix([[1,2,-1],[2,0,1],[-1,1,3]])/13
    h2=s.Matrix([[2,1,1],[1,3,-2],[1,-2,4]])/17
    q2=s.Matrix([[0,1,3],[1,4,-1],[3,-1,2]])/19
    # Same induced metric on each side, including second shape variation.
    ge=g+e*h+e*e*h2/2
    kp=k+e*q+e*e*q2/2
    # Independent two-face extrinsic perturbation and acceleration.
    d=s.Matrix([[2,-1,0],[-1,1,2],[0,2,-3]])/23
    d2=s.Matrix([[1,0,-1],[0,-2,1],[-1,1,4]])/29
    km=kp+e*d+e*e*d2/2
    def momentum(K):
        inv=ge.inv()
        return s.sqrt(-ge.det()/(-g.det()))*(inv*K*inv-s.trace(inv*K)*inv)
    # Exact density-normalized canonical jump with arbitrary e-dependent K.
    J=s.simplify(momentum(km)-momentum(kp))
    inv=g.inv()
    rev=lambda X:inv*X*inv-s.trace(inv*X)*inv
    assert zero(J.subs(e,0))
    assert zero(J.diff(e).subs(e,0)-rev(d))
    vol=s.trace(inv*h)/2
    dinv=-inv*h*inv
    drevd=dinv*d*inv+inv*d*dinv-s.trace(dinv*d)*inv-s.trace(inv*d)*dinv
    assert zero(J.diff(e,2).subs(e,0)-rev(d2)-2*(drevd+vol*rev(d)))
    # Literal second boundary variation: for gamma'=h, first momentum jump
    # zero, second action boundary pairing is h·delta[P].
    bulk_boundary_2=s.trace(J.diff(e).subs(e,0)*h)
    assert s.factor(bulk_boundary_2-s.trace(rev(d)*h))==0
    assert bulk_boundary_2!=0  # nonzero Israel mismatch is not free.
    # If first K jet is continuous, second action boundary work vanishes.
    assert zero(rev(s.zeros(3)))
    # Injective 3D trace reversal: no hidden first-order discontinuity.
    Z=s.Matrix(3,3,lambda i,j:s.Symbol('Z%d%d'%(min(i,j),max(i,j))))
    assert zero(g*rev(Z)*g-s.trace(g*rev(Z))*g/2-Z)
    # With different induced metrics, previous cancellation is invalid.
    jh=s.Matrix([[0,2,1],[2,1,0],[1,0,-1]])/31
    inv2=(ge+e*jh).inv(); Km=kp
    mismatched= s.sqrt(-(ge+e*jh).det()/(-g.det()))*(inv2*Km*inv2-s.trace(inv2*Km)*inv2)-momentum(kp)
    assert not zero(mismatched.diff(e).subs(e,0))
    print('PASS exact two-face momentum second jet, nonzero mismatch and continuous-interface cancellation')
    print('OPEN physical moving embedding, full Einstein/GHY/corners and graph-domain canonical symplectic flux')

if __name__=='__main__':main()
