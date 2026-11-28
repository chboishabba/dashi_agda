"""Exact dynamic replacement of a matched resistance by the existing 2:1 converter.
Normalized complex envelope ports, not a physical broadband radial interconnect.
"""
import sympy as S
from solar_steelman_unity import zero, geometry, modal_cycle, rhs
from solar_steelman_hf_continuous import two_mode_hamiltonian, continuous


def run():
    # Power wave port with reference resistance 1: effort e=s+r,
    # flow i=s-r. Converter r=s-sqrt(2)*a, hence i=sqrt(2)*a.
    # Its input effort e=2*s-sqrt(2)*a supplies adot=e/sqrt(2)-c.
    ar,ai,cr,ci,br,bi,dr,di,sr,si=S.symbols('ar ai cr ci br bi dr di sr si',real=True)
    a,c,b,d,s=[x+S.I*y for x,y in ((ar,ai),(cr,ci),(br,bi),(dr,di),(sr,si))]
    x=S.Matrix([a,c,b,d]); r=s-S.sqrt(2)*a; e=s+r; i=s-r
    f=rhs(x,s);assert zero(f[0]-e/S.sqrt(2)+c)
    power=S.re(S.conjugate(e)*i)
    assert zero(power-s*S.conjugate(s)+r*S.conjugate(r))
    Udot=2*S.re(S.conjugate(a)*f[0]+S.conjugate(c)*f[1])+S.re(S.conjugate(b)*f[2]+S.conjugate(d)*f[3])
    assert zero(Udot-power+b*S.conjugate(b)+d*S.conjugate(d))
    # Reverse target is a true load of effort=flow, not a parallel resistor.
    F,_=geometry();x0,M=modal_cycle(F);a0=x0[0]
    assert zero(1-S.sqrt(2)*a0)
    # Attach arbitrary SPD physical resistance metric via real transformer C.
    C=S.Matrix([[2,1],[0,1]]);R=C.T*C
    j=S.Matrix(S.symbols('j:2',real=True));v=S.Matrix(S.symbols('v:2',real=True))
    assert S.expand((C*j).dot(C.T.inv()*v)-j.dot(v))==0
    assert C.T*C==R
    # Attach a reciprocal lossless dynamical exterior in place of the
    # instantaneous incident wave. Two complex storage modes fwd/back,
    # source external damping and converter coupling through opposite signs.
    # Envelope state y: ydot=sqrt(2)*s-y-a, converter adot=y-c,
    # with source outgoing s-sqrt(2)*y. Reverse solve y=a=c=b=d=1/sqrt(2).
    # For this 5-mode chain that choice does NOT solve adot/cdot together:
    # adding a relay flips the steady impedance; reverse solve coupling
    # and phase rather than silently insert a matched termination.
    # Use TWO relay coordinates y,z, preserving skew coupling, original a port
    # becomes internal, its original damping removed. y'=sqrt2*s-y-z,
    # z'=y-a, a'=z-c, c'=a-g*b*d, etc.
    yr,yi,zr,zi=S.symbols('yr yi zr zi',real=True);y=yr+S.I*yi;z=zr+S.I*zi
    ff=S.Matrix([S.sqrt(2)*s-y-z,y-a,z-c,f[1],f[2],f[3]])
    state=S.Matrix([y,z,a,c,b,d]); t=1/S.sqrt(2);nom=S.ones(6,1)*t
    vars=[yr,zr,ar,cr,br,dr,yi,zi,ai,ci,bi,di]
    sub=dict(zip(vars+[sr,si],[t]*6+[0]*6+[1,0]))
    assert zero(ff.subs(sub))
    balance=2*S.re(sum(S.conjugate(state[k])*ff[k] for k in range(4)))+S.re(sum(S.conjugate(state[k])*ff[k] for k in (4,5)))
    assert zero(balance-s*S.conjugate(s)+(s-S.sqrt(2)*y)*S.conjugate(s-S.sqrt(2)*y)+b*S.conjugate(b)+d*S.conjugate(d))
    # Stability certificate in weighted energy coordinates. Existing modal
    # linearization may not remain Schur after adding external memory.
    Freal=S.Matrix([S.re(v).expand(complex=True) for v in ff]+[S.im(v).expand(complex=True) for v in ff]); A=Freal.jacobian(vars).subs(sub)
    # At the occupied nonlinear branch the unweighted linearization is dissipative.
    H=-(A+A.T)/2; assert H.is_positive_semidefinite
    O=S.Matrix.vstack(*[H*A**k for k in range(12)]); assert O.rank()==12
    I=S.eye(12); L=(I-A/2).inv(); P=L*(I+A/2)
    assert zero(I-P.T*P-2*L.T*H*L)
    # Exact unseeded equilibrium at source reflection = 1; no spontaneous seed.
    unseed=dict(zip(vars+[sr,si],[0,S.sqrt(2),0,S.sqrt(2),0,0]+[0]*6+[1,0]));assert zero(ff.subs(unseed))
    two_mode_hamiltonian(); continuous()
    print('PASS dynamic effort-flow converter, transformer power identity, two-relay exact unity, observability rank',O.rank())
    print('PASS causal envelope storage and local Schur, incident=1 reflected=0 useful=1; physical radial/material realization open')
if __name__=='__main__':run()
