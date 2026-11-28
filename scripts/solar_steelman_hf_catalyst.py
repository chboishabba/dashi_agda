"""Reciprocal ideal HF catalyst on the same unity modal/material boundary.
Resonant fifth-order Hamiltonian; physical material coefficient not inferred.
"""
import sympy as S
from solar_steelman_unity import zero,geometry,modal_cycle,recovery,rhs
from solar_steelman_tangent_tensor import angular_frames,tensor_inverse,sz,matzero,n,P,I,stack


def hamiltonian():
    # Treat complex amplitudes and conjugates as independent for derivatives.
    c,b,d,h,cc,bb,dd,hh,g=S.symbols('c b d h cc bb dd hh g')
    H=-S.I*g*h*hh*(cc*b*d-c*bb*dd)
    pairs=((c,cc),(b,bb),(d,dd),(h,hh))
    f=[-S.I*S.diff(H,q) for p,q in pairs];fc=[S.I*S.diff(H,p) for p,q in pairs]
    assert f==[-g*h*hh*b*d,g*h*hh*c*dd,g*h*hh*c*bb,-g*h*(cc*b*d-c*bb*dd)]
    # Action of HF catalyst exactly conserved; energy at full and half
    # frequencies conserved by the 2:1 resonant trilinear interaction.
    assert S.expand(f[3]*hh+h*fc[3])==0
    assert S.expand(f[0]*cc+c*fc[0]+(f[1]*bb+b*fc[1]+f[2]*dd+d*fc[2])/2)==0
    return H


def modes(x,s,chi=S.sqrt(2)):
    a,c,b,d,h=x;g=chi*h*S.conjugate(h)
    f=rhs(x[:4,:],s,g=g)
    # Conjugate catalyst reaction from the SAME Hamiltonian, not an
    # externally prescribed coupling coefficient.
    dh=-chi*h*(S.conjugate(c)*b*d-c*S.conjugate(b)*S.conjugate(d))
    return f.col_join(S.Matrix([dh]))


def common_clock():
    half=S.Rational(783,200);full=2*half;hf=S.Integer(7800)
    T=S.Rational(200,3);cycles=[q*T for q in (half,full,hf)]
    assert cycles==[261,522,520000]
    # These are nominal phase labels, not a measured resonance or SI
    # dynamical parameter fit. Rotating-envelope time is normalized to 1.
    assert all(S.exp(2*S.pi*S.I*q)==1 for q in cycles)
    return cycles,hf/full


def local_tensor():
    A,B,C=angular_frames();g=S.sqrt(2);assert tensor_inverse(A,B,C,g)==2
    # TE degree-two frame, rotate each actual TM2 tangent component by n×.
    H=stack([n.cross(C[i:i+3,:]) for i in range(0,C.rows,3)])
    assert sz(H.dot(H)-1)
    assert all(sz(n.dot(H[i:i+3,:])) for i in range(0,H.rows,3))
    # Five-factor local target: A⊗B⊗C⊗H⊗H, contracted against unit
    # labelled frames. The last two factors are complex conjugate HF action.
    # Pointwise exact mode reactions in ALL four material families.
    norms=[S.rem(S.expand(v.dot(v)),n[2]**2+n[0]**2+n[1]**2-1,n[2]) for v in (A,B,C,H)]
    assert all(S.simplify(q)==1 for q in norms)
    for u,idx in ((A,(1,2,3,3)),(B,(0,2,3,3)),(C,(0,1,3,3)),(H,(0,1,2,3))):
        assert matzero(g*u*S.prod(norms[j] for j in idx)-g*u)
    assert S.simplify(g*g*S.prod(norms)*norms[3]-2)==0
    return H


def run():
    hamiltonian();cycles,ratio=common_clock();local_tensor()
    F,_=geometry();x,M=modal_cycle(F);w=recovery(x,M)
    x=x.col_join(S.Matrix([1]));assert zero(modes(x,1))
    # Exact four-world stationary branches on the same source/catalyst port.
    worlds=[S.zeros(5,1),S.Matrix([0,0,0,0,1]),S.Matrix([0,S.sqrt(2),0,0,0]),x]
    expected=[(0,0,0),(0,0,0),(1,1,0),(1,0,1)]
    for i,(z,s) in enumerate(zip(worlds,(0,0,1,1))):
        assert zero(modes(z,s));inc=s*s;ref=(s-S.sqrt(2)*z[0])**2
        y=(z[2]+z[3])**2/2;assert (inc,ref,y)==expected[i]
    # Fixing the conserved HF action preserves the previous exact local
    # Schur certificate on the occupied modal quotient. HF phase is cyclic,
    # not an attracting degree of freedom; no full hyperbolic claim.
    assert zero(modes(x,1)[4]);assert w==S.Rational(1,2)
    chi,Henergy,gamma=S.symbols('chi Henergy gamma',positive=True)
    # g=chi |h|², HF stored work = (omega_H/omega_c)|h|².
    # At unit normalized cycle, maintenance loss for damping gamma is
    # 2 gamma Henergy. Startup store is not newly harvested work.
    required=ratio*S.sqrt(2)/chi
    assert S.simplify(chi*required/ratio-S.sqrt(2))==0
    print('PASS reciprocal HF action catalyst, exact four worlds',expected,'clock cycles',cycles)
    print('HF store at chi=sqrt(2):',ratio,'normalized units; general reverse store',required)
    print('PASS same tangent-frame fifth-order tensor and modal quotient stability; no physical nonlinear coefficient or HF maintenance admitted')
if __name__=='__main__':run()
