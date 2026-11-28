"""Independent source-shaped profile attempt, NOT Alpoge--Buckmaster data.
Paper Appendix C and Challenge.SimilarityResidual at ad53419.
Exact finite jets and one physical far-field recursion; no kernel receipt.
"""
import sympy as S
from itertools import product
from math import factorial, comb
from functools import lru_cache
import unittest

I=S.I; Q=S.Rational; N=4
zero=(0,0,0)
units=[tuple(int(i==j) for i in range(3)) for j in range(3)]


def plus(a,b):
    return tuple(x+y for x,y in zip(a,b))


def times(a,b):
    out={}
    for i,x in a.items():
        for j,y in b.items():
            k=plus(i,j)
            if sum(k)<=N:out[k]=out.get(k,0)+x*y
    return {k:S.expand(v) for k,v in out.items() if v!=0}


def shiftpoly(p,pt):
    out={}
    for e,c in p.items():
        for k in product(*(range(min(N,i)+1) for i in e)):
            if sum(k)>N:continue
            v=c*S.prod(comb(ej,kj)*pj**(ej-kj) for ej,kj,pj in zip(e,k,pt))
            out[k]=out.get(k,0)+v
    return out


@lru_cache(None)
def jet(m,pt,exponent,real_exp):
    # P=Im((x+iy)^m). Strip ONLY the common nonzero D^(-i omega)
    # at this point, AFTER differentiating the full complex power.
    p={(m-j,j,0):(-1)**((j-1)//2)*comb(m,j) for j in range(1,m+1,2)}
    D=1+sum(x*x for x in pt)
    d={units[i]:2*pt[i]/D for i in range(3)}
    d.update({plus(e,e):1/D for e in units})
    power={zero:S.Integer(1)};f={}
    for j in range(N+1):
        c=S.binomial(exponent,j).expand(func=True)
        for k,v in power.items():f[k]=f.get(k,0)+c*v
        power=times(power,d)
    a=times(shiftpoly(p,pt),f)
    return {k:S.expand(v*D**real_exp*S.prod(factorial(i) for i in k)) for k,v in a.items()}


def wjet(m,pt,omega,A,B):
    t=jet(m,pt,-Q(m,2)-I*omega,-Q(m,2))
    p=jet(m,pt,-Q(m-1,2)-I*omega,-Q(m-1,2))
    def w(j,k):
        v=0
        if j<2:
            v=A*(-1)**j*t.get(plus(k,units[1-j]),0)+B*p.get(plus(plus(k,units[j]),units[2]),0)
        else:
            v=-B*sum(p.get(plus(plus(k,e),e),0) for e in units[:2])
        return S.expand(v)
    return w


def curlconv(w):
    def d(i,j):
        return S.expand(sum(w(l,units[i])*w(j,units[l])+w(l,zero)*w(j,plus(units[i],units[l])) for l in range(3)))
    return [S.expand(d((i+1)%3,(i+2)%3)-d((i+2)%3,(i+1)%3)) for i in range(3)]


x,y,z=S.symbols('x y z',real=True)
xyz=(x,y,z); r2=x*x+y*y+z*z; D=1+r2; ez=S.Matrix([0,0,1]); Y=S.Matrix(xyz)

def simp(v):return v.applyfunc(S.simplify) if isinstance(v,S.MatrixBase) else S.simplify(v)
def curl(v):return S.Matrix([S.diff(v[2],y)-S.diff(v[1],z), S.diff(v[0],z)-S.diff(v[2],x), S.diff(v[1],x)-S.diff(v[0],y)])
def div(v):return S.simplify(sum(S.diff(v[i],xyz[i]) for i in range(3)))
def grad(f):return S.Matrix([S.diff(f,j) for j in xyz])
def lap(v):return v.applyfunc(lambda f:sum(S.diff(f,j,2) for j in xyz))


class Controls(unittest.TestCase):
    def test_source_symmetry_and_tail_phase(self):
        m=19; omega=S.symbols('omega',real=True)
        # P is odd under (x,y,z)->(x,-y,-z); axial vector e_z flips.
        P=S.im((x+I*y)**m).expand(complex=True)
        self.assertEqual(S.expand(P.subs(y,-y)+P),0)
        self.assertEqual(S.expand(sum(v*S.diff(P,v) for v in xyz)-m*P),0)
        # Exact azimuth/time phase characters for both wings.
        for a in (-1,1):
            self.assertEqual((-1)**(2-a),-1)
            self.assertEqual((-1)**a,-1)
        # leading tail drift, both curl orders reduce homogeneity by their order
        for order,alpha in [(1,-Q(m,2)-I*omega),(2,-Q(m-1,2)-I*omega)]:
            self.assertEqual(S.expand(I*omega+Q(1,2)+Q(1,2)*(m+2*alpha-order)),0)

    def test_entire_two_potential_family_rejected(self):
        A,B=S.symbols('A B'); w=S.symbols('w',real=True,positive=True)
        p=(Q(3,4),S.Integer(0),S.Integer(0))
        q=(Q(3,4),S.Integer(0),S.Integer(1))
        c=curlconv(wjet(19,p,w,A,B));d=curlconv(wjet(19,q,w,A,B))
        factor=Q(83226874893644824598016,1136868377216160297393798828125)
        self.assertEqual(S.expand(c[0]-factor*A*B*(w-9*I)*(46*w-1485*I)),0)
        pref=-Q(665814999149158596784128,302862043149743582494593171234930481)
        aa=82*w*w+1763*I*w+24149
        bb=-200*w**4-7388*I*w**3-35780*w*w-1734444*I*w-11810124
        self.assertEqual(S.expand(d[1]-pref*(aa*A*A+bb*B*B)),0)
        # For any real w>0, first equation forces AB=0. The real
        # coefficient of A² is strictly positive, imaginary of B² negative.
        self.assertTrue(S.re(aa).is_positive)
        self.assertTrue(S.im(bb).is_negative)
        # Hence even complex amplitudes A,B must both vanish. Adding any
        # time-independent mean cannot affect the second harmonic.

    def test_jet_against_direct_low_degree(self):
        # independent differentiation on a low-degree member of same formula
        m=3; p=(Q(3,4),S.Integer(0),S.Integer(1));w=S.Integer(2)
        a=jet(m,p,-Q(m,2)-I*w,-Q(m,2))
        f=(3*x*x*y-y**3)*D**(-Q(m,2)-I*w)
        at=dict(zip(xyz,p));Dp=D.subs(at)
        for k in [(0,1,0),(1,1,0),(0,1,2),(2,1,1)]:
            v=f
            for j,n in zip(xyz,k):v=S.diff(v,j,n)
            v=S.simplify(S.expand_log((v.subs(at)*Dp**(I*w)).rewrite(S.exp),force=True))
            self.assertEqual(S.simplify(v-a.get(k,0)),0)

    def test_original_adjoint_differential_identity(self):
        # Local formal L² adjoint, not a verified global adjoint field.
        w=S.Matrix([x,-y,0]);v=S.Matrix([x*y,y*z,z*x]);a=S.Matrix([z*y,x*z,x*y])
        L=v/2+v.jacobian(xyz)*Y/2-lap(v)+v.jacobian(xyz)*w+w.jacobian(xyz)*v
        Lstar=-a-a.jacobian(xyz)*Y/2-lap(a)-a.jacobian(xyz)*w+w.jacobian(xyz).T*a
        flux=Y*(a.dot(v))/2+w*(a.dot(v))
        flux+=S.Matrix([sum(v[i]*S.diff(a[i],j)-a[i]*S.diff(v[i],j) for i in range(3)) for j in xyz])
        self.assertEqual(S.expand(a.dot(L)-Lstar.dot(v)-div(flux)),0)

    def test_mean_tail_pressure_and_next_velocity(self):
        r=S.sqrt(r2); h=z/r
        U=z*S.Matrix([-y,x,0])/r**3
        pressure=(-Q(1,15)-Q(4,21)*S.legendre(2,h)-Q(8,105)*S.legendre(4,h))/r**2
        adv=U.jacobian(xyz)*U
        self.assertEqual(div(U),0)
        self.assertEqual(S.simplify(div(grad(pressure))+div(adv)),0)
        V=simp(-lap(U)+adv+grad(pressure))
        self.assertEqual(div(V),0)
        self.assertEqual(simp(V.jacobian(xyz)*Y+3*V),S.zeros(3,1))
        self.assertEqual(simp(curl(Y.cross(V))-V),S.zeros(3,1))
        # For r^-3 correction, similarity drift equals -V, cancelling
        # the entire r^-3 physical momentum coefficient, pressure included.
        self.assertEqual(simp(V/2+V.jacobian(xyz)*Y/2-lap(U)+adv+grad(pressure)),S.zeros(3,1))


if __name__=='__main__':unittest.main()
