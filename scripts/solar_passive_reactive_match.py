"""Exact passive Foster matching at both occupied midpoint frequencies.
Broader source-access class only; not an original remote hardware topology.
"""
import sympy as S
from solar_whole_boundary import candidate
from solar_same_port_boundary import replay

def match(f,r=1):
    r=S.Rational(r);assert r>=0
    l=1+r
    # Source onsite oscillator x,v, additional passive lossless q,p branch.
    # Z_add(s)=7s/(s^2+16); positive storage 7(p^2+16q^2)/2.
    A=S.Matrix([[0,1,0,0],[-1,-(1+r+l),0,-7],[0,0,0,1],[0,1,-16,0]])
    G=S.diag(1,1,112,7);I=S.eye(4);L=(I-A/2).inv();T=L*(I+A/2)
    j=S.Matrix([[0,1,0,0]]);O=j*L
    assert G-T.T*G*T==2*(1+r+l)*O.T*O
    assert S.Matrix.vstack(*[O*T**k for k in range(4)]).rank()==4
    b=S.zeros(4,1)
    for force in f:b=T*b+L*S.Matrix([0,force,0,0])
    x=(I-T**len(f)).inv()*b;start=x;N=Y=H=inc=ref=0
    for force in f:
        y=T*x+L*S.Matrix([0,force,0,0]);v=(x[1]+y[1])/2
        assert v==force/(2*(1+r))
        assert ((y.T*G*y-x.T*G*x)[0])/2==force*v-(1+r+l)*v*v
        N+=force*v-r*v*v;Y+=l*v*v;H+=v*v
        if r:
            a=force/(2*S.sqrt(r));o=a-S.sqrt(r)*v
            assert S.simplify(a*a-o*o-force*v+r*v*v)==0
            inc+=a*a;ref+=o*o
        x=y
    assert x==start and N==Y+H
    cap=sum(a*a for a in f)/(4*(1+r));assert Y==cap
    if r:assert N==inc-ref
    return dict(output=Y,natural=N,intrinsic=H,incident=inc,reflected=ref,cap=cap)

def run():
    w=S.symbols('w',real=True,nonzero=True)
    residual=S.factor(w-1/w+7*w/(16-w*w))
    assert S.simplify(residual+(w**4-24*w**2+16)/(w*(16-w*w)))==0
    for omega in (2*(S.sqrt(2)-1),2*(S.sqrt(2)+1)):
        assert S.simplify(residual.subs(w,omega))==0
    # Coarse upper for all returned, internally funded trajectories with
    # unchanged source damping and extra nonnegative losses.
    v,F,r=S.symbols('v F r',real=True);assert S.cancel(F*v-(1+r)*v*v-F*F/(4*(1+r))+(1+r)*(v-F/(2*(1+r)))**2)==0
    z,f,_=candidate();fixed=match(f,0);wave=match(f,1);off=match([0]*8,1)
    assert fixed['output']==1 and wave['output']==S.Rational(1,2) and off['output']==0
    active=replay(z,f,1,1);assert active['output']<wave['output']
    print('PASS exact two-harmonic passive match',fixed,wave,'active ideal',float(active['output']))
    print('PASS Schur by positive storage and four-step observability; all broader eligible active gains excluded by common cap')
if __name__=='__main__':run()
