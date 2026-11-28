"""BL: rational majorants for a quantitative tail energy certificate.
See BL roadmap for finite-dimensional energy perturbation inequalities.
Bound entries and their coordinate derivatives, not samples; use exact Fraction.
"""
from fractions import Fraction as F
import json,sys
from pathlib import Path

# All nonnegative majorants rounded upwards to keep rational sizes bounded.
SCALE=10**40

def up(x):
    x=F(x);return F(-((-x*SCALE).__floor__()),SCALE)

class B:
    def __init__(self,v,d=0,dd=0):self.v,self.d,self.dd=map(up,(v,d,dd))
    @staticmethod
    def of(x):return x if isinstance(x,B) else B(abs(F(x)))
    def __add__(self,y):
        y=B.of(y);return B(self.v+y.v,self.d+y.d,self.dd+y.dd)
    __radd__=__add__
    __sub__=__add__
    __rsub__=__add__
    def __mul__(self,y):
        y=B.of(y);return B(self.v*y.v,self.d*y.v+self.v*y.d,self.dd*y.v+2*self.d*y.d+self.v*y.dd)
    __rmul__=__mul__
    def __pow__(self,n):
        a=B(1)
        for _ in range(n):a=a*self
        return a
    def inv(self,low):
        low=F(low);assert low>0
        return B(1/low,self.d/low**2,self.dd/low**2+2*self.d**2/low**3)
    def invsqrt_ge_one(self):return B(1,self.d/2,self.dd/2+3*self.d**2/4)
    def diff(self):return B(self.d,self.dd) # first derivative only; subsequent use needs at most one derivative
    def cap(self,v):return B(min(self.v,F(v)),self.d,self.dd)


def envelope(d,c,cs):
    # All component bounds relative to gamma frame e_i=h0 delta/2 partial_i,
    # e_y=partial_y. Derivative majorants are ordinary x,y derivatives.
    h=F(4,5);j=F(6,5);eps=F(1,40)
    t=B(1,2,2);delta=B(d,2,2);x=B(1,1);F0=F(2,1)/h*(1+t)
    den=delta**4+F0**2*t
    assert d<=F(1,10) # t>=.9, hence den>=16
    deni=den.inv(16)
    # max |W_i| <= delta^4 + 3 F^2 + 2F delta^2; derivative bound via expression.
    W=delta**4+3*F0**2*x**2+2*F0*delta**2*x
    ah=eps*h*3*(F0*delta+(F(4,1)/h*delta+4*F0)*x*x)*W*deni**2
    S=1+3*delta**4*ah**2;al=S.invsqrt_ge_one()
    H=1+delta**4*ah**2;Hi=1+delta**4*ah**2*S.inv(1)
    # gam3 component <= 2h; max-entry summations over three indices.
    gam=B(2*h,2*h)
    da=h*delta*al.diff()*F(1,2)
    T=h*delta*ah.diff()*F(1,2)+3*gam*ah+2*h*x*ah
    M=al*(T+6*delta**4*ah**2*T)
    def tf(A):return A+3*Hi*A*H
    MT=tf(M)
    C0=j*tf(da*ah)+j*al**2*(2+3*delta**4*ah**2)*MT*F(1,2)
    C1=F(3,2)*j*al**2*MT
    b=B(1,F(3,5),1);b2=b**2
    # f is y^2(L-y)^2(L-2y)/L^3, L in (1,1.4).
    y=B(F(7,5),1);f=(y**2*y**2*B(F(7,5),2)).cap(F(1,8))
    lift=1+(b+B(1))*al
    lift=lift.cap(1)
    # radial s=t/(.1+t)=1-.1/(.1+t), derivative estimates on t>=.9.
    radial=(1+F(1,10)*(t+F(1,10)).inv(1)).cap(1)
    angular=B(2,6,6);fourier=B(1,10,100)
    # endpoint p values/derivatives from products, L>=1.
    poly=(y**2*y**3*F(1,2)).cap(F(1,20))
    def what(co):
        a=sum(abs(F(float(v))) for v in co[:180]);b0=sum(abs(F(float(v))) for v in co[180:])
        return angular*radial**3*(a*lift*fourier+b0*poly)*(1+10*t).inv(10)
    # actual m=2 projection: (1-t²)[(1-t²)what(c)+t²what(cs)].
    taper=delta*(1+t);wh=taper*(taper*what(c)+t**2*what(cs))
    w=delta**2*wh;u=(1+w).inv(F(9,10))
    # u lower bound 1+w>=.949 from BH/BK; .9 is weaker.
    # compactified metric difference and D, max entries.
    aa=ah**2;A=(b2+B(1)).cap(F(9,25))*(3*delta**2*aa*al**2*(1+al).inv(1)+al*delta**2*aa)+delta**2*aa+ah
    E=u*(u+1)*wh*b2+u**2*(A+f*(C0+delta**2*u*wh*C1))
    Dh=u**3*f*C1
    # covariant derivative in reference frame; max |Gamma0|<=2,
    # four terms per contraction, two contractions, |ell|<=.8.
    # m=-1+(al+1/al)/u_wall; al+1/al-2=(sqrt S-1)^2/sqrt S.
    m=9*delta.v**8*ah.v**4/4+3*w.v
    assert S.v<=2 # al+1/al <=3 follows from S<=2 and al<=1
    return [d*d*E.v,d*d*(E.d+18*E.v),d*d*Dh.v,d*d*(Dh.d+18*Dh.v),m]


def certify(c,cs):
    e=F(1,100000)
    # Norm perturbation to energy matrix, all entries measured in reference frame.
    # Exact inequalities are derived in BL roadmap; conservative constants.
    M=6-800*e;V=F(342,25)-6000*e # 24-6*(1+2*.6^2)=13.68
    ell=F(36,5)+10000*e
    schur=V-ell**2/(4*M)
    assert M>0 and schur>11
    print('rational energy perturbation threshold',float(e),'M lower',float(M),'Schur lower',float(schur),flush=True)
    for k in range(1,12):
        d=F(1,10**k);vals=envelope(d,c,cs)
        print('delta <=',float(d),'five majorants',[float(v) for v in vals],flush=True)
        if max(vals)<=e:
            print('CERTIFIED quantitative collar: delta <=',d,'equivalently |x|^2 >=',1-d,flush=True);return
    raise AssertionError('tail majorant failed')

if __name__=='__main__':
    c=json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]);cs=json.loads(Path(sys.argv[2]).read_text());assert len(c)==len(cs)==252
    certify(c,cs)
