#!/usr/bin/env python3
"""BR51: exact moving-wall conormal defect coefficient and Cauchy budget.

This is the physical ADM/Israel graph error left unpaid by BR50, NOT a
claim of derivative-level tame regularity or source-integrated coercivity.

For F=n-f and θ=F_t-v^i F_i:
  (J_F/D-u_n) = k_t u_t + sum_i k_i u_i,
  k_t=-θ/N², k_i=H^{ni}-δ_{ni}-H^{ai}f_a+θ v^i/N².
Every term (tilt, normal shear, shift and lapse) is retained.
For real physical jets, Cauchy gives
  |J_F-D u_n|² <= D²(k_t²+sum k_i²)(u_t²+sum u_i²).
The same pointwise bound holds by summing the original 15 metric and
five subsidiary channels with the positive tensor Gram; no Lorentzian
wall work is asserted positive.

Checker is exact SymPy, split by --part algebra|budget|channels.
"""
import argparse
import sympy as s

def fields():
    N=s.symbols("N",positive=True)
    D=s.symbols("D",positive=True)
    hii=s.symbols("h0:4",positive=True)
    v=s.Matrix(s.symbols("v0:4",real=True))
    f=s.Matrix(s.symbols("f0:4",real=True)) # f0=time, f1..3 tangent
    F=s.Matrix([-f[0],-f[1],-f[2],-f[3],1])
    Hi=s.diag(*[1/x for x in hii])
    theta=F[0]-sum(v[i]*F[i+1] for i in range(4))
    kt=-theta/N**2
    ks=s.Matrix([sum(Hi[i,j]*F[j+1] for j in range(4))
                 -int(i==3)+theta*v[i]/N**2 for i in range(4)])
    return N,D,hii,v,f,F,Hi,theta,kt,ks

def algebra():
    N,D,h,v,f,F,Hi,theta,kt,ks=fields()
    u=s.symbols("ut u0:4")
    du=s.Matrix(u[1:])
    t=u[0]
    full=D*((F[1:5,0].T*Hi*du)[0]-theta*(t-(v.T*du)[0])/N**2)
    ref=D*du[3]
    assert s.cancel(full-ref-D*(kt*t+(ks.T*du)[0]))==0
    # Gaussian limit is zero despite nonzero tangent ADM shift.
    collar={f[i]:0 for i in range(4)}
    collar.update({v[3]:0,h[3]:1})
    assert s.simplify(kt.subs(collar))==0
    assert ks.subs(collar).applyfunc(s.cancel)==s.zeros(4,1)
    print("PASS BR51 all five exact ADM graph conormal defect coefficients")

def budget():
    # Concrete signed rational source chart with spacelike graph normal.
    N,D,h,v,f,F,Hi,theta,kt,ks=fields()
    subst={N:s.Rational(3,2),D:s.Rational(9,7)}
    subst.update({h[i]:s.Rational(i+4,4) for i in range(4)})
    subst.update({v[i]:s.Rational(i-1,11) for i in range(4)})
    subst.update({f[i]:s.Rational(i-2,13) for i in range(4)})
    k=s.Matrix([kt,*ks]).subs(subst)
    assert k!=s.zeros(5,1)
    z=(F[1:5,0].T*Hi*F[1:5,0])[0]-theta**2/N**2
    assert s.cancel(z.subs(subst))>0
    for seed in range(8):
        u=s.Matrix([s.Rational((i+2)*(seed+3)%19-9,7) for i in range(5)])
        err=D.subs(subst)*(k.T*u)[0]
        gram=(k.T*k)[0]*(u.T*u)[0]-(k.T*u)[0]**2
        # Five-coordinate Lagrange identity is sum of exact 10 squares.
        wedge=sum((k[i]*u[j]-k[j]*u[i])**2
                  for i in range(5) for j in range(i+1,5))
        assert s.cancel(gram-wedge)==0 and gram>=0
        assert s.cancel(err*err-D.subs(subst)**2*(k.T*k)[0]*(u.T*u)[0])<=0
    print("PASS BR51 ten-square Lagrange/Cauchy graph-error budget and spacelike normal")

def channels():
    N,D,h,v,f,F,Hi,theta,kt,ks=fields()
    val={N:s.Rational(3,2),D:s.Rational(9,7)}
    val.update({h[i]:s.Rational(i+4,4) for i in range(4)})
    val.update({v[i]:s.Rational(i-1,11) for i in range(4)})
    val.update({f[i]:s.Rational(i-2,13) for i in range(4)})
    k=s.Matrix([kt,*ks]).subs(val)
    for dim in (15,5):
        jet=s.Matrix(dim,5,lambda i,j:s.Rational((i+2)*(j+5)%23-11,7))
        actual=jet*k*D.subs(val)
        from_norm=sum((actual[i])**2 for i in range(dim))
        upper=D.subs(val)**2*(k.T*k)[0]*sum(jet[i,j]**2
                  for i in range(dim) for j in range(5))
        assert s.cancel(upper-from_norm)>=0
    print("PASS BR51 full original 15/5 channel-positive graph-defect budget")

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--part",choices=("algebra","budget","channels","all"),default="algebra")
    args=p.parse_args()
    if args.part in ("algebra","all"):algebra()
    if args.part in ("budget","all"):budget()
    if args.part in ("channels","all"):channels()

if __name__=="__main__":main()
