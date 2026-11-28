#!/usr/bin/env python3
"""Original E4/E6/Delta/j formal Euler differential jet weld.

Finite formal coefficients and exact symbolic differential-algebra checks.
This is not a Bishop derivative theorem or a CM root proof.
"""
import argparse
import json
from sympy import symbols, expand

def mul(a,b,N):
    out=[0]*(N+1)
    for i,x in enumerate(a[:N+1]):
        if not x: continue
        for j,y in enumerate(b[:N+1-i]):
            if y: out[i+j]+=x*y
    return out

def sub(a,b): return [x-y for x,y in zip(a,b)]
def scale(a,k): return [k*x for x in a]
def deriv(a,offset=0): return [(i+offset)*x for i,x in enumerate(a)]
def series_div(a,b,N):
    assert b[0] == 1
    z=[]
    for n in range(N+1):
        z.append(a[n]-sum(z[k]*b[n-k] for k in range(n)))
    return z

def test_coefficients(N):
    M=N+2
    sigma1=[0]*(M+1);sigma3=sigma1.copy();sigma5=sigma1.copy()
    for d in range(1,M+1):
        for k in range(d,M+1,d):
            sigma1[k]+=d;sigma3[k]+=d**3;sigma5[k]+=d**5
    e2=[1]+[-24*sigma1[k] for k in range(1,M+1)]
    e4=[1]+[240*sigma3[k] for k in range(1,M+1)]
    e6=[1]+[-504*sigma5[k] for k in range(1,M+1)]
    de2=deriv(e2);de4=deriv(e4);de6=deriv(e6)
    for name,lhs,rhs in [
        ('Ramanujan-E2',scale(de2,12),sub(mul(e2,e2,M),e4)),
        ('Ramanujan-E4',scale(de4,3),sub(mul(e2,e4,M),e6)),
        ('Ramanujan-E6',scale(de6,2),sub(mul(e2,e6,M),mul(e4,e4,M)))]:
        assert lhs[:N+1]==rhs[:N+1],name
    cube=mul(mul(e4,e4,M),e4,M)
    square=mul(e6,e6,M)
    delta_num=sub(cube,square)
    assert delta_num[0]==0
    assert all(x%1728==0 for x in delta_num[:N+2])
    delta=[x//1728 for x in delta_num]
    assert delta[1]==1
    # Delta=q D, j=q^-1 J, where J is the original regularized j.
    D=delta[1:N+2];J=series_div(cube[:N+1],D,N)
    e6j=mul(e6,J,N)
    dj=deriv(J,-1);d2j=deriv(dj,-1)
    # Cleared by q: X Dj=-j Y.
    assert mul(e4,dj,N)[:N+1]==scale(e6j,-1)[:N+1]
    # Cleared by q: 6 X² D²j=j (3 X³+3 Y² -Y U), U=3D E4.
    xsq=mul(e4,e4,N);xcube=cube[:N+1];ysq=square[:N+1]
    u=scale(de4,3);yu=mul(e6,u,N)
    s=[3*xcube[k]+3*ysq[k]-yu[k] for k in range(N+1)]
    assert scale(mul(xsq,d2j,N),6)==mul(J,s,N)
    assert deriv(delta)[:N+1]==mul(e2,delta,M)[:N+1]
    return {'coefficient_degree':N,'ramanujan_identities':3*(N+1),
            'first_jet_coefficients':N+1,'second_jet_coefficients':N+1,
            'discriminant_coefficients':N+1,'j_regular_constant':J[0],
            'j_regular_linear':J[1]}

def symbolic():
    X,Y,E,K,D,DX,DY,Dd,Dj,D2j,U=symbols('X Y E K D DX DY Dd Dj D2j U')
    product=Dj*D+K*Dd-3*X**2*DX
    delta_flow=Dd-E*D
    e4=3*DX-E*X+Y
    quotient=K*D-X**3
    cleared=D*(X*Dj+K*Y)
    assert expand(cleared-(X*product-X*K*delta_flow+X**3*e4-(E*X-Y)*quotient))==0
    first=X*Dj+K*Y
    first_derivative=DX*Dj+X*D2j+Dj*Y+K*DY
    e6=2*DY-E*Y+X**2
    u=U-3*DX
    second=6*X**2*D2j-K*(3*X**3+3*Y**2-Y*U)
    assert expand(second-(6*X*first_derivative-6*(DX+Y)*first
                   -3*X*K*e6+3*K*Y*e4+K*Y*u))==0
    return {'first_cleared_ring_identity':True,'second_cleared_ring_identity':True,
            'positive_denominator_cancellation_only':'Delta != 0','nonzero_X_required':False}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--degree',type=int,default=256);a=p.parse_args()
    assert 2<=a.degree<=512
    print(json.dumps({'symbolic':symbolic(),'formal_q':test_coefficients(a.degree)},sort_keys=True))
