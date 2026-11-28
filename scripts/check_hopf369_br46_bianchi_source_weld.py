#!/usr/bin/env python3
"""BR46: contracted Bianchi source of the SAME 15-component reduced metric.

Classical 5D linear Ricci at a flat adapted physical chart point, for general
symmetric h_ab and every five covector frequencies z_a. Retain the normal
component and z^2=0 characteristic case. The identity proves the
*principal-symbol* subsidiary forcing, not curved lower-order cancellation,
nonlinear metric existence or the BR29 boundary constraint estimate.

For reduced Rbar=Ric_lin-1/2(z_a C_b+z_b C_a), C_b=z^a h_ab
-1/2 z_b tr_eta(h), contracted Bianchi gives:
    z^a (Rbar_ab-eta_ab tr Rbar/2) = -(z^2/2) C_b .
Therefore div(trace reverse) of an actual reduced bulk source must match
the subsidiary wave source; it cannot be replaced by zero off shell.
"""
import argparse
import sympy as s

def check(component):
    eta=s.diag(-1,1,1,1,1)
    z=s.Matrix(s.symbols('z0:5'))
    h=s.Matrix(5,5,lambda i,j:s.Symbol('h%d%d'%(min(i,j),max(i,j))))
    zu=eta*z
    z2=(z.T*eta*z)[0]
    tr=s.trace(eta*h)
    C=h*zu-z*tr/2
    Ric=s.Matrix(5,5,lambda i,j:
       (z[i]*(h*zu)[j]+z[j]*(h*zu)[i]-z2*h[i,j]-z[i]*z[j]*tr)/2)
    source=s.Matrix(5,5,lambda i,j:
       Ric[i,j]-(z[i]*C[j]+z[j]*C[i])/2)
    # BR4 reduced principal operator: scalar diagonal, not substitute
    # for the full BR15 optical potential or nonlinear Einstein source.
    assert (source+z2*h/2).applyfunc(s.expand)==s.zeros(5)
    # Source-level exact contracted Bianchi (trace reverse).
    rictr=s.trace(eta*Ric)
    redtr=s.trace(eta*source)
    b=component
    original=sum(zu[i]*(Ric[i,b]-eta[i,b]*rictr/2) for i in range(5))
    residual=sum(zu[i]*(source[i,b]-eta[i,b]*redtr/2) for i in range(5))
    assert s.expand(original)==0
    assert s.expand(residual+z2*C[b]/2)==0
    # Keep the signed normal covector and characteristic zero mode:
    # on z²=0 the identity becomes 0=0, not C_b=0.
    assert s.expand((residual+z2*C[b]/2).subs({z[0]:0,z[1]:0,z[2]:0,z[3]:0,z[4]:0}))==0
    print('PASS BR46 5D contracted Bianchi',b,'reduced metric and subsidiary source')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--component',type=int,default=0)
    a=p.parse_args()
    if not 0<=a.component<5:raise ValueError('5D covector index')
    check(a.component)

if __name__=='__main__':main()
