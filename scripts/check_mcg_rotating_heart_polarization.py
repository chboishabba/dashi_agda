#!/usr/bin/env python3
"""Rotating cardiac vector-dipole analytical fixture, not a mechanical rotor.

Cardiac excitation may yield rotating/translating equivalent current dipoles.
The simple rotating moment below is an explicit toy source, not an MRI/MCG
anatomical inversion or evidence of disk rotation / gravitomagnetism.
"""
import sympy as s

def check():
    w,t,r,m0,mu=s.symbols("w t r m0 mu",positive=True,real=True)
    n=s.Matrix([0,0,1])
    D=3*n*n.T-s.eye(3)
    m=s.Matrix([m0*s.cos(w*t),m0*s.sin(w*t),0])
    B=mu/(4*s.pi*r**3)*D*m
    assert s.simplify(B[0]**2+B[1]**2-(mu*m0/(4*s.pi*r**3))**2)==0
    co=s.Matrix([s.cos(w*t),s.sin(w*t),0])
    y=s.trigsimp((co.T*B)[0])
    assert s.simplify(y+mu*m0/(4*s.pi*r**3))==0
    assert s.simplify(B[0].subs(t,s.pi/(2*w)))==0
    counter=s.Matrix([s.cos(w*t),-s.sin(w*t),0])
    yc=s.trigsimp((counter.T*B)[0])
    assert s.simplify(yc+mu*m0*s.cos(2*w*t)/(4*s.pi*r**3))==0
    print("PASS rotating cardiac moment, two-polarization demodulation and r^-3")
    print("OPEN human anatomical current-source source and measured polarisation")

if __name__=="__main__":check()
