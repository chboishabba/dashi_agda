#!/usr/bin/env python3
"""Exact 3D dipole and sensor-axis geometry, not a tissue or experimental model.

Mathematical physics source: classical magnetostatics; repository owner:
DiamondMCGFiniteBridgeExact (separate periodic Fourier representation).
"""
import sympy as s

def same(a,b,label):
    diff=a-b
    if isinstance(diff,s.MatrixBase):
        assert all(s.simplify(v)==0 for v in diff),label
    else:
        assert s.simplify(diff)==0,label

def main():
    x,y,z,mx,my,mz=s.symbols('x y z mx my mz',real=True)
    R=s.Matrix([x,y,z]);m=s.Matrix([mx,my,mz]);q=R.dot(R)
    # B/(mu0/4pi) = (3 (m dot R) R - |R|² m)/|R|^5.
    B=(3*m.dot(R)*R-q*m)/q**s.Rational(5,2)
    r=s.symbols('r',positive=True)
    same(B.subs({mx:0,my:0,mz:1,x:0,y:0,z:r}),
         s.Matrix([0,0,2/r**3]),'axial field')
    same(B.subs({mx:1,my:0,mz:0,x:0,y:0,z:r}),
         s.Matrix([-1/r**3,0,0]),'equatorial field')
    U=s.Matrix([[0,-1,0],[1,0,0],[0,0,1]])
    transformed=B.subs({x:-y,y:x,mx:-my,my:mx},simultaneous=True)
    same(transformed,U*B,'proper-rotation covariance')
    M=3*R*R.T-q*s.eye(3)
    same(M,M.T,'dipole tensor symmetry')
    same(s.trace(M),0,'dipole tensor trace-free')
    n=s.Matrix([0,0,1]);tangent=s.Matrix([1,0,0])
    tilted=B.subs({mx:1,my:0,mz:0,x:0,y:0,z:r})
    same(n.dot(tilted),0,'axial readout null for orthogonal moment')
    same(tangent.dot(tilted),-1/r**3,'transverse readout recovers signal')
    # First prove for positive source-observer separation d; substitute
    # d=r-a only in the stated physical domain r>a>0.
    a=s.symbols('a',positive=True)
    d=s.symbols('d',positive=True)
    axial=B.subs({mx:0,my:0,mz:1,x:0,y:0,z:d})
    same(axial,s.Matrix([0,0,2/d**3]),'positive-axis dipole')
    pair=(axial.subs(d,r-a)+axial.subs(d,r+a))/2
    same(pair,s.Matrix([0,0,(r-a)**-3+(r+a)**-3]),
         '3D-to-finite-pair axial weld under r>a')
    print('PASS 3D dipole tensor, rotation, sensor-axis null and axial pair')
    print('OPEN tissue currents, source support, experimental orientation/calibration')

if __name__=='__main__':main()
