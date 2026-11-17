"""Exact restricted 4x4 tangential Maxwell planar layer transfer.

exp(-iωt), exp(ikx x), ky=0, μ scalar, eps_xz=eps_yz=0.
State [Ex,Ey,Hx,Hy].  This is NOT the full 3D retarded dyadic Green,
nor measured ground/ionosphere electrodynamics.
"""
import sympy as S
I=S.I

def tangential_generator(omega,kx,mu,epsxx,epsyy,epszz,epsxy=0,epsyx=0):
    w=S.sympify(omega);k=S.sympify(kx);m=S.sympify(mu)
    exx,eyy,ezz,exy,eyx=map(S.sympify,
                           (epsxx,epsyy,epszz,epsxy,epsyx))
    if w==0 or m==0 or ezz==0:
        raise ValueError("omega, mu and epszz must be nonzero")
    # Maxwell: Hz=k Ey/(ωμ), Ez=-k Hy/(ω epszz)
    # curl E=iωμH, curl H=-iω eps E.
    return S.Matrix([
        [0,0,0,I*(w*m-k*k/(w*ezz))],
        [0,0,-I*w*m,0],
        [-I*w*eyx,I*(k*k/(w*m)-w*eyy),0,0],
        [I*w*exx,I*w*exy,0,0]])

def transfer_midpoint_z(generator,thickness):
    """Exact rational Cayley discretization of exp(M d), NOT exp(M d)."""
    d=S.sympify(thickness);ident=S.eye(4)
    return (ident-d*generator/2).inv()*(ident+d*generator/2)

def three_layer_tangential_transfer(generators,thicknesses):
    if len(generators)!=3 or len(thicknesses)!=3:
        raise ValueError("three layers expected")
    out=S.eye(4)
    for M,d in zip(generators,thicknesses):
        out=transfer_midpoint_z(M,d)*out
    return out
