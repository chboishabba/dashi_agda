"""P0 conditional coupled radion/material and shielding constructions.
Natural units, canonically normalized scalar and material fluctuation.
Not a microscopic coupling derivation or physical gravity device.
Donors: check_kk_radion_reduced_action, check_kk_radion_spherical_match,
check_sc_driven_order_parameter_energy, GRQFTNegativeActiveStressRepulsionRouteExact.
"""
import sympy as s

def exact():
    k,m,h,c=s.symbols("k m h c", positive=True)
    lam,alpha,beta,J,T=s.symbols("lambda alpha beta J T", real=True)
    # Quadratic static energy in scalar and material amplitude, one Fourier mode.
    A=k*k+m*m
    B=c*c*k*k+h*h
    K=s.Matrix([[A,lam],[lam,B]])
    source=s.Matrix([alpha*T,J])
    D=A*B-lam**2
    response=K.adjugate()*source/D
    assert all(s.factor(v)==0 for v in K*response-source)
    assert s.factor(response[0]-(alpha*T-lam*J/B)/(A-lam**2/B))==0
    assert s.factor(response[0].subs(lam,0)-alpha*T/A)==0
    # Positive Hessian when D>0; mixed coupling softens static scalar mode.
    x,y=s.symbols("x y",real=True)
    energy=(s.Matrix([x,y]).T*K*s.Matrix([x,y]))[0]/2
    assert s.expand(energy-B*(y+lam*x/B)**2/2-D*x*x/(2*B))==0
    # Physical conformal metric, g_J=exp(2 beta phi) g_E.
    # Linear weak-field potential correction beta*phi; acceleration -grad.
    X=s.symbols("X",real=True)
    phi=s.Function("phi")(X)
    Psi=s.Function("Psi")(X)
    assert s.diff(Psi+beta*phi,X)==s.diff(Psi,X)+beta*s.diff(phi,X)
    target=s.symbols("target",real=True)
    # Reverse-solve a specified scalar amplitude, with material source port J.
    Jstar=(alpha*T*B-D*target)/lam
    assert s.factor(response[0].subs(J,Jstar)-target)==0
    # Finite 1D shielding proxy: a massive scalar in a slab with
    # Dirichlet incident amplitude and matched outgoing impedance z>=0.
    # This is NOT static tensor gravity shielding or an Earth solution.
    mu,d,z,u=s.symbols("mu d z u",positive=True)
    xx=s.symbols("xx",real=True)
    denom=s.cosh(mu*d)+z*s.sinh(mu*d)/mu
    field=u*(s.cosh(mu*(d-xx))+z*s.sinh(mu*(d-xx))/mu)/denom
    assert s.simplify(s.diff(field,xx,2)-mu**2*field)==0
    assert s.simplify(field.subs(xx,0)-u)==0
    assert s.simplify((s.diff(field,xx)+z*field).subs(xx,d))==0
    assert s.simplify(field.subs(xx,d)-u/denom)==0
    # Passive stable scalar attenuation requires the actual incident field
    # to couple to this channel; ordinary tensor gravity is unchanged here.
    print("PASS conditional mixed susceptibility, inverse source, Hessian and scalar slab transfer")
    print("OPEN microscopic lambda, conformal beta, conserved stress, tensor shielding and SI calibration")

if __name__=="__main__": exact()
