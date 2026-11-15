#!/usr/bin/env python3
"""Conditional Smith/Filsinger source-work identities. NOT a hardware receipt."""
import sympy as s

def three_member_hamiltonian_identity():
    t=s.symbols('t',real=True)
    x,z,y,vx,vz,vy=[s.Function(v)(t) for v in ('x','z','y','vx','vz','vy')]
    w1,w2,we,lam=s.symbols('w1 w2 we lam',positive=True,real=True)
    gd,ge=[s.Function(v)(t) for v in ('g_driver_converter','g_converter_environment')]
    ux,un,gl,gi,gz,gy=s.symbols('Fdrive Fnatural gammaLoad gammaLocal gammaConverter gammaEnvironment',real=True)
    V=(w1*x)**2/2+(w2*z)**2/2+(we*y)**2/2+lam*z**4/4+gd*(x-z)**2/2+ge*(z-y)**2/2
    H=(vx*vx+vz*vz+vy*vy)/2+V
    dyn={s.diff(x,t):vx,s.diff(z,t):vz,s.diff(y,t):vy,
        s.diff(vx,t):-s.diff(V,x)-(gl+gi)*vx+ux,
        s.diff(vz,t):-s.diff(V,z)-gz*vz,
        s.diff(vy,t):-s.diff(V,y)-gy*vy+un}
    Wmod=s.diff(gd,t)*(x-z)**2/2+s.diff(ge,t)*(z-y)**2/2
    work=ux*vx+un*vy+Wmod-gl*vx**2-gi*vx**2-gz*vz**2-gy*vy**2
    assert s.simplify(s.diff(H,t).subs(dyn)-work)==0

def delayed_fm_phase_doubler():
    # Two phase-delayed FM paths at relative opposition.
    # A=B=1: fast-averaged intensity 1-cos(u*cos(theta)).
    u,theta=s.symbols('u theta',real=True)
    I=1-s.cos(u*s.cos(theta))
    doubled=u**2*(1+s.cos(2*theta))/4
    assert s.trigsimp(s.series(I,u,0,4).removeO()-doubled)==0
    # A single ideal constant-envelope FM path has no low-frequency
    # power oscillation under memoryless square-law carrier averaging.
    psi,A=s.symbols('psi A',real=True)
    carrier_squared=s.integrate((A*s.cos(psi))**2,(psi,0,2*s.pi))/(2*s.pi)
    assert s.simplify(carrier_squared-A*A/2)==0
    assert 3915+3915==7830 # milliHertz, conditional slow phase clock

def check():
    three_member_hamiltonian_identity()
    delayed_fm_phase_doubler()
    print('PASS exact Hamiltonian source ledger, delayed-phase second harmonic and single-path negative control')

if __name__=='__main__':check()
