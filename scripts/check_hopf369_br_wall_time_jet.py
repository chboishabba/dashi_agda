#!/usr/bin/env python3
"""BR20/24 normal force time corner: mean lapse acceleration jet control."""
import sympy as s

def run():
    e=s.symbols('e',real=True); N=s.symbols('N',positive=True); j=s.symbols('j')
    K=s.Matrix(3,3,lambda a,b:s.Symbol('k%d%d'%(min(a,b),max(a,b))))
    A=s.Matrix(3,3,lambda a,b:s.Symbol('a%d%d'%(min(a,b),max(a,b))))
    Ay=s.Matrix(3,3,lambda a,b:s.Symbol('ay%d%d'%(min(a,b),max(a,b))))
    z,zy,B,By,ell=s.symbols('z zy B By ell',real=True)
    c=s.Matrix(s.symbols('c0:3')); divc=s.Symbol('divc'); dlogN=s.Matrix(s.symbols('l0:3'))
    # Gaussian spatial initial chart; first variation at t²/2.
    # gamma(t)=gamma+e A_full, N(t)=N+e B. A_nn=z, A_na=c.
    # d_y log volume derivative = tr K + e/2 d_y tr_gamma A_full.
    tau=s.trace(K); Dvol=tau+e*(s.trace(Ay)-2*s.trace(K*A)+zy)/2
    ny=1-e*z/2; ny_y=-e*zy/2
    # Tangential divergence of normal vector: -e div c.
    div=ny*Dvol+ny_y-e*divc
    normal_log=ny*(ell+e*(By/N-ell*B/N))-e*c.dot(dlogN)
    dk=s.diff(div+normal_log,e).subs(e,0)
    target=s.trace(Ay)/2-s.trace(K*A)-divc-c.dot(dlogN)-z*(tau+ell)/2+By/N-ell*B/N
    assert s.expand(dk-target)==0
    # BR20: common A, A_nn=0, [A_ab,y]=2j A_ab, [K]=j I.
    # Therefore the geometric variation of normal force has common trace,
    # even though its actual mean does not vanish a priori.
    Ayp=Ayp0=Ay+2*j*A; Kp=K+j*s.eye(3)
    dk0=lambda k,ay:s.trace(ay)/2-s.trace(k*A)-divc-c.dot(dlogN)
    assert s.expand(dk0(Kp,Ayp)-dk0(K,Ay))==0
    # Choose B=0 on wall, B_y=-N*mean dk_geom common. No changed A.
    R=dk0(K,Ay); assert s.expand((R+By/N).subs(By,-N*R))==0
    # g_tt time-acceleration correction -2NB and derivative.
    Bp,Bm,Byp,Bym,Nyp,Nym=s.symbols('Bp Bm Byp Bym Nyp Nym')
    jump=-2*(Nyp*Bp+N*Byp-Nym*Bm-N*Bym)
    assert jump.subs({Bp:0,Bm:0,Byp:Bym})==0
    # Higher even lapse jets: linear trace map (mean, jump) is rank two.
    vp,vm=s.symbols('vp vm')
    mat=s.Matrix([(vp+vm)/2,vp-vm]).jacobian([vp,vm]); assert mat.det()==-1
    print('PASS mean physical wall acceleration jet and temporal Israel compatibility')
    print('PASS independent mean/jump control of next lapse derivative; finite formal jets only')
if __name__=='__main__':run()
