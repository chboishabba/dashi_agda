"""Exact XCI/II passive energy identity and restored midpoint candidates."""
import json
import sympy as S
from smith_filsinger_lorentz_ade_sympy import generator,energy
q=S.Rational

def check(y0,y1,g,d,c=None,k=4):
    A,B,M=generator(n=2,load_conductance=0)
    A=S.Matrix(A); A[0,0]-=y0/2;A[1,1]-=(y1+g)/2
    A[2,2]-=d;A[3,3]-=d
    if c:
        A=A.row_join(S.zeros(8,1)).col_join(S.zeros(1,9));A[1,8]=g/2;A[8,1]=g/c;A[8,8]=-g/c
        B=B.col_join(S.zeros(1,2));M=S.diag(M,c)
    n=A.rows;z=S.Matrix(S.symbols('z:'+str(n),real=True));e=z[:2,:];h=z[2:4,:];v=z[6:8,:]
    b=S.Matrix(S.symbols('a:2',real=True));Y=S.diag(y0,y1);root=S.diag(S.sqrt(y0),S.sqrt(y1));J=2*root*b-Y*e
    # Energy equation on arbitrary state and incident amplitudes.
    out=root*e-b;load=g*(e[1]-(z[8] if c else 0))**2
    loss=q(1,5)*e.dot(e)+q(4,9)*v.dot(v)+q(3,2)*d*h.dot(h)
    assert S.expand((z.T*M*(A*z+2*B*root*b))[0]-(b.dot(b)-out.dot(out)-load-loss))==0
    # Exact source pulse after lossless delay and 45-degree mixer: normalize
    # aligned pulse to 1, external original two pulses each 1/sqrt(2).
    dt=q(1,10*k);I=S.eye(n);K=(I-dt*A/2).inv();T=2*K-I
    src=[S.zeros(2,1)]*(2*k)+[S.Matrix([0,1])]*k+[S.zeros(2,1)]*k
    kicks=[dt*K*2*B*root*a for a in src];w=S.zeros(n,1)
    for kick in kicks:w=T*w+kick
    z0=(I-T**(4*k)).inv()*w;z=z0;tot=[S.Integer(0)]*6
    for a,kick in zip(src,kicks):
        z1=T*z+kick;mid=(z+z1)/2;e=mid[:2,:];h=mid[2:4,:];v=mid[6:8,:];out=root*e-a
        vals=[dt*a.dot(a),dt*out.dot(out),dt*g*(e[1]-(mid[8] if c else 0))**2,dt*q(1,5)*e.dot(e),dt*q(4,9)*v.dot(v),dt*q(3,2)*d*h.dot(h)]
        assert S.expand(vals[0]-sum(vals[1:])-(energy(z1,M)-energy(z,M)))==0
        tot=[a+b for a,b in zip(tot,vals)];z=z1
    assert z==z0 and tot[0]==sum(tot[1:]);return dict(k=k,eta=float(tot[2]/tot[0]),ledger={k:str(v) for k,v in zip(('incident','reflected','terminal','ohmic','relaxation','magnetic'),tot)},exact_restored=True)
if __name__=='__main__':
    print(json.dumps({'series_rc':check(q(1,10),q(250),q(270),q(0),q(1000),2),'magnetic_loss':check(q(1,10),q(400),q(400),q(3,10),None,4)},indent=2))
