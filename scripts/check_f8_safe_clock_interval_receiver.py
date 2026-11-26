"""Exact Q(sqrt(145)) contraction of the actual captured binary64 state.
Bounds receiver arithmetic, NOT errors in the propagated state, source,
clock inversion, stage RHS or continuum model. Uses binary native slot data.
"""
import argparse,json,math
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import ksw668_f8_tt_multipole as original
from check_f8_parity_capture_tail import capture

class A:
    """x+y sqrt(145), exact rational arithmetic."""
    def __init__(self,x=0,y=0):self.x,self.y=Q(x),Q(y)
    @staticmethod
    def lift(a):return a if isinstance(a,A) else A(a)
    def __add__(self,o):o=A.lift(o);return A(self.x+o.x,self.y+o.y)
    __radd__=__add__
    def __neg__(self):return A(-self.x,-self.y)
    def __sub__(self,o):return self+-A.lift(o)
    def __rsub__(self,o):return A.lift(o)+-self
    def __mul__(self,o):o=A.lift(o);return A(self.x*o.x+145*self.y*o.y,self.x*o.y+self.y*o.x)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=A.lift(o);d=o.x*o.x-145*o.y*o.y
        return self*A(o.x/d,-o.y/d)
    def __rtruediv__(self,o):return A.lift(o)/self
    def __pow__(self,n):
        if n<0:return (1/self)**(-n)
        r=A(1)
        for _ in range(n):r=r*self
        return r
    def zero(self):return self.x==self.y==0
    def interval(self):
        S=10**60;k=math.isqrt(145*S*S);a,b=Q(k,S),Q(k+1,S)
        assert a*a<=145<b*b
        return sorted((self.x+self.y*a,self.x+self.y*b))
    def outward(self,digits=35):
        l,h=self.interval();s=10**digits;lo=l*s;hi=h*s
        n=lo.numerator//lo.denominator;m=-((-hi.numerator)//hi.denominator)
        return [str(n),str(m)] # fixed decimal units 10^-digits

T=12;b=Q(1,T);v=A(0,Q(-1,145));a,c=1+v,1-v;s=1-v*v
acc=Q(T**3,(1+T*T)**2);beta=A(0,Q(1,T));J=A(0,Q(-1,T*145))

def rows(j):
    W,Wt,D,E,Y,L,X=j;F=v*W+s*D;R=-Wt+2*v*E+s*Y+(acc-3/b)*D+L
    box=-Wt+2*v*E+s*Y+acc*D+L;N=v*v*Wt+2*v*s*E+s*s*Y-v*v*acc*D
    E4=-b*b*(beta*beta*Wt+J*W+L)/4;legacy=-b*b*(beta*beta*Wt+J*W+X)/4
    direct=b*b*(-N/(2*s)+box/6);SMS=-b*b*(beta*beta*Wt+(J+2*beta)*W-L)/2
    assert (direct-SMS+(b+b**3/2)*F+b*b*R/3).zero()
    return [E4,legacy,direct,SMS,F,R]


def q(x):return Q(float(x))
def receiver(U,P,M,W,Pt,Mt,force,prev,nextW,dr,h,dt,r,eps):
    dr,h,dt,r,eps=map(q,(dr,h,dt,r,eps));j=int(r/dr);u=r/dr-j;ids=range(j-1,j+3)
    w=[-u*(u-1)*(u-2)/6,(u+1)*(u-1)*(u-2)/2,-(u+1)*u*(u-2)/2,(u+1)*u*(u-1)/6]
    dw=[-(3*u*u-6*u+2)/6,(3*u*u-4*u-1)/2,(-3*u*u+2*u+2)/2,(3*u*u-1)/6];dw=[x/dr for x in dw]
    dd=[(1-u)/dr**2,(3*u-2)/dr**2,(1-3*u)/dr**2,u/dr**2]
    out=[[] for _ in range(4)]
    for m,ell in enumerate((0,2,4)):
        fac=(r/eps)**ell
        dot=lambda x,weights=w:fac*sum((weights[k]*x(i) for k,i in enumerate(ids)),A())
        Uj=lambda k,i:q(U[m,k,i]);Wj=lambda k,i:q(W[m,k,i]);Nj=lambda k,i:(q(P[m,k,i])-q(M[m,k,i]))/2
        Nt=lambda k,i:(q(Pt[m,k,i])-q(Mt[m,k,i]))/2
        B=dot(lambda i:(q(nextW[m,i])-q(prev[m,i]))/(2*dt));Bstage=dot(lambda i:(a*q(Pt[m,0,i])+c*q(Mt[m,0,i]))/2+acc*Nj(0,i));W0=dot(lambda i:Wj(0,i))
        L=dot(lambda i:Uj(0,i),[dd[k]+(2*ell+2)*dw[k]/r for k in range(4)])
        X=dot(lambda i:Uj(0,i),[dd[k]+2*ell*dw[k]/r+ell*(ell-1)*w[k]/r**2 for k in range(4)])
        D=dot(lambda i:(-3*Uj(0,i)+4*Uj(1,i)-Uj(2,i))/(2*h));E=dot(lambda i:(-3*Wj(0,i)+4*Wj(1,i)-Wj(2,i))/(2*h));Y=dot(lambda i:(Uj(2,i)-2*Uj(1,i)+Uj(0,i))/h**2)
        De=dot(lambda i:(Uj(2,i)-Uj(0,i))/(2*h));Ee=dot(lambda i:(Wj(2,i)-Wj(0,i))/(2*h));Ye=dot(lambda i:(Uj(4,i)-2*Uj(2,i)+Uj(0,i))/(4*h*h))
        Dc=dot(lambda i:Nj(0,i));Ec=dot(lambda i:Nt(0,i));Yc=dot(lambda i:(q(Pt[m,0,i])-q(force[m,0,i]))/(2*a)+(q(Mt[m,0,i])-q(force[m,0,i]))/(2*c))
        for k,jets in enumerate(([W0,B,D,E,Y,L,X],[W0,B,De,Ee,Ye,L,X],[W0,B,Dc,Ec,Yc,L,X],[W0,Bstage,De,Ee,Ye,L,X])):out[k].append(rows(jets))
    return out


def run(work):
    output={};worst=0.;checks=0
    for label in ('A0','A1','C0','C1'):
        p=work/(label+'.json');ck=work/(label+'.npz');side=work/(label+'.receiver-state.npz');prod=json.loads(p.read_text());old=capture(ck,side,p)
        with np.load(side,allow_pickle=False) as z:
            U,P,M,W,source=[z[k].copy() for k in ('U','P','M','Ut','source')];dr,h,b0,v0,amp=[float(z[k].item()) for k in ('dr','dy','b','v','amp')]
        with np.load(ck,allow_pickle=False) as z:nextP=z['P'][:,0,:].copy();nextM=z['M'][:,0,:].copy();prev=z['w2'].copy()
        dt=prod['step_time'];tn=12.
        for _ in range(7):tn-=(original.F(tn)-original.F(12.)-dt)/(math.sqrt(1+tn*tn)/tn**2)
        vn=-1/math.sqrt(1+tn*tn);nextW=((1+vn)*nextP+(1-vn)*nextM)/2;nextW[:,-1]=0
        nr=U.shape[-1];cp=np.zeros((3,nr));cm=cp.copy();j=np.arange(1,nr)
        for i,d in enumerate((3,7,11)):
            den=(j+.5)**d-(j-.5)**d;cp[i,1:]=d*(j+.5)**(d-1)/den;cm[i,1:]=d*(j-.5)**(d-1)/den
        Wu,Pt,Mt=[np.zeros_like(U) for _ in range(3)];original.stage(U,P,M,Wu,Pt,Mt,dr,h,b0,v0,amp,source,cp,cm,3)
        force=np.zeros_like(U);N=(P-M)/2
        for i,d in enumerate((3,7,11)):
            force[i,:,0]=2*d*(U[i,:,1]-U[i,:,0])/dr**2
            force[i,:,1:-1]=(cp[i,1:-1]*(U[i,:,2:]-U[i,:,1:-1])-cm[i,1:-1]*(U[i,:,1:-1]-U[i,:,:-2]))/dr**2
        force-=3*N/(b0+h*np.arange(U.shape[1]))[None,:,None];force[:,:,-1]=0
        output[label]={}
        for place,r in [('near',prod['nominal_receiver_r']),('far',prod['far_receiver_grid_r'])]:
            o=receiver(U,P,M,W,Pt,Mt,force,prev,nextW,dr,h,dt,r,prod['eps']);names=('raw','even','characteristic','even_stage_time');total={};diff={}
            for k,packet in enumerate(o):
                total[names[k]]=[sum((packet[m][j] for m in range(3)),A()).outward() for j in range(6)]
                diff[names[k]]=[(packet[m][2]-packet[m][3]).outward() for m in range(3)]
                for m in range(3):
                    for j in range(6):
                        a0,a1=packet[m][j].interval();ref=old['receivers'][place]['observations'][names[k]][j][m];err=abs(float((a0+a1)/2)-ref);worst=max(worst,err);checks+=1
                        assert err<1e-11*max(1.,abs(ref)),(label,place,k,m,j,err,ref)
            output[label][place]=dict(totals=total,direct_minus_SMS_per_mode=diff,raw_minus_even_direct_per_mode=[(o[0][m][2]-o[1][m][2]).outward() for m in range(3)])
    return dict(scope='Exact algebraic receiver contraction on captured binary64 operands and represented radial/temporal coordinates. No propagation/clock/source/RHS error bound, no B continuum coefficient or physical sign certificate.',interval_units='10^-35',rows=['E4','legacy4','direct','SMS','F','R'],exact_offshell_identities=4*2*4*3,compared_float_rows=checks,max_abs_difference_from_float_adapter=worst,runs=output)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--work',required=True,type=Path);a0=p.parse_args();print(json.dumps(run(a0.work),indent=2))
