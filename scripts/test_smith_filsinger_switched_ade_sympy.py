from dataclasses import replace
import sympy as S
from smith_filsinger_switched_ade_sympy import step,transition,green
from smith_filsinger_lorentz_ade_sympy import generator,LorentzMaterial

def run():
    counts=dict(balance=0,stationary=0,causal=0,periodic=0,superposition=0,telescope=0)
    h=S.Rational(1,5)
    for n in (1,2,3):
        m=LorentzMaterial(); load=S.Rational(1,7)
        z=S.Matrix([S.Rational(i-2,7) for i in range(4*n)])
        j=S.ones(n,1); c=-j/3
        A,B,_=generator(n,m,load_conductance=load)
        T,F,_,_=transition(n,m,m.eps,h,load=load)
        L=S.eye(4*n)-h*A/2
        assert T==L.inv()*(S.eye(4*n)+h*A/2) and F==L.inv()*h*B
        counts['stationary']+=1
        maps=[]; initial=z; sums=0; first_storage=None
        for k in range(8):
            e1=S.Rational(3 if k%2==0 else 2)
            a,b,M0,M1=transition(n,m,e1,h,load=load); maps.append((a,b))
            if first_storage is None:first_storage=(z.T*M0*z)[0]/2
            r=step(z,j,c,m,e1,h,load=load)
            assert r['residual']==0
            assert all(r[x]>=0 for x in ('ohmic','relaxation','useful_load'))
            sums+=r['natural_work']+r['controller_work']+r['modulation_work']-r['ohmic']-r['relaxation']-r['useful_load']
            z=r['z']; m=replace(m,eps=e1); counts['balance']+=1
        assert (z.T*M1*z)[0]/2-first_storage==sums;counts['telescope']+=1
        for i in range(9):
            for k in range(8):
                g=green(maps,i,k)
                if i<=k:assert g==S.zeros(4*n,n);counts['causal']+=1
                if i+2<=8 and k+2<8:assert g==green(maps,i+2,k+2);counts['periodic']+=1
        assert green(maps,1,0)!=green(maps,2,1)
        direct=S.zeros(4*n,1)
        for i,(a,b) in enumerate(maps,1):
            direct=a*direct+b*j
            assert direct==sum((green(maps,i,k)*j for k in range(i)),S.zeros(4*n,1));counts['superposition']+=1
    print(counts)
if __name__=='__main__':run()
