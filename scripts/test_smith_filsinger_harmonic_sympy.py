from dataclasses import replace
import sympy as S
from smith_filsinger_lorentz_ade_sympy import LorentzMaterial
from smith_filsinger_switched_ade_sympy import transition
from smith_filsinger_harmonic_sympy import harmonic_transfer,quadrature_step,clean


def run():
    count=0
    for N,root in ((2,-1),(3,(-1+S.I*S.sqrt(3))/2),(4,S.I)):
        root=S.sympify(root); lam=S.I; h=S.Rational(1,5); load=S.Rational(1,7)
        for switched in (False,True):
            eps=[S.Integer(2+(j%2 if switched else 0)) for j in range(N)]
            mats=[replace(LorentzMaterial(),eps=e) for e in eps]
            maps=[transition(1,mats[j],eps[(j+1)%N],h,load=load)[:2] for j in range(N)]
            H=harmonic_transfer(maps,lam,root)
            for m in range(N):
                for n in range(N):
                    if m!=n and not switched:
                        assert H[m*4:(m+1)*4,n:n+1]==S.zeros(4,1);count+=1
            if switched:
                assert any(H[m*4:(m+1)*4,n:n+1]!=S.zeros(4,1) for m in range(N) for n in range(N) if m!=n);count+=1
            u=S.Matrix([S.Integer(j+1)+S.I for j in range(N)]); c=clean(H*u)
            z=[clean(sum((c[m*4:(m+1)*4,:]*root**(m*j)*lam**j for m in range(N)),S.zeros(4,1))) for j in range(N+1)]
            total=0; mod=0
            for j,(T,F) in enumerate(maps):
                src=S.Matrix([S.simplify(sum(u[n]*root**(n*j)*lam**j for n in range(N)))])
                assert clean(z[j+1]-T*z[j]-F*src)==S.zeros(4,1);count+=1
                w=quadrature_step(z[j],S.zeros(1,1),src,mats[j],eps[(j+1)%N],h,load=load)
                assert clean(w['z']-z[j+1])==S.zeros(4,1) and w['residual']==0;count+=1
                assert all(w[k].is_nonnegative for k in ('ohmic','relaxation','useful_load'));count+=1
                total+=w['controller_work']+w['modulation_work']-w['ohmic']-w['relaxation']-w['useful_load'];mod+=w['modulation_work']
            assert S.simplify(total)==0;count+=1
            if not switched:assert mod==0;count+=1
            print(N,switched,'modulation work',S.simplify(mod),flush=True)
    print(count,'exact harmonic checks PASS')
if __name__=='__main__':run()
