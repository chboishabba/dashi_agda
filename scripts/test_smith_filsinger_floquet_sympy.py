from dataclasses import replace
import sympy as S
from smith_filsinger_lorentz_ade_sympy import LorentzMaterial
from smith_filsinger_switched_ade_sympy import transition,step
from smith_filsinger_floquet_sympy import floquet,two_phase_sidebands

def run():
    count=0
    for n in (1,2):
        m=LorentzMaterial(); h=S.Rational(1,5); source=S.ones(n,1); load=S.Rational(1,7)
        for eps in (m.eps,S.Integer(3)):
            m1=replace(m,eps=eps)
            maps=[transition(n,m,eps,h,load=load)[:2],transition(n,m1,m.eps,h,load=load)[:2]]
            for lam in (S.Integer(1),S.Integer(-1)):
                M,z=floquet(maps,lam,source)
                assert z[2]==lam**2*z[0];count+=1
                a,b=two_phase_sidebands(z,lam)
                assert a+b==z[0] and lam*(a-b)==z[1];count+=1
                assert b==S.zeros(4*n,1);count+=1  # DC / Nyquist controls can be blind
                total=0
                for j,(mat,end) in enumerate(((m,eps),(m1,m.eps))):
                    r=step(z[j],S.zeros(n,1),source*lam**j,mat,end,h,load=load)
                    assert r['z']==z[j+1] and r['residual']==0;count+=1
                    total+=r['controller_work']+r['modulation_work']-r['ohmic']-r['relaxation']-r['useful_load']
                assert total==0;count+=1
            lam=S.I
            M,z=floquet(maps,lam,source)
            z=[v.applyfunc(S.simplify) for v in z]
            a,b=two_phase_sidebands(z,lam)
            assert (z[2]-lam**2*z[0]).applyfunc(S.simplify)==S.zeros(4*n,1);count+=1
            assert (b.applyfunc(S.simplify)==S.zeros(4*n,1))==(eps==m.eps);count+=1
    try: floquet([(S.eye(1),S.eye(1))],1,S.ones(1,1))
    except ValueError: count+=1
    else: raise AssertionError('singularity accepted')
    print(f'{count} exact Floquet checks PASS')
if __name__=='__main__':run()
