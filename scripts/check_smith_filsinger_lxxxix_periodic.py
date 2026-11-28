"""Independent exact 4-bin periodic orbit test for LXXXIX selective loads."""
import json
from pathlib import Path
import sympy as S
from smith_filsinger_lorentz_ade_sympy import generator,energy
Q=S.Rational; DT=Q(1,10);P=((0,0),(1,0),(0,1),(0,0))

def periodic_case(Z,G,amp,local=True):
    Y=1/Z;A,B,M=generator(n=2,load_conductance=Y)
    L=S.diag(0,G) if local else S.diag(G,G)
    A=S.Matrix(A);A[:2,:2]=A[:2,:2]-L/2
    K=(S.eye(8)-DT*A/2).inv();T=2*K-S.eye(8)
    kicks=[]
    for x0,x1 in P:
        a=S.Matrix([Q(x0)*amp,Q(x1)*amp]);kicks.append(DT*K*B*(2*a/Z))
    v=S.zeros(8,1)
    for kick in kicks:v=T*v+kick
    z0=(S.eye(8)-T**4).inv()*v
    z=z0.copy(); tot={k:S.Integer(0) for k in ('incident','reflected','terminal','other','ohmic','relaxation','storage','net')}
    for (x0,x1),kick in zip(P,kicks):
        a=S.Matrix([Q(x0)*amp,Q(x1)*amp]);z1=T*z+kick;mid=(z+z1)/2
        e=mid[:2,:];vv=mid[6:8,:];b=e-a
        d=dict(incident=DT*a.dot(a)/Z,reflected=DT*b.dot(b)/Z,
               terminal=DT*G*e[1]**2,other=DT*L[0,0]*e[0]**2,
               ohmic=DT*Q(1,5)*e.dot(e),relaxation=DT*Q(4,9)*vv.dot(vv),
               storage=S.factor(energy(z1,M)-energy(z,M)))
        d['net']=d['incident']-d['reflected']
        assert S.factor(d['net']-sum(d[k] for k in ('terminal','other','ohmic','relaxation','storage')))==0
        for k in tot:tot[k]+=d[k]
        z=z1
    assert z==z0 and tot['storage']==0 and tot['terminal']>0
    assert S.factor(tot['net']-sum(tot[k] for k in ('terminal','other','ohmic','relaxation')))==0
    return dict(Z=str(Z),G=str(G),localised=local,incident=float(tot['incident']),
        reflected=float(tot['reflected']),net=float(tot['net']),
        terminal=float(tot['terminal']),other=float(tot['other']),
        ohmic=float(tot['ohmic']),relaxation=float(tot['relaxation']),
        terminal_per_incident=float(tot['terminal']/tot['incident']),
        terminal_per_net=float(tot['terminal']/tot['net']),
        capture=float(tot['net']/tot['incident']),restored_exact=True,energy_residual_exact_zero=True)

if __name__=='__main__':
    rows={
      'periodic_uniform':periodic_case(Q(3,32),Q(24),Q(1,4),False),
      'periodic_selective':periodic_case(Q(3,32),Q(24),Q(1,4),True),
      'periodic_tuned':periodic_case(Q(1,20),Q(6433843,200000),S.sqrt(Q(1,20)/Q(3,2)),True)
    }
    assert all(x['restored_exact'] and x['energy_residual_exact_zero'] for x in rows.values())
    print(json.dumps(rows,indent=2))
    Path('/mnt/data/filsinger_lxxxix_periodic_receipt.json').write_text(json.dumps(rows,indent=2)+'\n')
