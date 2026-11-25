"""XCI exact finite Maxwell/Lorentz spectral and passive network consumer.
No measured source, hardware, or continuous Maxwell PDE claim.
"""
import json
import sympy as S
from smith_filsinger_lorentz_ade_sympy import generator, energy
q=S.Rational; dt=q(1,10); Z=q(1,200); Y=1/Z; G=q(204)
P=[S.Matrix(v) for v in ((0,0),(1,0),(0,1),(0,0))]

def system(g=0,tau=q(1,20)):
    A,B,M=generator(n=2,load_conductance=Y)
    A=S.Matrix(A); A[1,1]-=G/2
    if g:
        assert g>0 and tau>0
        A=A.row_join(S.zeros(8,1)).col_join(S.zeros(1,9))
        A[1,1]-=g/2; A[1,8]=g/2; A[8,1]=1/tau; A[8,8]=-1/tau
        B=B.col_join(S.zeros(1,2)); M=S.diag(M,g*tau)
    return A,B,M

def solve(a,g=0):
    A,B,M=system(g); n=A.rows; I=S.eye(n)
    K=(I-dt*A/2).inv(); T=2*K-I; kicks=[dt*K*B*(2*Y*v) for v in a]
    v=S.zeros(n,1)
    for kick in kicks:v=T*v+kick
    z0=(I-T**4).inv()*v; z=z0; es=[]; bs=[]
    tot=dict.fromkeys(('incident','reflected','terminal','ohmic','relaxation','memory','storage'),S.Integer(0))
    for a0,k in zip(a,kicks):
        z1=T*z+k; mid=(z+z1)/2; e=mid[:2,:]; vel=mid[6:8,:]; b=e-a0
        d=dict(incident=dt*Y*a0.dot(a0),reflected=dt*Y*b.dot(b),terminal=dt*G*e[1]**2,
               ohmic=dt*q(1,5)*e.dot(e),relaxation=dt*q(4,9)*vel.dot(vel),
               memory=dt*g*(e[1]-mid[8])**2 if g else 0,storage=energy(z1,M)-energy(z,M))
        assert S.expand(d['incident']-sum(d[k] for k in d if k!='incident'))==0
        for k in tot:tot[k]+=d[k]
        es.append(e); bs.append(b); z=z1
    assert z==z0 and tot['storage']==0
    assert S.expand(tot['incident']-sum(tot[k] for k in tot if k!='incident'))==0
    return tot,es,bs,T

def dft(a):
    return [sum(((-S.I)**(k*j)*a[j] for j in range(4)),S.zeros(2,1)) for k in range(4)]

def norm(v):return S.expand((v.conjugate().T*v)[0])

def pack(t):return dict(**{k:str(S.factor(v)) for k,v in t.items()},eta=float(t['terminal']/t['incident']))

def run():
    base,e,b,T=solve(P); ah=dft(P); eh=dft(e)
    assert all(S.simplify(x)==0 for x in eh[0].col_join(eh[2]))
    assert sum(map(norm,ah))==4*sum(map(norm,P))
    assert ah[3]==ah[1].conjugate()
    s=20*S.I; C=S.Matrix([[1,-1],[0,1]])
    D=(2*s+q(1,5)+q(3,2)*s/(s*s+q(2,3)*s+4))*S.eye(2)+C*C.T/(q(3,2)*s)
    H=2*Y*(D+Y*S.eye(2)+S.diag(0,G)).inv(); h=H[1,:]
    assert all(S.simplify(x)==0 for x in H*ah[1]-eh[1])
    lam=S.simplify(G/Y*norm(h.T)); assert 0<lam<1
    assert S.simplify(base['terminal']/base['incident']-G/Y*norm(h*ah[1])/sum(map(norm,P))/2)==0
    active=[S.simplify(((-S.I)**(-j)*ah[1]+(-S.I)**(-3*j)*ah[3])/4) for j in range(4)]
    act,*_=solve(active); assert S.simplify(act['terminal']-base['terminal'])==0
    # Causal lossless one-bin delay on port 0 and rational orthogonal mixer.
    # Both directions have their own delay state; no negative-time advance.
    R=q(1,29)*S.Matrix([[20,-21],[21,20]]); assert R.T*R==S.eye(2)
    inner=[R*S.Matrix([P[(j-1)%4][0],P[j][1]]) for j in range(4)]
    tuned,_,bout,_=solve(inner); reverse=[R.T*v for v in bout]
    outer=[S.Matrix([reverse[(j-1)%4][0],reverse[j][1]]) for j in range(4)]
    store=[]
    for j in range(4):
        prev=dt*Y*(P[(j-1)%4][0]**2+reverse[(j-1)%4][0]**2)
        nxt=dt*Y*(P[j][0]**2+reverse[j][0]**2)
        assert S.expand(dt*Y*(norm(P[j])+norm(bout[j])-norm(inner[j])-norm(outer[j])))==nxt-prev
        store.append(nxt-prev)
    assert sum(store)==0 and sum(map(norm,outer))==sum(map(norm,bout))
    assert tuned['incident']==base['incident'] and tuned['terminal']>base['terminal']
    assert S.simplify(tuned['terminal']/tuned['incident']-lam/2)<0
    mem,*_=solve(inner,q(1)); assert mem['memory']>0
    # Exact zero-input and dark-frequency negative controls.
    for a in ([S.zeros(2,1)]*4,[S.Matrix([1,0])]*4,[(-1)**j*S.Matrix([1,0]) for j in range(4)]):
        x,*_=solve(a); assert x['terminal']==0
    return dict(status='PASS_EXACT_FINITE_MODEL',baseline=pack(base),active_only=pack(act),
                unrestricted_active_optimum=str(lam),unrestricted_active_optimum_decimal=float(lam),
                unchanged_external_source_mode_preserving_ceiling=float(lam/2),
                lossless_delay_mixer=pack(tuned),passive_memory_candidate=pack(mem),
                source_bins=[[str(v) for v in a] for a in P],delay_storage_restored=True,
                fixed_source_external_incident_unchanged=True,physical_calibration=False)

if __name__=='__main__':print(json.dumps(run(),indent=2))
