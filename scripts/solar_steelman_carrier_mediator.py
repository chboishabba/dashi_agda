"""Local two-carrier polar lift of the constructed reciprocal mediator.
No prescribed shared phase; synchronized initial phases are a premise.
Not a measured constitutive tensor, canonical Hamiltonian or Maxwell field.
"""
import sympy as S
from solar_steelman_autonomous_mediator import run as mediator,evaluate,waveform
from solar_steelman_boundary_weld import branch,check,ledger,zero
I=S.I
OMEGA=S.Rational(520000,261)

def rhs(z,energies,phases,model):
    """Each cell has two positive modal energies and two unit phases.
    Modal energies e0,e1 are |h0|^2,|h1|^2 in complex amplitude coordinates.
    Physical clock coupling is not assumed: carrier phases rotate locally.
    """
    models,parent,order,flows=[model[k] for k in ('models','parent','order','flows')]
    e=[a+b for a,b in energies]
    u=[v*S.conjugate(w) for w,v in phases]
    assert all(S.expand(x*S.conjugate(x)-1)==0 for x in u)
    ratios=[S.cancel(v/evaluate(c,p)) for v,(_,_,c),p in zip(e,models,u)]
    F=S.zeros(z.rows,1);de=[]
    for k,(ids,r,_) in enumerate(models):
        f=waveform(r,u[k])*ratios[k]
        for j,i in enumerate(ids):F[i]+=f[j]
        de.append(-S.expand(z[ids,:].dot(f)))
    for j in order[1:]:
        p=parent[j];flux=flows[j]*ratios[p]*ratios[j]
        de[p]-=flux;de[j]+=flux
    # Both carrier amplitudes experience radial reciprocal reaction;
    # proportional energy allocation retains their positive energy ratio.
    split=[]
    for (a,b),v,t in zip(energies,de,e):
        share=S.cancel(a/t);part=share*v
        split.append((part,v-part))
    pd=[(I*OMEGA*w,I*(OMEGA+1)*v) for w,v in phases]
    return F.applyfunc(S.expand),split,pd

def algebra():
    # Actual complex carrier ODE h'=i omega h + (e'/2e) h.
    x,y,k,w=S.symbols('x y k w',real=True);h=x+I*y
    f=I*w*h+k*h/2
    assert S.expand(2*S.re(S.conjugate(h)*f)-k*(x*x+y*y))==0
    # Skew coupling to z under metric H/alpha: force proportional to
    # h energy; radial amplitude reaction accounts for all power.
    a,b,P,Q,S0,S1,c=S.symbols('a b P Q S0 S1 c',positive=True)
    flux=c*(a+b)*(P+Q)/(S0*S1)
    assert S.cancel(-a*flux/(a+b)-b*flux/(a+b)+P*flux/(P+Q)+Q*flux/(P+Q))==0
    # Beat phase derivative and return. Relative phase offsets are conserved,
    # hence local carrier construction alone does NOT synchronize cells.
    u,v=S.symbols('u v');assert S.expand(I*(OMEGA+1)*v*u-I*OMEGA*v*u-I*v*u)==0
    T=2*S.pi*261
    assert all(S.exp(I*w*T)==1 for w in (1,2,OMEGA,OMEGA+1))
    # An independent phase error persists; no attracting phase lock claimed.
    assert S.exp(I*OMEGA*T)==1

def boundary(model):
    hi,lo=model['rows'];U=S.eye(15);sh=U[:,0];rl=U[8:15,:]
    ih=S.ones(1,1);il=lo['p'];R=lo['load']
    vh=sh.T*hi['v'];vl=rl*lo['v'];Xh=-sh.T*hi['X']*sh;Xl=-rl*lo['X']*rl.T
    Lh,Kh=branch(S.Integer(2),S.Integer(1),Xh);Ll,Kl=branch(S.Integer(1),S.Integer(2),Xl)
    check(S.Integer(2),S.Integer(1),Lh,Kh,ih,ih-vh,-sh.T*lo['v'])
    check(S.Integer(1),S.Integer(2),Ll,Kl,il,vl-R*il,rl*hi['v'])
    assert zero(vh+I*Xh*ih-ih) and zero(vl-I*Xl*il-R*il)
    assert S.expand(S.re((il.H*R*il)[0]))==1
    ledger()
    print('PASS exact causal external boundary with same occupied mediator rows',flush=True)

def certify(model):
    algebra();boundary(model)
    models=model['models'];z=waveform({w:model['data'][w][0] for w in (1,2)},S.Integer(1))
    e=[evaluate(c,S.Integer(1)) for _,_,c in models]
    energies=[(v/2,v/2) for v in e];phases=[(S.Integer(1),S.Integer(1)) for v in e]
    F,de,pd=rhs(z,energies,phases,model)
    assert F==waveform({w:model['data'][w][2] for w in (1,2)},S.Integer(1))
    assert all(S.expand(a+b+evaluate(c,S.Integer(1))-mean)==0 for (a,b),c,mean in zip(de,model['local'],model['means']))
    assert S.expand(z.dot(F)+sum(a+b for a,b in de))==0
    assert all(a==I*OMEGA and b==I*(OMEGA+1) for a,b in pd)
    # Actual off-orbit independent phase and energy errors, not merely a
    # common-clock perturbation. Exact energy cancellation must survive.
    phases[0]=(S.Integer(1),I);phases[1]=(I,S.Integer(1))
    energies[0]=(e[0]/3,e[0]/4);z[0]+=1
    Fp,dep,_=rhs(z,energies,phases,model)
    residual=S.expand(z.dot(Fp)+sum(a+b for a,b in dep))
    assert S.cancel(residual,extension=S.sqrt(2))==0
    print('PASS 48 independent local two-carrier states, synchronized occupied orbit and off-phase energy ledger',flush=True)
    print('PASS carrier common return, 520000 and 520261 cycles; 48 local beat phases (relative offsets neutral)',flush=True)
    print('LIMIT constructed polar/skew law, phase-lock mechanism and physical HF tensor/Maxwell transport unproved',flush=True)
def run(m=None):
    certify(mediator(m))

if __name__=='__main__':run()
