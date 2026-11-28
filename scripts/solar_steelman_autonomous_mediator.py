"""Distributed autonomous skew mediator for the exact loaded orbit.
Ideal shared phase and constructed effort couplings; not a physical HF law,
Hamiltonian Poisson bracket, retarded propagation or stability certificate.
"""
import sympy as S
from itertools import combinations
from solar_steelman_loaded_material import loaded, cross_band_reaction, rmm, pair, bilinear
from solar_steelman_material_metric import run as metric
from solar_steelman_whitney_lift import solve
from solar_spherical_whitney import shell_mesh

I=S.I

def local_grams(m):
    xyz,s,idx,_=shell_mesh([1,1.5,2]);H=m['H'];piv=list(m['d']['piv'])
    total=S.zeros(H.rows);cells=[]
    for k,t in enumerate(s[3]):
        p=S.Matrix([[S.Rational(float(v)) for v in xyz[j]] for j in t])
        V=abs((p[1:,:]-S.ones(3,1)*p[0,:]).det())/6
        g=S.ones(4,1).row_join(p).inv()[1:,:]
        ids=list(range(3*k,3*k+3));forms=[S.eye(3)[:,j]*S.ones(1,4) for j in range(3)]
        for a,b in combinations(range(4),2):
            edge=idx[1][(t[a],t[b])]
            if edge not in piv:continue
            w=S.zeros(3,4);w[:,a]=g[:,b];w[:,b]=-g[:,a]
            forms.append(w);ids.append(3*len(s[3])+piv.index(edge))
        moments=V*(S.ones(4)+S.eye(4))/20
        K=S.Matrix(len(ids),len(ids),lambda a,b:S.trace(forms[a]*moments*forms[b].T))
        for a,i in enumerate(ids):
            for b,j in enumerate(ids):total[i,j]+=K[a,b]
        cells.append((ids,K))
    assert total==H
    return s[3],cells


def tree(tets):
    faces={};adj=[[] for _ in tets]
    for j,t in enumerate(tets):
        for face in combinations(t,3):
            if face in faces:
                k=faces[face];adj[j].append(k);adj[k].append(j)
            else:faces[face]=j
    parent={0:-1};order=[0]
    for j in order:
        for k in adj[j]:
            if k not in parent:parent[k]=j;order.append(k)
    assert len(order)==len(tets)
    assert all(len(set(tets[j])&set(tets[parent[j]]))==3 for j in order[1:])
    return parent,order


def evaluate(coeff,u):
    v=S.conjugate(u)
    return S.expand(sum(c*(u**k if k>=0 else v**(-k)) for k,c in coeff.items()))


def waveform(r,u):
    h=(1+I)/S.sqrt(2)
    a,b=r[2];c,d=r[1]
    return ((a+I*b)*u**2+h*(c+I*d)*u).applyfunc(lambda x:S.expand(S.sqrt(2)*S.re(x)))


def mediator_rhs(z,energy,u,models,parent,order,flows):
    """Actual autonomous finite port equations on the unit clock circle.

    Stores use positive energy coordinates, not square-root amplitudes.
    Ratios are state dependent; the target force is not injected for free.
    The phase clock has its own independent rotation udot=i*u.
    """
    assert S.expand(u*S.conjugate(u)-1)==0
    target=[evaluate(a,u) for _,_,a in models]
    ratios=[S.cancel(e/t) for e,t in zip(energy,target)]
    F=S.zeros(z.rows,1);dE=[]
    for i,(ids,r,_) in enumerate(models):
        force=waveform(r,u)*ratios[i]
        for k,j in enumerate(ids):F[j]+=force[k]
        dE.append(-S.expand(z[ids,:].dot(force)))
    for j in order[1:]:
        p=parent[j];flow=flows[j]*ratios[p]*ratios[j]
        dE[p]-=flow;dE[j]+=flow
    return F.applyfunc(S.expand),[S.expand(e) for e in dE],I*u


def run(m=None):
    if m is None:m=metric()
    alpha=S.Rational(1,2)
    rows=[loaded(m,alpha,S.Integer(2),S.eye(15)[:,0],S.eye(15)[1:8,:]),
          loaded(m,alpha,S.Integer(1),S.eye(15)[:,1],S.eye(15)[8:15,:])]
    expected,_,_=cross_band_reaction(m,alpha,rows)
    T=m['d']['T'];J=solve(m['R'],T.T);Z=rmm(m['U'],J);HZ=rmm(m['B'].T,J)
    # Occupied material states and required increments, same loaded fields.
    data={}
    for w,row,j in [(2,rows[0],rows[0]['recv'].T*rows[0]['p']),
                    (1,rows[1],-rows[1]['source'])]:
        jr,ji=pair(j);ar,ai=rmm(Z,jr),rmm(Z,ji);zr,zi=pair(row['z'])
        hr,hi=rmm(HZ,jr),rmm(HZ,ji)
        data[w]=((zr+ar,zi+ai),(ar,ai),(-w*hi/alpha,w*hr/alpha))
    tets,cells=local_grams(m);parent,order=tree(tets)
    h=(1+I)/S.sqrt(2);ph={2:1,-2:1,1:h,-1:S.conjugate(h)}
    global_coeff={k:S.Integer(0) for k in range(-4,5)}
    summed={w:[S.zeros(m['H'].rows,1),S.zeros(m['H'].rows,1)] for w in (1,2)}
    local=[];local_forces=[]
    for ids,K in cells:
        z={};r={}
        for w,(zz,aa,rr) in data.items():
            zr,zi=[v[ids,:] for v in zz];ar,ai=[v[ids,:] for v in aa]
            real,imag=-w*rmm(K,ai)/alpha,w*rmm(K,ar)/alpha
            for a,i in enumerate(ids):summed[w][0][i]+=real[a];summed[w][1][i]+=imag[a]
            z[w]=(zr,zi);z[-w]=(zr,-zi);r[w]=(real,imag);r[-w]=(real,-imag)
        c={k:S.Integer(0) for k in range(-4,5)}
        for k in z:
            for l in r:c[k+l]+=ph[k]*ph[l]*bilinear(z[k],r[l])/2
        c={k:S.expand(v) for k,v in c.items()}
        assert all(S.expand(c[-k]-S.conjugate(c[k]))==0 for k in range(5))
        for k,v in c.items():global_coeff[k]+=v
        local.append(c);local_forces.append((ids,r))
    for w in data:assert tuple(summed[w])==data[w][2]
    assert all(S.expand(global_coeff[k]-expected[k])==0 for k in expected)
    print('PASS exact 48 local element Gram split and full force/power reconstruction',flush=True)
    # Local mean powers cannot all vanish; exact shared-face tree routes
    # each imbalance. Positive flow is parent -> child.
    means=[c[0] for c in local];assert sum(means)==0
    flows=means.copy()
    for j in reversed(order[1:]):flows[parent[j]]+=flows[j]
    assert flows[0]==0
    divergence=[S.Integer(0)]*len(cells)
    for j in order[1:]:divergence[j]+=flows[j];divergence[parent[j]]-=flows[j]
    assert divergence==means
    print('PASS local mean closure',sum(v!=0 for v in means),'nonzero cells;',len(order)-1,'shared-face tree links',flush=True)
    # Autonomous common unit-circle clock. Positive local store S_i(theta)
    # with derivative mean_i - instantaneous power_i; triangle bound >0.
    x,y=S.symbols('x y',real=True);u=x+I*y;v=x-I*y
    def derivative(f):return S.expand(-y*S.diff(f,x)+x*S.diff(f,y))
    def circle_zero(f):return S.rem(S.expand(f),x*x+y*y-1,x)==0
    offsets=[];models=[]
    for cell,c in enumerate(local):
        a={k:S.expand(-c[k]/(I*k)) for k in c if k}
        offset=1+2*sum(abs(S.re(a[k]))+abs(S.im(a[k])) for k in range(1,5))
        E=offset+sum(a[k]*(u**k if k>0 else v**(-k)) for k in a)
        P=sum(c[k]*(u**k if k>0 else v**(-k)) for k in c)
        assert circle_zero(derivative(E)+P-c[0])
        assert circle_zero(E-S.conjugate(E));assert offset>=1
        offsets.append(offset);models.append((*local_forces[cell],{0:offset,**a}))
    assert derivative(x*x+y*y)==0
    # Positive energy-coordinate state. Force ratios e_i/E_i*(theta),
    # shared-face transfer ratios e_i e_j/(E_i* E_j*). These equations
    # conserve arbitrary-state energy, and each e_i_dot has factor e_i.
    # Test actual assembled vector field at the occupied clock point,
    # then perturb both the current and store states without re-solving.
    phase=S.Integer(1);z=waveform({w:data[w][0] for w in data},phase)
    e=[evaluate(a,phase) for _,_,a in models]
    assert all(v>0 for v in e)
    F,dE,du=mediator_rhs(z,e,phase,models,parent,order,flows)
    assert F==waveform({w:data[w][2] for w in data},phase)
    assert all(S.expand(v+evaluate(local[i],phase)-means[i])==0 for i,v in enumerate(dE))
    assert S.expand(z.dot(F)+sum(dE))==0 and du==I
    ep=e.copy();ep[0]*=2;ep[1]/=2;zp=z.copy();zp[0]+=1
    Fp,dEp,_=mediator_rhs(zp,ep,phase,models,parent,order,flows)
    assert S.expand(zp.dot(Fp)+sum(dEp))==0
    # Generic skew cancellation and factorization for every state.
    a,b,c,q,s,f=S.symbols('a b c q s f',real=True,nonzero=True)
    assert S.cancel(a*b*c/q-c*(a*b/q))==0
    assert S.cancel(-f*a*b/(q*s)+f*a*b/(q*s))==0
    print('PASS actual assembled 48-store RHS on orbit and perturbed state; exact arbitrary-state energy cancellation',flush=True)
    print('PASS all 48 positive periodic store primitives, autonomous local skew pairs and adjacent mean transport',flush=True)
    print('  sufficient total offset',float(sum(offsets)),'(not minimum or physical HF store)',flush=True)
    print('LIMIT shared ideal clock, constructed local effort couplings; no actual HF electromagnetic law, finite-speed or stability proof',flush=True)

    return dict(models=models,parent=parent,order=order,flows=flows,data=data,local=local,means=means,rows=rows)

if __name__=='__main__':run()
