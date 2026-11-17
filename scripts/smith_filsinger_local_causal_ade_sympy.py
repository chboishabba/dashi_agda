"""Exact local Maxwell–Lorentz split-Cayley propagation with a finite
graph-dependency cone. Reuses LorentzMaterial/curl_matrix and quadratic
energy from smith_filsinger_lorentz_ade_sympy. Does NOT prove physical
Maxwell light-cone support or independent environmental work.
"""
import sympy as S
from smith_filsinger_lorentz_ade_sympy import LorentzMaterial,curl_matrix,energy

def local_spec(n=3, material=None, load=0, curl=None):
    if not isinstance(n,int) or n<1:raise ValueError('n positive integer')
    m=(material or LorentzMaterial()).validated()
    load=S.sympify(load)
    if load.is_nonnegative is not True:raise ValueError('nonnegative receiver load')
    C=curl_matrix(n) if curl is None else S.Matrix(curl)
    if C.shape!=(n,n):raise ValueError('curl shape')
    M=S.diag(*([m.eps]*n+[m.mu]*n+
               [m.omega0sq/m.alpha]*n+[S.Integer(1)/m.alpha]*n))
    return dict(n=n,material=m,load=load,curl=C,mass=M)

def edge_updates(spec):
    n,m,C=spec['n'],spec['material'],spec['curl']
    edges=[]
    for i in range(n):
        for j in range(n):
            if C[i,j]!=0:
                edges.append(('curl',i,n+j,S.cancel(C[i,j]/m.eps),
                              S.cancel(-C[i,j]/m.mu)))
    for i in range(n):
        edges.append(('polar_E_V',i,3*n+i,-1/m.eps,m.alpha))
        edges.append(('polar_P_V',2*n+i,3*n+i,S.Integer(1),-m.omega0sq))
        if m.sigma>0:edges.append(('ohmic',i,i,-m.sigma/m.eps,S.Integer(0)))
        if spec['load']>0:
            edges.append(('useful_load',i,i,-spec['load']/m.eps,S.Integer(0)))
        if m.gamma>0:
            edges.append(('relaxation',3*n+i,3*n+i,-m.gamma,S.Integer(0)))
    return edges

def primitive_matrix(spec,edge):
    N=4*spec['n'];_,i,j,a,b=edge
    A=S.zeros(N)
    if i==j:A[i,i]=a
    else:A[i,j]=a;A[j,i]=b
    return A

def cayley_edge_step(spec,z,edge,dt=S.Rational(1,4)):
    dt=S.sympify(dt)
    if dt.is_positive is not True:raise ValueError('dt>0')
    n=spec['n'];M=spec['mass']
    if z.shape!=(4*n,1):raise ValueError('state shape')
    A=primitive_matrix(spec,edge)
    i,j=edge[1:3]
    support=sorted({i,j})
    sub=A.extract(support,support)
    eye=S.eye(len(support))
    T=(eye-dt*sub/2).inv()*(eye+dt*sub/2)
    znew=z.copy()
    initial=S.Matrix([z[k] for k in support])
    final=T*initial
    for row,k in enumerate(support):znew[k]=S.factor(final[row])
    mid=(initial+final)/2
    weight=M.extract(support,support)
    delta=S.factor(energy(znew,M)-energy(z,M))
    predicted=S.factor(dt*(mid.T*(sub.T*weight+weight*sub)*mid)[0]/2)
    if S.factor(delta-predicted)!=0:raise AssertionError('Cayley energy identity')
    if edge[0] in ('curl','polar_E_V','polar_P_V'):
        if predicted!=0:raise AssertionError('lossless primitive produced energy')
    elif predicted>0:raise AssertionError('passive primitive generated work')
    return dict(initial_state=z,z=znew,edge=edge,energy_change=delta,
                work=predicted,support=tuple(support))

def source_kick(spec,z,cell,current,dt=S.Rational(1,4),origin='natural'):
    n,m=spec['n'],spec['material'];dt=S.sympify(dt);j=S.sympify(current)
    if not 0<=cell<n:raise ValueError('local source cell')
    if dt.is_positive is not True:raise ValueError('dt>0')
    if origin not in ('natural','controller'):raise ValueError('source ownership')
    after=z.copy();after[cell]=S.factor(z[cell]+dt*j/m.eps)
    change=S.factor(energy(after,spec['mass'])-energy(z,spec['mass']))
    supplied=S.factor(dt*j*(z[cell]+after[cell])/2)
    assert S.factor(change-supplied)==0
    return dict(initial_state=z,z=after,kind=origin,cell=cell,
                work=supplied,energy_change=change)

def dependency_step(dependent,touched):
    result=set(dependent)
    if set(touched)&result:result.update(touched)
    return result

def dependency_cone(initial_index,steps):
    result={initial_index}
    for step in steps:
        touched=step['support'] if 'support' in step else (step['cell'],)
        result=dependency_step(result,touched)
    return result

def source_response(spec,initial_source_cell,ops,dt=S.Rational(1,4)):
    n=spec['n'];z=S.zeros(4*n,1)
    records=[source_kick(spec,z,initial_source_cell,1,dt)]
    z=records[-1]['z']
    for edge in ops:
        step=cayley_edge_step(spec,z,edge,dt)
        records.append(step);z=step['z']
    cone=dependency_cone(initial_source_cell,records)
    outside=[k for k in range(4*n) if k not in cone]
    if any(z[k]!=0 for k in outside):raise AssertionError('graph cone violated')
    return dict(field=z,cone=cone,records=records,all_outside_zero=True)

def full_ledger(spec,initial,records):
    previous=initial
    totals=dict(natural=S.Integer(0),controller=S.Integer(0),
                useful_load=S.Integer(0),ohmic=S.Integer(0),
                relaxation=S.Integer(0))
    for r in records:
        if r['initial_state']!=previous:raise ValueError('nonconsecutive state trace')
        previous=r['z']
        if 'edge' in r:
            kind=r['edge'][0]
            if kind in ('ohmic','relaxation','useful_load'):
                totals[kind]-=r['energy_change']
        else:totals[r['kind']]+=r['work']
    delta=S.factor(energy(previous,spec['mass'])-energy(initial,spec['mass']))
    residual=S.factor(delta+totals['useful_load']+totals['ohmic']+
                      totals['relaxation']-totals['natural']-totals['controller'])
    if residual!=0:raise AssertionError('ledger not exactly conserved')
    return dict(**totals,energy_change=delta,residual=residual,
                restored_all_states=previous==initial,
                physical_source_meter=False,physical_maxwell_front=False)
