"""S2 seven-edge distributed trace on P0AB grids. Normalized finite box, not radiation."""
import sys, hashlib, json
from pathlib import Path
from itertools import product, combinations
import numpy as np
from scipy.sparse import csr_matrix, kron, diags
from scipy.sparse.linalg import splu
raw=Path(sys.argv[1]).read_bytes()
if hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='66c63c068144b49db850dc93c6d204fd09e3a3af':
    c=raw.decode(); raw=(c[c.index('def sparse('):c.index('def frame(')]+c[c.index('def refine('):c.index('def assay(')]).encode()
assert hashlib.sha256(raw).hexdigest()== 'd5502bf04844668d0636d9943d7cbc33f445c5884eac483038224edf6dbf0972'
exec(compile(raw,'P0AB selected definitions','exec'))
coarse=complex_grid(4); fine=complex_grid(12); R,H=refine(4,coarse,fine)
G,C,Z=fine[2]; I1=H[1].astype(float)/27; I2=H[2].astype(float)/27
M=flat_mass(12,1,4); N=flat_mass(12,2,4); Mc=flat_mass(4,1,4); Nc=flat_mass(4,2,4); Cc=coarse[2][1]
# Original XCIII/XCIV seven directed edges, two oriented faces.
edges=[(1,4),(2,5),(0,1),(1,2),(3,4),(4,5),(0,3)]
Gp=np.zeros((7,6),dtype=int)
for i,(a,b) in enumerate(edges): Gp[i,a]=-1;Gp[i,b]=1
Dp=np.array([[1,0,1,0,-1,0,-1],[-1,1,0,1,0,-1,0]])
assert not np.any(Dp@Gp)
pts=[(3,3,6),(6,3,6),(9,3,6),(3,6,6),(6,6,6),(9,6,6)]
# Whole translated copies of receiver chains (not independent edge smearing).
entries=[[],[],[]]
for shift in product((-1,0,1),repeat=3):
    p=[tuple(a+b for a,b in zip(v,shift)) for v in pts]
    for j,v in enumerate(p): entries[0].append((j,fine[1][0][(),v],1))
    for j,(a,b) in enumerate(edges):
        ax=next(i for i in range(3) if p[a][i]!=p[b][i]);assert p[b][ax]-p[a][ax]==3
        for d in range(3):
            v=list(p[a]);v[ax]+=d;entries[1].append((j,fine[1][1][(ax,),tuple(v)],1))
    for j,a in enumerate((0,1)):
        for x,y in product(range(3),repeat=2):
            v=(p[a][0]+x,p[a][1]+y,p[a][2]);entries[2].append((j,fine[1][2][(0,1),v],1))
Q=[sparse(e,(m,len(fine[0][k]))) for k,(e,m) in enumerate(zip(entries,(6,7,2)))]
assert zero(Q[1]@G-csr_matrix(Gp)@Q[0])
assert zero(Q[2]@C-csr_matrix(Dp)@Q[1])
T=Q[1].astype(float)/27; Tc=T@I1
# Exact source charge compatibility under injection, including all seven edges.
assert zero(G.T@Q[1].T-Q[0].T@csr_matrix(Gp.T))
assert np.linalg.matrix_rank(T.toarray())==7
mf=splu(M.tocsc()); nf=splu(N.tocsc())
B=T.T.toarray(); gain=np.sqrt(np.linalg.eigvalsh(T@mf.solve(B))[-1])
rows=[]
for omega in (.5,1.,2.):
    # Positive uniform damping is an explicit surrogate, not an outgoing BC.
    s=.2+1j*omega
    K=s*M+(C.T@N@C)/s; Kc=s*Mc+(Cc.T@Nc@Cc)/s
    kf=splu(K.tocsc()); kc=splu(Kc.tocsc())
    e=kf.solve(B); b=-(C@e)/s; impedance=T@e
    ec=kc.solve(Tc.T.toarray()); bc=-(Cc@ec)/s; zc=Tc@ec
    ef=I1@ec; bf=I2@bc
    r=B-s*(M@ef)+C.T@(N@bf); q=-s*bf-C@ef
    # Complex energy residual bound in the full fine first-order system.
    res=np.sqrt(np.maximum(0,np.sum((r.conj()*mf.solve(r.real)).real+(r.conj()*1j*mf.solve(r.imag)).real,axis=0)+np.sum((q.conj()*(N@q)).real,axis=0)))
    err=np.linalg.norm(impedance-zc,axis=0); bound=gain*res/s.real
    assert np.all(err<=bound+1e-10)
    assert np.max(abs(impedance-impedance.T))<1e-10
    lam=np.linalg.eigvalsh((impedance+impedance.conj().T)/2)[0];assert lam>0
    work=np.real(np.diag(impedance)); loss=s.real*np.sum((e.conj()*(M@e)).real+(0),axis=0)+s.real*np.sum((b.conj()*(N@b)).real,axis=0)
    assert np.max(abs(work-loss))<1e-10
    # Exact zero-mode charge relation for all independent port columns.
    assert np.max(abs(s*(G.T@(M@e))-G.T@B))<1e-10
    rows.append(dict(omega=omega,min_hermitian_eigenvalue=float(lam),max_work_error=float(np.max(abs(work-loss))),max_port_error=float(max(err)),max_residual_bound=float(max(bound))))
# Zero initial data and no input cannot create a field; gradient mode retained.
assert zero(C@G)
print(json.dumps(dict(status='CONDITIONAL_DISTRIBUTED_SEVEN_EDGE_PORT',fine_edges=M.shape[0],fine_faces=N.shape[0],translated_copies=27,port_rank=7,rows=rows,physical_admission=False),indent=2))
