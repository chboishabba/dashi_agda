"""Conditional C4 multiplicity fixtures; not selected Suzuki matrices."""
import numpy as np
import sympy as sp
from toe_cyclotomic_hom_batch import apply_batch
from toe_cyclotomic_operator import compile_shape,points
import check_toe_atlas_mirror as M

# Each fixture has explicit 12 and 78 blocks and retains eigenvalue orientation.
# These are illustrative spectra, NOT obtained from the original class table.
fixtures = {'6E': ([1]*6+[3]*6+[1]*39+[3]*39, -1, 90),
            '6B': ([1]*6+[3]*6+[0]*45+[2]*33, 1, 66)}
A=M.inv(M.Pa)@M.r@M.Pa%3; B=M.inv(M.Pa)@M.m@M.Pa%3
records={(name,s):dict(compile_shape(G,lam,s),scalar=g) for s in (1,2) for name,G,lam,g in [('r',A,1,[1,0,27]),('s',B,2,[1,0,1])]}

def ipow(v,k):
    a,b=np.split(v,2,axis=2)
    aa=np.zeros_like(a); bb=np.zeros_like(b)
    for j in range(4):
        mask=(k%4==j)
        x,y=((a,b),(-b,a),(-a,-b),(b,-a))[j]
        aa[:,:,mask]=x[:,:,mask]; bb[:,:,mask]=y[:,:,mask]
    return np.concatenate((aa,bb),axis=2)

def act(state,name,exponents,sign,adj=False):
    phase,v,den=state; target=3-phase if name=='s' else phase
    out,d=apply_batch(records[name,target if adj else phase],v,adjoint=adj)
    if name=='r':
        # Mirror swaps phase sectors linearly; inverse gauges and inverse spectra.
        k=(np.array(exponents)+(1 if sign==-1 else 0))*(1 if phase==1 else -1)*(-1 if adj else 1)
        out=ipow(out,k)
    return target,out,den*d

def same(a,b): return a[0]==b[0] and np.array_equal(a[1]*b[2],b[1]*a[2])
X=points(6); parity=(-X%3)@3**np.arange(5,-1,-1)
v=np.random.default_rng(42).integers(-2,3,(2,729,180)).astype(object)
for branch,(e,sign,trace) in fixtures.items():
    L=sp.diag(*[sp.I**k for k in e]); assert L**4==sp.eye(90)
    assert sp.trace(L**2)*sign==trace
    for phase in (1,2):
        x=(phase,v,1); r=act(x,'r',e,sign); r2=act(r,'r',e,sign)
        expected=ipow(v[:,parity],2*(np.array(e)+(sign==-1)))
        assert same(r2,(phase,expected,1))
        r3=act(r2,'r',e,sign); assert same(act(r3,'r',e,sign),x)
        assert same(act(r,'r',e,sign,True),x)
        mirror=act(x,'s',e,sign); assert same(act(mirror,'s',e,sign),x)
        assert same(act(act(mirror,'r',e,sign),'s',e,sign),r3)
        print('PASS',branch,phase,'65610 coordinates',flush=True)
    print('fixture',branch,'multiplicity quarter',sp.trace(L),'half',sp.trace(L**2),'combined half',trace,flush=True)
print('PASS SymPy',sp.__version__,'conditional extended multiplicity fixtures; actual selection OPEN')
