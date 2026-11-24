"""H05 six-face signed residual intervention cube on actual F8 receiver rows.
Diagnostic, not a physical evolution commutation theorem.
"""
import itertools
import numpy as np
from warp_native_geometric_receiver import receiver_bank, check_identity
from warp_israel_affine import radial_source_at_receiver, offsets, forced_identity

def cube(states, vel, obs, source_offset):
    # states: three same-grid time slots, six channels U,P,M,R,J,K.
    # Interventions retain U,W and subtract selected signed normal histories.
    X=np.asarray(states)
    if X.ndim!=5 or X.shape[:3]!=(3,6,3) or len(vel)!=3:
        raise ValueError('three indexed six-channel snapshots required')
    base=X[:,:3].copy()
    def edge(x,a,sign=-1):
        y=x.copy()
        for i,v in enumerate(vel):
            c=sign*X[i,3+a]
            y[i,1]+=(1-v)*c; y[i,2]-=(1+v)*c
        return y
    def observe(x):
        # retain modes; affine source offset applied exactly once
        return np.einsum('csiqyr,siqyr->cq',obs,x)+offsets(source_offset)
    def equal(a,b):
        np.testing.assert_allclose(a,b,rtol=1e-10,atol=1e-10)
    vertices={bits:base.copy() for bits in itertools.product((0,1),repeat=3)}
    for bits in vertices:
        for a in range(3):
            if bits[a]:vertices[bits]=edge(vertices[bits],a)
    faces={}
    for a,b in itertools.combinations(range(3),2):
        c=3-a-b
        for side in (0,1):
            bits=[0,0,0];bits[c]=side;x=vertices[tuple(bits)]
            left=edge(edge(x,a),b);right=edge(edge(x,b),a)
            equal(left,right);equal(observe(left),observe(right))
            faces[f'{a}{b}@{c}={side}']=float(np.max(abs(left-right)))
    paths={}
    for perm in itertools.permutations(range(3)):
        x=base.copy()
        for a in perm:x=edge(x,a)
        equal(x,vertices[(1,1,1)])
        for a in reversed(perm):x=edge(x,a,1)
        equal(x,base);paths[str(perm)]=True
    values={str(bits):observe(x) for bits,x in vertices.items()}
    # At zero-initial constraint ledger Q=R+J+K, the last vertex has
    # zero unweighted Q. This is an intervention, not a solution.
    return faces,paths,values

def main():
    rng=np.random.default_rng(369)
    t=12.;rx=.053;eps=.04;dr=.008;dy=.012;h=.001;nt=2;nr=13;ny=7
    velocities=-1/np.sqrt(1+np.linspace(t-.001,t+.001,7)**2)
    vel=velocities[[2,4,6]]
    obs=receiver_bank(t,rx,eps,dr,dy,h,velocities,nt,nr,ny)
    check_identity(obs,t)
    X=rng.normal(size=(3,6,3,ny,nr))*1e-4
    X[:,:,:,:,-1]=0
    src=np.zeros((3,nr));src[:,5:8]=rng.normal(size=(3,3))
    g=radial_source_at_receiver(src,.013,rx,eps,dr)
    faces,paths,values=cube(X,vel,obs,g)
    for val in values.values():
        err,scale=forced_identity(val,g,t)
        assert np.all(abs(err)<=1e-10*np.maximum(1.,scale))
    print('six faces, six reversible paths, eight original geometric observer packets PASS')
if __name__=='__main__':main()
