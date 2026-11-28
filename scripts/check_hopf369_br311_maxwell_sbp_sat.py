"""BR311 original Hopf magnetic state into 3D Maxwell SBP-SAT flux energy.
Principal flat linear Maxwell only: no variable metric RMHD constraint-propagation
or nonlinear Einstein exterior wellposedness asserted.
"""
import argparse
import numpy as np
import check_hopf369_br283_284_g4_coupled as d
import check_hopf369_br310_sbp_source_boundary as ledger

def energy_derivative(E,B,DE,DB,W):
    return np.sum(W[...,None]*(E*DE+B*DB))

def run(n):
    g,v,U,dx=d.initial(n);D,h,_=ledger.sbp(n,dx)
    B=U[...,4:].copy()
    x=np.linspace(-1.5,1.5,n);X=np.stack(np.meshgrid(x,x,x,indexing='ij'),axis=-1)
    E=np.stack([X[...,1]*X[...,2]+.25,X[...,2]*X[...,0]-.1,X[...,0]*X[...,1]+.3],axis=-1)
    curl=lambda a:np.stack([ledger.derivative(a[...,2],D,1)-ledger.derivative(a[...,1],D,2),ledger.derivative(a[...,0],D,2)-ledger.derivative(a[...,2],D,0),ledger.derivative(a[...,1],D,0)-ledger.derivative(a[...,0],D,1)],axis=-1)
    DE=curl(B); DB=-curl(E)
    W=np.multiply.outer(np.multiply.outer(h,h),h)
    raw=energy_derivative(E,B,DE,DB,W)
    outward=0.;incoming=0.;outgoing=0.
    dE=np.zeros_like(E);dB=np.zeros_like(B)
    for axis in range(3):
        wh=np.multiply.outer(*[h for i in range(3) if i!=axis])
        for side,sgn in ((0,-1),(-1,1)):
            sl=[slice(None)]*3;sl[axis]=side;sl=tuple(sl)
            normal=np.zeros(3);normal[axis]=sgn
            ee=E[sl];bb=B[sl]
            q=np.cross(normal,bb);win=ee+q;wout=ee-q
            face_flux=np.einsum('...i,...i->...',np.cross(ee,bb),normal)
            outward+=np.sum(wh*face_flux)
            incoming+=np.sum(wh*np.sum(win*win,axis=-1))/4
            outgoing+=np.sum(wh*np.sum(wout*wout,axis=-1))/4
            # SAT with incoming projection; all edge/corner faces contribute.
            dE[sl]-=win/(2*h[side]);dB[sl]+=np.cross(normal,win)/(2*h[side])
    assert abs(raw+outward)<1e-10
    assert abs(outward-(outgoing-incoming))<1e-10
    sat=energy_derivative(E,B,DE+dE,DB+dB,W)
    expected=-incoming-outgoing
    assert abs(sat-expected)<1e-10 and sat<=1e-12
    # Wrong sign injection adds incoming power instead of dissipating it.
    wrong=energy_derivative(E,B,DE-dE,DB-dB,W)
    assert wrong>sat and incoming>0
    print('BR311',n,'original Hopf B and independent E SBP boundary flux',raw,outward,'incoming',incoming,'outgoing',outgoing,flush=True)
    print('BR311 passive SAT energy derivative',sat,'exact negative target',expected,'wrong-sign injected',wrong,'defect',abs(sat-expected),flush=True)
    print('BR311 OPEN curved ADM symmetrizer, physical exterior, induction div/SAT and Einstein constraints',flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);run(p.parse_args().n)
