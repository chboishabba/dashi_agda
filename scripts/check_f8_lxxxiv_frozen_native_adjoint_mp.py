"""LXXXIV independent frozen-native floating-adjoint regression.

Probe original SSPRK3 homogeneous Euler operators into binary64 matrices and
hold those coefficient bits fixed. A 70-digit reference calculates forward and
transpose responses to 12 unit source cells, for each of 18 receiver/mode rows.
This is not a certified rounding bound on the original operator assembly.
Run local only; do not run GitHub CI.
"""
import argparse,json
import numpy as np
import mpmath as mp
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import stage,F
from warp_stage_adjoint import transpose
from warp_native_geometric_receiver import receiver_bank
from warp_frame_attribution import project
mp.mp.dps=70

def check(order,mode,channel,N=4):
    dr,dy,h,eps=.008,.012,.001,.04;nr,ny=13,7;rx=.073
    ts=np.array([brentq(lambda t:F(t)-F(1)-.02-k*h/2,.5,3) for k in range(2*N+1)])
    b=1/ts;v=-1/np.sqrt(1+ts**2)
    incidence=[(2*i,2*i+2,2*i+1) for i in range(N)]
    shape=(3,3,ny,nr);coords=[(c,mode,y,r) for c in range(3) for y in range(ny) for r in range(nr-1)]
    size=len(coords);eye=np.eye(size)
    cp=np.zeros((3,nr));cm=cp.copy()
    for q,d in enumerate((3,7,11)):
        j=np.arange(1,nr);den=(j+.5)**d-(j-.5)**d
        cp[q,1:]=d*(j+.5)**(d-1)/den;cm[q,1:]=d*(j-.5)**(d-1)/den
    def pack(z):return np.array([z[t] for t in coords])
    def unpack(w):
        z=np.zeros(shape)
        for j,t in enumerate(coords):z[t]=w[j]
        return z
    def E(z,k,source=None):
        src=np.zeros((3,nr));amp=0.
        if source is not None:src[mode,source]=1.;amp=amps[k]
        out=np.zeros(shape)
        stage(*z,*out,dr,dy,b[k],v[k],amp,src,cp,cm,order)
        return project(z+h*out)
    amps=np.sin(np.arange(2*N+1)+.3)*.02
    maps=[np.column_stack([pack(E(unpack(eye[j]),k)) for j in range(size)])
          for k in range(2*N+1)]
    sparse=[]
    for M in maps:
        sparse.append([[(int(j),mp.mpf(float(M[i,j]))) for j in np.flatnonzero(M[i])]
                       for i in range(size)])
    def mv(A,x):return [sum((c*x[j] for j,c in row),mp.mpf(0)) for row in A]
    def mtv(A,x):
        z=[mp.mpf(0)]*size
        for i,row in enumerate(A):
            if not x[i]:continue
            for j,c in row:z[j]+=c*x[i]
        return z
    def add(a,b):return [x+y for x,y in zip(a,b)]
    def mul(a,c):return [x*c for x in a]
    third=mp.mpf(1)/3;two=mp.mpf(2)/3
    amps_mp=[mp.mpf(float(t)) for t in amps]
    obs_bank=receiver_bank(ts[2*(N-1)],rx,eps,dr,dy,h,v,N-1,nr,ny)
    obs=np.zeros((N+1,size));fullobs=np.zeros((N+1,*shape))
    for slot in range(3):
        obs[N-2+slot]=pack(obs_bank[channel,slot])
        fullobs[N-2+slot]=obs_bank[channel,slot]
    ob=[[mp.mpf(float(x)) for x in row] for row in obs]
    # Reference reverse: A insert B^T C^T p/6, B insert C^T p/6,
    # C insert 2p/3. All computational stages retain separate identities.
    p=ob[-1];sensitivity=[mp.mpf(0)]*size
    for i in range(N-1,-1,-1):
        a,B,c=incidence[i];ct=mtv(sparse[c],p)
        dB=mul(ct,mp.mpf(1)/6);dA=mtv(sparse[B],dB)
        sensitivity=add(sensitivity,add(mul(dA,amps_mp[a]),
            add(mul(dB,amps_mp[B]),mul(p,two*amps_mp[c]))))
        p=add(add(mul(p,third),mul(ct,mp.mpf(1)/2)),
              add(mtv(sparse[a],dA),ob[i]))
    # Original native transpose, from independent production owner.
    pn=project(fullobs[-1]);kn=np.zeros(nr)
    def T(z,k):return project(z+h*transpose(z,dr,dy,b[k],v[k],order))
    for i in range(N-1,-1,-1):
        a,B,c=incidence[i]
        pc=2*T(pn,c)/3;pb=T(pc,B)/4
        for j in range(nr-1):
            kn[j]+=(-4*h/dy)*(amps[a]*pb[2,mode,0,j]
               +amps[B]*(pc/4)[2,mode,0,j]+amps[c]*(2*pn/3)[2,mode,0,j])
        pn=project(pn/3+3*pc/4+T(pb,a))+project(fullobs[i])
    defects=[];ferr=[];rerr=[]
    for j in range(nr-1):
        u=[mp.mpf(0)]*size;u[coords.index((2,mode,0,j))]=mp.mpf(float(-4*h/dy))
        x=[mp.mpf(0)]*size;states=[x]
        for a,B,c in incidence:
            xx=add(mv(sparse[a],x),mul(u,amps_mp[a]))
            z=add(mul(x,mp.mpf(3)/4),
                  mul(add(mv(sparse[B],xx),mul(u,amps_mp[B])),mp.mpf(1)/4))
            x=add(mul(x,third),mul(add(mv(sparse[c],z),mul(u,amps_mp[c])),two))
            states.append(x)
        ref=sum((v*w for z,w in zip(states,ob) for v,w in zip(z,w)),mp.mpf(0))
        dual=sum((v*w for v,w in zip(sensitivity,u)),mp.mpf(0))
        defects.append(abs(ref-dual))
        # Independent actual original native stage and actual receiver.
        x=np.zeros(shape);states=[x]
        for a,B,c in incidence:
            u0=E(x,a,j);z=.75*x+.25*E(u0,B,j)
            x=x/3+2*E(z,c,j)/3;states.append(x)
        f=sum(np.sum(obs_bank[channel,k]*states[N-2+k]) for k in range(3))
        ferr.append(abs(mp.mpf(float(f))-ref))
        rerr.append(abs(mp.mpf(float(kn[j]))-ref))
    assert max(defects)<mp.mpf('1e-58')
    return {'order':order,'mode':mode,'channel':channel,
      'exact_frozen_parity':float(max(defects)),
      'native_forward_drift':float(max(ferr)),
      'native_reverse_drift':float(max(rerr)),
      'authority':'70-digit frozen binary64 matrix, not original coefficient-rounding certification'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--order',type=int,required=True)
    args=p.parse_args();result=[]
    for mode in range(3):
        for channel in range(6):
            r=check(args.order,mode,channel);result.append(r)
            print(json.dumps(r),flush=True)
    print('PASS',args.order,len(result),flush=True)
