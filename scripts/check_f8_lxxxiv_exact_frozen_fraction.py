"""LXXXIVb exact-rational frozen-native SSPRK3 forward/adjoint fixture.
The stage and observation coefficients are probed in binary64, converted
exactly to fractions, and the finite source response is then computed with
exact rational forward and backward arithmetic. This is NOT a certificate
for production stage-coefficient construction or arbitrary floating runs.
"""
import argparse,json,time
from fractions import Fraction as Q
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import stage,F
from warp_native_geometric_receiver import receiver_bank
from warp_frame_attribution import project

def audit(order,mode,channel,jsource=4,N=4):
    start=time.monotonic()
    dr,dy,h,eps=.008,.012,.001,.04
    nr,ny=13,7;rx=.073;shape=(3,3,ny,nr)
    times=np.array([brentq(lambda t:F(t)-F(1)-.02-k*h/2,.5,3) for k in range(2*N+1)])
    b=1/times;v=-1/np.sqrt(1+times*times)
    amps=np.sin(np.arange(2*N+1)+.3)*.02
    inc=[(2*i,2*i+2,2*i+1) for i in range(N)]
    coords=[(c,mode,y,r) for c in range(3) for y in range(ny) for r in range(nr-1)]
    size=len(coords)
    cp=np.zeros((3,nr));cm=cp.copy()
    for q,dim in enumerate((3,7,11)):
        j=np.arange(1,nr);den=(j+.5)**dim-(j-.5)**dim
        cp[q,1:]=dim*(j+.5)**(dim-1)/den
        cm[q,1:]=dim*(j-.5)**(dim-1)/den
    def pack(z):return np.array([z[t] for t in coords])
    def unpack(x):
        z=np.zeros(shape)
        for i,t in enumerate(coords):z[t]=x[i]
        return z
    def euler(x,k,amp=0.):
        src=np.zeros((3,nr));src[mode,jsource]=1
        out=np.zeros(shape)
        stage(*x,*out,dr,dy,b[k],v[k],amp,src,cp,cm,order)
        return project(x+h*out)
    basis=np.eye(size);mat=[]
    for k in range(2*N+1):
        raw=np.column_stack([pack(euler(unpack(z),k)) for z in basis])
        mat.append([[(int(j),Q(float(raw[i,j]))) for j in np.flatnonzero(raw[i])]
                    for i in range(size)])
    def mv(M,x):return [sum((c*x[j] for j,c in row),Q(0)) for row in M]
    def mtv(M,x):
        out=[Q(0)]*size
        for i,row in enumerate(M):
            if not x[i]:continue
            for j,c in row:out[j]+=c*x[i]
        return out
    def add(a,b):return [x+y for x,y in zip(a,b)]
    def mul(a,c):return [x*c for x in a]
    obsbank=receiver_bank(times[2*(N-1)],rx,eps,dr,dy,h,v,N-1,nr,ny)
    obs=[[Q(0)]*size for _ in range(N+1)]
    for slot in range(3):
        obs[N-2+slot]=[Q(float(z)) for z in pack(obsbank[channel,slot])]
    inject=[Q(0)]*size
    inject[coords.index((2,mode,0,jsource))]=Q(float(-4*h/dy))
    amplitudes=[Q(float(t)) for t in amps]
    x=[Q(0)]*size;states=[x]
    for a,B,c in inc:
        u=add(mv(mat[a],x),mul(inject,amplitudes[a]))
        z=add(mul(x,Q(3,4)),mul(add(mv(mat[B],u),mul(inject,amplitudes[B])),Q(1,4)))
        x=add(mul(x,Q(1,3)),mul(add(mv(mat[c],z),mul(inject,amplitudes[c])),Q(2,3)))
        states.append(x)
    reference=sum((a*b for x,y in zip(states,obs) for a,b in zip(x,y)),Q(0))
    p=obs[-1];grad=[Q(0)]*size
    for i in range(N-1,-1,-1):
        a,B,c=inc[i];ct=mtv(mat[c],p)
        dB=mul(ct,Q(1,6));dA=mtv(mat[B],dB)
        grad=add(grad,add(mul(dA,amplitudes[a]),add(mul(dB,amplitudes[B]),mul(p,Q(2,3)*amplitudes[c]))))
        p=add(add(mul(p,Q(1,3)),mul(ct,Q(1,2))),add(mtv(mat[a],dA),obs[i]))
    reverse=sum((a*b for a,b in zip(grad,inject)),Q(0))
    assert reference==reverse
    x=np.zeros(shape);statesf=[x]
    for a,B,c in inc:
        u=euler(x,a,amps[a])
        z=.75*x+.25*euler(u,B,amps[B])
        x=x/3+2*euler(z,c,amps[c])/3
        statesf.append(x)
    native=float(sum(np.sum(obsbank[channel,k]*statesf[N-2+k]) for k in range(3)))
    delta=abs(Q(native)-reference)
    return dict(order=order,mode=mode,channel=channel,source_cell=jsource,
        exact_frozen_forward_adjoint='PASS exact Fraction equality',
        max_native_float_vs_exact_frozen=float(delta),
        frozen_receiver=float(reference),native_receiver=native,
        exact_discrepancy_numerator_bits=delta.numerator.bit_length(),
        exact_discrepancy_denominator_bits=delta.denominator.bit_length(),
        seconds=time.monotonic()-start,
        scope='Finite frozen binary64 matrix only, not a prospective or stage coefficient rounding bound')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--order',type=int,required=True)
    p.add_argument('--mode',type=int,default=None);p.add_argument('--channel',type=int,default=None)
    p.add_argument('--cell',type=int,default=4)
    a=p.parse_args()
    rows=[]
    for q in (range(3) if a.mode is None else (a.mode,)):
        for ch in (range(6) if a.channel is None else (a.channel,)):
            r=audit(a.order,q,ch,a.cell);rows.append(r)
            print(json.dumps(r),flush=True)
    print('PASS',a.order,len(rows),max(x['max_native_float_vs_exact_frozen'] for x in rows))
