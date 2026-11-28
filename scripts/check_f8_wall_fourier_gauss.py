"""Original short-slab wall Fourier Gauss source; no controller or coupled solution.
Uses characteristic wall history and independent field normal derivative.
Ordered Fourier products use no conjugation; signed k=0 retained.
"""
import numpy as np
from scipy.interpolate import CubicSpline
from scipy.special import roots_legendre
from check_f8_characteristic_history import evolve, coefficient, bump


def spatial(p,H,q,G):
    def conn(k,A):
        return np.array([[[1j*(k[i]*A[a,j]+k[j]*A[a,i]-k[a]*A[i,j])/2
                           for j in range(3)] for i in range(3)] for a in range(3)])
    C,D=conn(p,H),conn(q,G)
    V=-np.einsum('al,lij->aij',H,D); k=p+q
    R=1j*(np.einsum('a,aij->ij',k,V)-np.einsum('j,aia->ij',k,V))
    R+=np.einsum('aal,lij->ij',C,D)-np.einsum('ajl,lia->ij',C,D)
    R1=1j*(np.einsum('a,aij->ij',q,D)-np.einsum('j,aia->ij',q,D))
    return np.trace(R-H@R1)


def ordered(p,A,q,B,t):
    H,Ht,Htt,Hn,P=A; G,Gt,Gtt,Gn,Q=B
    # P,Q are actual first-order stress (charge included).
    e=Hn/2+3*P; d=Gn/2+3*Q
    R=spatial(p,H,q,G)/t**2-np.trace(H@Gtt)-.75*np.trace(Ht@Gt)-4/t*np.trace(H@Gt)
    K1=Hn/2; L1=Gn/2
    gauss=-np.trace(K1@L1)
    expanded=-9*np.trace(P@Q)+3*np.trace(P@d+e@Q)-np.trace(e@d)
    assert np.allclose(gauss,expanded,rtol=1e-10,atol=1e-12)
    return np.array([R,gauss,-9*np.trace(P@Q),np.trace(e@d),np.trace(H@G),np.trace(Ht@Gt)],complex)


def quadrature(k,cutoff,nodes):
    a,w=roots_legendre(nodes); ph=2*np.pi*np.arange(16)/16
    if k==0:
        for p,wp in zip(cutoff*(a+1)/2,cutoff*w/2):
            for c,wc in zip(a,w):
                for phi in ph:
                    v=p*np.array([c,np.sqrt(1-c*c)*np.cos(phi),np.sqrt(1-c*c)*np.sin(phi)])
                    yield v,-v,wp*wc*p*p/(4*np.pi**2*len(ph))
        return
    # split radial intervals at triangle changes for better quadrature
    edges=sorted(set([0.,cutoff]+[v for v in (k,cutoff-k,k-cutoff) if 0<v<cutoff]))
    for lo,hi in zip(edges,edges[1:]):
        for p,wp in zip(lo+(hi-lo)*(a+1)/2,(hi-lo)*w/2):
            low=abs(k-p); high=min(k+p,cutoff)
            if high<=low:continue
            for q,wq in zip(low+(high-low)*(a+1)/2,(high-low)*w/2):
                c=(k*k+p*p-q*q)/(2*k*p); r=p*np.sqrt(max(0.,1-c*c))
                for phi in ph:
                    v=np.array([p*c,r*np.cos(phi),r*np.sin(phi)])
                    yield v,np.array([k,0.,0.])-v,wp*wq*p*q/(4*np.pi**2*k*len(ph))


def run(cells=128,nh=16,nodes=4,cutoff=80,t=1.035):
    kh=cutoff*(1-np.cos(np.linspace(0,np.pi,nh)))/2; ci=coefficient(kh)
    # Run past evaluation time so spline uses actual two-sided history.
    times,_,_,H,Ht,_=evolve(kh,ci,cells,t+.004)
    hs=CubicSpline(times,H,axis=0); vs=CubicSpline(times,Ht,axis=0)
    # Independent normal derivative from field values, not enforced characteristic V.
    dn=.5/cells; vals=[evolve(kh,ci,cells,t,sample_n=j*dn)[-1][:,0] for j in (1,2)]
    wall=evolve(kh,ci,cells,t)[3][-1]
    normal=(-3*wall+4*vals[0]-vals[1])/(2*dn)
    fields=np.stack([hs(t),vs(t),vs(t,1),normal,ci*bump(t)],axis=1)
    interp=CubicSpline(kh,fields,axis=0)
    axis=np.array([1.,2.,3.]);axis/=np.linalg.norm(axis);v=np.cross(axis,[0.,0.,1.]);v/=np.linalg.norm(v);rot=np.column_stack((axis,v,np.cross(axis,v))); seed=rot.T@np.diag([0.,1.,-1.])@rot
    def mode(p):
        r=np.linalg.norm(p); P=np.eye(3)-np.outer(p,p)/r**2; E=P@seed@P-P*np.trace(P@seed)/2
        return interp(r)[:,None,None]*E
    rows=[]
    for k in (0.,30.):
        result=np.zeros(6,complex); symmetry=0.
        for p,q,w in quadrature(k,cutoff,nodes):
            A,B=mode(p),mode(q); a=ordered(p,A,q,B,t); b=ordered(q,B,p,A,t)
            result+=w*(a+b)/2
        assert np.all(np.isfinite(result)) and np.max(abs(result.imag))<1e-10
        assert result[3].real>=-1e-10 if k==0 else True
        rows.append(result.real.tolist())
        print('cells,nh,nodes,k',cells,nh,nodes,k,'Rtt,Gauss,ideal,defect-square,HH,HtHt',result.real.tolist(),flush=True)
    print('wall time jet discrepancy',np.max(abs(hs(t,1)-vs(t))),flush=True)
    return rows

if __name__=='__main__':
    run();run(cells=256,nh=24,nodes=6)
