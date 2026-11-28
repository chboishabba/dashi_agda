"""Same-clock fixed incident wave-port and phase-resolved actuator bus.
Discrete normalized chain, source termination r=1, not field calibration.
"""
import sympy as S
from solar_reciprocal_unfrozen_weld import exact
from solar_whole_boundary import candidate,direct_passive,bus_inverse

def replay(z,f,source_r,eta):
    r,eta=map(S.Rational,(source_r,eta));assert r>=0 and 0<=eta<=1
    B=S.Matrix([[1,-1,0],[0,1,-1]]);I=S.eye(6);D=S.diag(2,1,1+r)
    m=S.Rational(1,100000);c=S.Rational(1,10000);M=I;b=S.zeros(6,1);steps=[];n=len(f)
    p=[S.zeros(2,1)];dz=[z[(k+1)%n]-z[k] for k in range(n)]
    for k in range(n):
        K=S.eye(3)+B.T*S.diag(*((z[k]+z[(k+1)%n])/2))*B
        A=S.zeros(6);A[:3,3:]=S.eye(3);A[3:,:3]=-K;A[3:,3:]=-D
        L=(I-A/2).inv();T=L*(I+A/2);u=L*S.Matrix([0,0,0,0,0,f[k]])
        steps.append((T,u));M=T*M;b=T*b+u;p.append(2*dz[k]-p[-1])
    assert p[-1]==p[0];x=(I-M).inv()*b;start=x;W=[];N=Y=H=HA=inc=ref=S.Integer(0)
    def energy(x,z,p):
        e=B*x[:3,:];return (x.dot(x)+sum(z[j]*e[j]**2 for j in range(2))+m*p.dot(p))/2
    for k,(T,u) in enumerate(steps):
        y=T*x+u;v=(x[3:,:]+y[3:,:])/2;e0=B*x[:3,:];e1=B*y[:3,:];d=dz[k]
        R=S.Matrix([(a*a+b*b)/4 for a,b in zip(e0,e1)]);w=(m*(p[k+1]-p[k])+c*d+R).dot(d)
        nw=f[k]*v[2]-r*v[2]**2;yw=v[0]**2;hh=v.dot(v);ha=c*d.dot(d)
        assert energy(y,z[(k+1)%n],p[k+1])-energy(x,z[k],p[k])==nw+w-yw-hh-ha
        if r:
            a=f[k]/(2*S.sqrt(r));o=a-S.sqrt(r)*v[2];assert S.simplify(a*a-o*o-nw)==0;inc+=a*a;ref+=o*o
        W.append(w);N+=nw;Y+=yw;H+=hh;HA+=ha;x=y
    assert x==start
    buy=sum(max(0,w) for w in W);sell=sum(max(0,-w) for w in W);export=eta*sell-buy;out=Y+export
    assert N==out+H+HA+(1-eta)*sell
    if r:assert N==inc-ref
    return dict(output=out,receiver=Y,natural=N,buy=buy,sell=sell,export=export,work=W,incident=inc,reflected=ref,contraction=sum(a*a for a in M))

def run():
    z,f,old=candidate();eta=S.Rational(9,20);a=replay(z,f,0,eta)
    for k in ('output','receiver','natural','buy','sell','export','contraction'):assert a[k]==old[k]
    b=bus_inverse(a['work'],eta,S.Rational(1,100));assert b['export']==a['export']
    print('PASS original eight signed steps, capacitor return and local export stability',float(b['initial']),float(b['capacity']),float(b['local_radius']))
    r=replay(z,f,1,eta);ideal=replay(z,f,1,1);p=direct_passive(f,load=2,source_r=1)
    assert r['incident']==1 and 0<=r['reflected']<=1
    assert p['output']>ideal['output']>=r['output']
    print('PASS fixed incident wave boundary', {k:float(v) for k,v in r.items() if k!='work'},'ideal',float(ideal['output']),'passive',float(p['output']))
    # Same incident force profile and same source termination. Broad comparator
    # requires permitted lossless routing from source-port load to useful bus.
    # A stationary chain with fixed output port remains a separate comparator.
    static=replay([S.ones(2,1)]*len(f),f,1,eta)
    print('restricted stationary fixed load',float(static['output']),'active net margin',float(r['output']-static['output']))
    off=replay(z,[0]*len(f),1,eta);assert off['output']<0 and off['receiver']==0
if __name__=='__main__':run()
