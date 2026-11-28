"""Exact same-clock discrete gradient and rational eight-node candidate.
Uses normalized chain geometry, not measured actuator or HF material.
"""
import sympy as S
B=S.Matrix([[1,-1,0],[0,1,-1]]);D=S.diag(2,1,1);I=S.eye(6)

def exact(z,forces,dt=S.Integer(1),m=S.Rational(1,100000),c=S.Rational(1,10000),eta=S.Rational(3,10),load=S.Integer(1)):
    n=len(z); assert len(forces)==n and all(0<=a<=1 for x in z for a in x)
    M=I;b=S.zeros(6,1);steps=[];dd=S.diag(1+load,1,1)
    for k in range(n):
        K=S.eye(3)+B.T*S.diag(*((z[k]+z[(k+1)%n])/2))*B
        A=S.zeros(6);A[:3,3:]=S.eye(3);A[3:,:3]=-K;A[3:,3:]=-dd
        L=(I-dt*A/2).inv();T=L*(I+dt*A/2);u=L*S.Matrix([0,0,0,0,0,dt*forces[k]])
        steps.append((T,u));M=T*M;b=T*b+u
    x=(I-M).inv()*b;initial=x; p=[S.zeros(2,1)];dz=[z[(k+1)%n]-z[k] for k in range(n)]
    for d in dz:p.append(2*d/dt-p[-1])
    assert p[0]==p[-1]
    def energy(x,z,p):
        e=B*x[:3,:];return (x.dot(x)+sum(z[j]*e[j]**2 for j in range(2))+m*p.dot(p))/2
    N=Y=H=HA=S.Integer(0);work=[]
    for k,(T,u) in enumerate(steps):
        y=T*x+u;v=(x[3:,:]+y[3:,:])/2;e0=B*x[:3,:];e1=B*y[:3,:];vm=dz[k]/dt;dp=p[k+1]-p[k]
        R=S.Matrix([(a*a+b*b)/4 for a,b in zip(e0,e1)]);force=m*dp/dt+c*vm+R
        W=force.dot(dz[k]);ha=dt*c*vm.dot(vm);nw=dt*forces[k]*v[2];yw=dt*load*v[0]**2;hh=dt*v.dot(v)
        assert energy(y,z[(k+1)%n],p[k+1])-energy(x,z[k],p[k])==nw+W-yw-hh-ha
        work.append(W);N+=nw;Y+=yw;H+=hh;HA+=ha;x=y
    assert x==initial
    buy=sum(max(0,w) for w in work);sell=sum(max(0,-w) for w in work);export=eta*sell-buy;out=Y+export
    assert N==out+H+HA+(1-eta)*sell
    prefix=[S.Integer(0)]
    for w in work:prefix.append(prefix[-1]+eta*max(0,-w)-max(0,w))
    assert prefix[-1]==export
    capacity=max(prefix)-min(prefix) if export>=0 else None
    return dict(output=out,receiver=Y,natural=N,buy=buy,sell=sell,export=export,heat=HA,capacity=capacity,contraction=sum(a*a for a in M))

def run():
    e0,e1,z0,z1=S.symbols('e0 e1 z0 z1');assert S.expand((z0+z1)*(e0+e1)*(e1-e0)/4+(e0**2+e1**2)*(z1-z0)/4-(z1*e1**2-z0*e0**2)/2)==0
    f=[1,1,0,0,-1,-1,0,0]
    rows=[[5,544],[394,744],[962,410],[949,69],[738,52],[185,974],[799,904]]
    z=[S.Matrix(r)/1000 for r in rows];z.append(sum(((-1)**k*v for k,v in enumerate(z)),S.zeros(2,1)))
    r=exact(z,f);base=exact([S.ones(2,1)]*8,f);off=exact(z,[0]*8)
    assert r['contraction']<1 and r['export']>0 and r['output']<base['output']
    assert off['receiver']==0 and off['export']<0
    print('nodes',z[-1]);print('candidate', {k:float(v) for k,v in r.items()});print('stationary',float(base['output']));print('source off',float(off['output']));print('PASS exact restored unfrozen ledger; gain NOT established')
if __name__=='__main__':run()
