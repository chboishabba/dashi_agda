"""Exact endpoint-first passive access and restored capacitor/bus inverse.
Normalized midpoint chain only. No measured material/source or converter law.
"""
import sympy as S
from solar_reciprocal_unfrozen_weld import exact

def candidate():
    z=[S.Matrix(r)/1000 for r in [[5,544],[394,744],[962,410],[949,69],[738,52],[185,974],[799,904],[976,123]]]
    f=[1,1,0,0,-1,-1,0,0]
    return z,f,exact(z,f,eta=S.Rational(9,20))

def direct_passive(f,load=1,source_r=0):
    # Existing unit onsite stiffness and intrinsic damping. An eligible broader
    # output class admits a local source-port damper with lossless bus transfer.
    l,r=map(S.Rational,(load,source_r)); assert l>0 and r>=0
    A=S.Matrix([[0,1],[-1,-(1+l+r)]]);I=S.eye(2)
    L=(I-A/2).inv();T=L*(I+A/2);b=S.zeros(2,1)
    for force in f:b=T*b+L*S.Matrix([0,force])
    x=(I-T**len(f)).inv()*b;start=x;N=Y=H=0
    for force in f:
        y=T*x+L*S.Matrix([0,force]);v=(x[1]+y[1])/2
        assert (y.dot(y)-x.dot(x))/2==force*v-(1+l+r)*v*v
        N+=force*v-r*v*v;Y+=l*v*v;H+=v*v;x=y
    assert x==start and N==Y+H
    return dict(output=Y,natural=N,efficiency=Y/N if N else 0)

def bus_inverse(work,eta,headroom=1,export_gain=S.Rational(1,2)):
    # J20-inspired capacitor energy coordinate; ideal reversible transfer map,
    # not a claim that J20's actual circuit implements these commands.
    eta,H,g=map(S.Rational,(eta,headroom,export_gain));assert 0<=eta<=1 and H>0 and 0<g<1
    inc=[eta*max(0,-w)-max(0,w) for w in work];p=[S.Integer(0)]
    for d in inc:p.append(p[-1]+d)
    export=p[-1];assert export>0
    start=H-min(p);E=[start+x for x in p]+[start]
    V=[S.sqrt(2*x) for x in E] # C=1
    for a,b,x,y in zip(V,V[1:],E,E[1:]):
        I=b-a;assert S.simplify((a+b)*I/2-(y-x))==0
    # Export feedback at the return event: export=nominal+g*energy error.
    error=S.symbols('error',real=True);assert S.expand(start+error+export-(export+g*error)-start)==(1-g)*error
    radius=min(H,export/g)/2;assert radius>0
    return dict(export=export,initial=start,capacity=max(E)+radius,local_radius=radius,return_multiplier=1-g)

def run():
    z,f,r=candidate();p=direct_passive(f)
    assert p['output']>r['output'] and p['efficiency']>r['output']/r['natural']
    assert p['efficiency']==S.Rational(1,2)
    # Even ideal recovery cannot beat this explicit wider passive witness.
    ideal=exact(z,f,eta=S.Integer(1));assert p['output']>ideal['output']
    # Aggregate buy/sell is sufficient for a two-tranche buffer existence test,
    # NOT the original phase-resolved chronology (retained by exact()).
    b=bus_inverse([-r['sell'],r['buy']],S.Rational(9,20))
    assert b['export']==r['export']
    print('PASS', 'active',float(r['output']),'active_eta1',float(ideal['output']),'direct_passive',float(p['output']),'passive_ratio',float(p['efficiency']),'bus_export',float(b['export']),'bus_multiplier',b['return_multiplier'])
    # Fixed force ceiling for all returned trajectories with source damping 1:
    # f*v-v² = f²/4-(v-f/2)². Source work excludes no actuator external funding.
    v,F=S.symbols('v F',real=True);assert S.expand(F*v-v*v-F*F/4+(v-F/2)**2)==0
    assert sum(x*x for x in f)/4==1
    print('PASS full-source-access outer cap 1; comparator eligibility is decisive')
if __name__=='__main__':run()
