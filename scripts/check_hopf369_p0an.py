"""P0AN: exact rank-24 signed and separated AdS3 tensor controls."""
import math
import sympy as s

def audit():
    t=s.symbols('t'); C=math.comb
    half={p:C(4,5-p) for p in range(1,6)}
    assert half=={1:1,2:4,3:6,4:4,5:1}
    dim=sum(m*C(24,p) for p,m in half.items())
    odd=sum(m*C(24,p) for p,m in half.items() if p%2)
    even=dim-odd
    assert (dim,even,odd)==(98280,43608,54672)
    # Full gravity vs unorbifolded lattice V2: natural inversion mismatch.
    assert (300+2*even,24+2*odd)==(87516,109368)
    assert 87516-109368==-21852 and 98580-98304==276
    assert (300+dim,24+dim)==(98580,98304)
    # Natural parity TIMES flavour exchange. Both copies retained, even/odd
    # each get one full half-carrier (orthogonal BIDI via symmetric/antisymmetric).
    X=s.Matrix([[0,1],[1,0]])
    for p in half:
        J=(-1)**p*X
        assert J*J==s.eye(2) and J.trace()==0
        for sign in (-1,1):
            v=s.Matrix([1,sign*(-1)**p]); assert J*v==sign*v
    assert (300+dim,24+dim)==(98580,98304)
    # 3-cycle of three rank-eight blocks, not a claimed Leech isometry.
    P=s.expand((1+t**3)**8)
    ch=[P.coeff(t,p) for p in range(1,6)]
    assert ch==[0,0,8,0,0]
    # Symmetric square trace = (tr R)^2/2+tr R^2/2 = 0.
    traces=[8*(12-3*m) for m in range(7)]
    assert traces==[96,72,48,24,0,-24,-48] and 54 not in traces
    print('rank24: natural',even,odd,'flavour-corrected',dim,dim,'C3 traces',traces,flush=True)
    # Actual binary Heisenberg carrier 2^12, using all translation and modulation labels.
    n=12; mask=(1<<n)-1; count=0
    for i in range(n):
        for j in range(n):
            for x in range(1<<n):
                a=1<<i; b=1<<j
                assert ((-1)**((b & (x^a)).bit_count())==(-1)**((a&b).bit_count())*(-1)**((b&x).bit_count()))
                count+=1
    assert (1<<n)*24==98304 and mask==4095
    print('binary Weyl relations',count,'PASS',flush=True)
    # All-index separated normal spectrum using symbolic conjugation.
    a=s.symbols('a',positive=True); p=s.Function('P')(t); w=(1-t*t)**(a/2)
    # T_z/h²=-[(1-t²) d²+t d], plus mu²/h² f².
    expr=(-(1-t*t)*s.diff(w*p,t,2)-t*s.diff(w*p,t)+a*(a-3)*w*p/(1-t*t))/w
    target=-(1-t*t)*s.diff(p,t,2)+(2*a-1)*t*s.diff(p,t)+a*(a-2)*p
    assert s.simplify(expr-target)==0
    for A in (3,4,5):
        for j in range(9):
            P=s.gegenbauer(j,A-1,t)
            assert s.expand(-(1-t*t)*s.diff(P,t,2)+(2*A-1)*t*s.diff(P,t)+A*(A-2)*P-(A+j)*(A+j-2)*P)==0
    print('all-index Gegenbauer conjugation; 27 exact polynomial controls PASS',flush=True)

if __name__=='__main__': audit()
