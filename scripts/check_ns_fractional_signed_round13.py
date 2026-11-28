"""Exact controls for weighted physical derivative and quarter interpolation."""
import importlib.util
from pathlib import Path
from random import Random
from fractions import Fraction as Q
if not __debug__:raise SystemExit('refusing optimized execution')
p=Path(__file__).with_name('check_ns_diagonal_convolution_round13.py')
s=importlib.util.spec_from_file_location('carrier',p);c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
def inner(u,v):return sum(a*d+b*e for (a,b),(d,e) in zip(u,v))
def main():
    rng=Random(36914);count=0;nonzero=0
    for _ in range(12):
        U=c.make(1,rng);F={k:c.force(k,U) if k!=c.O else c.V0 for k in U}
        for _ in range(12):
            w={k:Q(rng.randrange(0,10),7) for k in U};nu=Q(rng.randrange(1,5),7)
            E=sum(w[k]*c.mass(u) for k,u in U.items())
            D=sum(w[k]*c.m2(k)*c.mass(u) for k,u in U.items())
            P=2*sum(w[k]*inner(F[k],u) for k,u in U.items())
            d={k:c.vsum(c.vscale(u,-nu*c.m2(k)),F[k]) for k,u in U.items()}
            rate=2*sum(w[k]*inner(d[k],u) for k,u in U.items())
            assert rate==P-2*nu*D;count+=1
            assert 2*E*rate==2*E*P-4*nu*E*D;count+=1
            nonzero+=P!=0
    assert nonzero>0;count+=1
    for _ in range(1000):
        m=[Q(rng.randrange(0,30),17) for _ in range(16)]
        r=[j*j for j in range(1,17)]
        E=sum(m);H=sum(a*b for a,b in zip(r,m));D=sum(a*a*b for a,b in zip(r,m))
        A=sum(j*b for j,b in enumerate(m,1))
        assert A*A<=E*H;count+=1
        assert H*H<=E*D;count+=1
        assert A**4<=E**3*D;count+=1
    print(f'{count}/{count} weighted signed and quarter controls PASS; nonzero transfer {nonzero}')
if __name__=='__main__':main()
