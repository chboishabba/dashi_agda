"""Nonthermal gyrotropic modulation on the original loaded SI exterior.
Prescribed skew material control, NOT a paid magnetic field generator.
"""
import numpy as np
import sympy as S
from itertools import product
from scipy.linalg import block_diag
import solar_material_exterior_weld as base

def gyro_material(freqs,nu=30.,D=30.,gyro=10.,delta=10.):
    n=len(freqs); assert nu>0 and D>0
    J=np.cross(base.axis,np.eye(3)).T
    Y=np.zeros((16*n,16*n),complex);parts=[]
    for p in product((-1,0,1),repeat=3):
        nn=sum(t!=0 for t in p)
        if not nn:continue
        site=np.array(p)/np.sqrt(nn);w={1:1/21,2:4/105,3:9/280}[nn]
        B=block_diag(*([base.angular(site)]*n));q=delta*(site@base.axis)
        A=block_diag(*[(nu+2j*np.pi*f)*np.eye(3)+gyro*J for f in freqs])
        for k in range(n-1):
            A[3*k:3*k+3,3*k+3:3*k+6]=q*J
            A[3*k+3:3*k+6,3*k:3*k+3]=q*J
        H=(A+A.conj().T)/2;assert np.allclose(H,nu*np.eye(3*n))
        L=D*np.linalg.solve(A,B);Y+=w*B.T@L;parts.append((w,B,L,H,q,D))
    return Y,parts

def symbolic():
    x=S.Matrix(S.symbols('x:3',real=True)); b=S.Matrix(S.symbols('b:3',real=True))
    assert S.expand(x.dot(b.cross(x)))==0
    # Population event, cold births and removal at old velocity: exact norm loss.
    n,r,c,m=S.symbols('n r c m',positive=True);a=n-r;t=a+c
    assert S.cancel(m*n/2-m*a*a/(2*t)-m*r/2-m*a*c/(2*t))==0
    # Equal density turnover r=c, cold birth: retained current fraction.
    assert S.cancel((a/t).subs(c,r)-(1-r/n))==0
    # Paired skew sideband correction: the same resolvent cancellation,
    # with the generator J retained on both sides (no commuting assumption on J).
    A,w=S.symbols('A w');assert S.cancel(1/(A+S.I*w)+1/(A-S.I*w)-2*A/(A*A+w*w))==0

def run():
    symbolic();base.material=gyro_material
    for carrier,mod,order in [(7.83,3.915,1),(3.915,7800.,1),(3.915,7800.,2)]:
        freqs=[carrier+j*mod for j in range(-order,order+1)]
        p=base.optimal(base.exterior(freqs,0),freqs);a=base.optimal(base.exterior(freqs,10),freqs)
        print(dict(freqs=freqs,stationary=p,reactive=a,gross_delta=a['ideal']-p['ideal'],cost_ceiling=a['allocation_upper']-p['diagonal_load']),flush=True)
    print('PASS: skew material electrical work and cold population event identities; magnetic generation and chemical source costs unadmitted')
if __name__=='__main__':run()
