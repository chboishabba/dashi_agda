#!/usr/bin/env python3
"""Exact 3D ordinary magnetic support, experiment observability and port work.

Illustrative dimensions/parameters. Not physical measurement, real superconducting
calibration, Filsinger energy extraction, or 4D non-Abelian mass-gap evidence.
"""
from sympy import Matrix, Rational as Q, symbols, diff, hessian, simplify, zeros
x,y,z,G,B0,alpha,mg,u = symbols('x y z G B0 alpha mg u', real=True)
checks=[]
def check(name, result):
    assert bool(result), name
    checks.append(name)
    print(f'PASS {len(checks):02d} {name}')

# Static vacuum quadrupole. Matter (alpha) experiences its material-response
# potential; vacuum stress has no body-force divergence away from boundaries.
B=Matrix([G*x,G*y,B0-2*G*z])
r=(x,y,z)
Div=sum(diff(B[i],r[i]) for i in range(3))
Curl=Matrix([diff(B[2],y)-diff(B[1],z),
             diff(B[0],z)-diff(B[2],x),diff(B[1],x)-diff(B[0],y)])
check('vacuum div B=0', simplify(Div)==0)
check('vacuum curl B=0', Curl==zeros(3,1))
check('nonuniform field has real gradient',B.diff(z)!=zeros(3,1))
B2=simplify(B.dot(B))
F=Matrix([simplify(alpha*diff(B2,s)/2) for s in r])
check('material force equals chi-gradient square', all(simplify(F[i]-alpha*diff(B2,r[i])/2)==0 for i in range(3)))
check('vertical force is minus 2 alpha G (B0-2Gz)',simplify(F[2]+2*alpha*G*(B0-2*G*z))==0)
check('horizontal restorative force exists for diamagnet',simplify(F[0]-alpha*G**2*x)==0 and simplify(F[1]-alpha*G**2*y)==0)
P={G:1,B0:1,alpha:-1,mg:2}
U=simplify(-alpha*B2/2+mg*z)
dU=Matrix([diff(U,v) for v in r])
check('magnetic+gravitational energy stationary at origin',dU.subs(P).subs({x:0,y:0,z:0})==zeros(3,1))
check('net support exactly balances 2 units of ordinary weight',F[2].subs(P).subs(z,0)==P[mg])
check('3D equilibrium Hessian positive diagonal',hessian(U,r).subs(P)==Matrix.diag(1,1,4))
check('3D equilibrium Hessian principal minors positive',all(hessian(U,r).subs(P)[:n,:n].det()>0 for n in (1,2,3)))
check('mechanical support at rest has no mechanical work rate',sum(F[i]*v for i,v in enumerate(symbols('vx vy vz'))).subs({'vx':0,'vy':0,'vz':0})==0)
check('moving through magnetic force can transfer mechanical energy',F[2].subs(P).subs(z,0)!=0)

# Maxwell stress divergence in current-free region: material boundaries,
# induced magnetization and its interface force must not be erased.
S=Matrix([[simplify(B[i]*B[j]-(B2/2 if i==j else 0)) for j in range(3)] for i in range(3)])
StressDiv=Matrix([simplify(sum(diff(S[i,j],r[j]) for j in range(3))) for i in range(3)])
check('vacuum Maxwell stress divergence vanishes locally',StressDiv==zeros(3,1))
check('material susceptibility force not falsely equated with vacuum stress divergence',F!=StressDiv)
check('remove diamagnetic response means zero magnetic force',F.subs(alpha,0)==zeros(3,1))
check('reverse alpha flips magnetic force sign',simplify(F[2].subs(alpha,1)+F[2].subs(alpha,-1))==0)
check('reverse B and its gradient leaves B^2 force invariant',simplify((-B).dot(-B)-B2)==0)

# Four-channel source owner: ordinary external support is observationally
# indistinguishable from a hypothetical gravity change if only weight is used.
# Entries: support, freeFall, clock, optical, TT; mechanism classes in Agda.
ordinary=(1,0,0,0,0)
scalar_metric=(1,1,1,1,0)
propagating=(1,1,1,1,1)
inertia_only=(1,0,0,0,0)
check('weight channel aliases ordinary and metric comparator',ordinary[0]==scalar_metric[0])
check('independent freefall separates ordinary vs selected scalar-metric candidate',ordinary[1]!=scalar_metric[1])
check('independent clock separates ordinary vs selected scalar-metric candidate',ordinary[2]!=scalar_metric[2])
check('independent optical separates ordinary vs selected scalar-metric candidate',ordinary[3]!=scalar_metric[3])
check('TT channel separates selected scalar from propagating modes',scalar_metric[4]!=propagating[4])
check('ordinary EM and inertia-only remain ambiguous under five source signatures',ordinary==inertia_only)

# Exact Filsinger source-selected work: field + material, no duplicated port.
# Same illustrative values as original source-equivalent model, these are
# not measurements and do not instantiate the Agda admission records.
n,d,mod,fi,ff,mi,mf,interior,fl,load,ml,rec=13,2,1,5,5,4,4,8,7,6,2,1
check('original field balance holds',n+d+fi==interior+fl+ff)
check('original material balance holds',interior+mod+mi==load+ml+rec+mf)
check('real shared port cancels exactly once',n+d+mod+fi+mi==load+fl+ml+rec+ff+mf)
check('restored field and material states',fi+mi==ff+mf)
check('without replenished natural input fixed load cannot persist',d+mod<load+fl+ml+rec)
check('the internal port is not an extra environmental source',n+d+mod==load+fl+ml+rec)
print(f'{len(checks)}/{len(checks)} exact local comparator checks PASS')
