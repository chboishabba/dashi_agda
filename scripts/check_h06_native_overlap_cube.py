#!/usr/bin/env python3
"""Exact rational regression of native H06 overlap and H05 source operations.
Not a kernel test. Common overlap, not physical evolution of the geometry.
"""
from itertools import combinations, product, permutations
from fractions import Fraction as F
import sympy as s


def require(ok, label):
    if not ok:
        raise RuntimeError(label)


def mat_equal(a, b):
    return all(s.cancel(x) == 0 for x in a-b)


def normalize(B, o, p):
    E=s.eye(4)[list(p),:]
    M=E*B
    if M.det()==0:
        return None
    D=B*M.inv()
    return D, o-D*E*o


def rotation(q):
    w,x,y,z=q
    n=sum(a*a for a in q)
    require(n!=0, 'zero quaternion')
    return s.Matrix([[n-2*(y*y+z*z),2*(x*y-w*z),2*(x*z+w*y)],
                     [2*(x*y+w*z),n-2*(x*x+z*z),2*(y*z-w*x)],
                     [2*(x*z-w*y),2*(y*z+w*x),n-2*(x*x+y*y)]])/n

D=[s.eye(3),s.diag(1,-1,-1),s.diag(-1,1,-1),s.diag(-1,-1,1)]


def read_frame(k,R):
    A=D[k]*R
    d=1+s.trace(A)
    if d==0:
        return None
    require(d>0,'trace guard')
    return s.Matrix([A[2,1]-A[1,2],A[0,2]-A[2,0],A[1,0]-A[0,1]])/d


def write_frame(k,v):
    return D[k]*rotation([s.Integer(1),*v])


# Generic row coefficient probes, not just sampled point equality.
o,a,b,p,q,r=s.symbols('o a b p q r',real=True)
u,v=s.symbols('u v',real=True)
g=o+a*u+b*v; h=p+q*u+r*v
require(s.expand((g-h).subs({u:0,v:0})-(o-p))==0,'origin probe')
require(s.expand((g-h).subs({u:1,v:0})-(g-h).subs({u:0,v:0})-(a-q))==0,'slope 0 probe')
require(s.expand((g-h).subs({u:0,v:1})-(g-h).subs({u:0,v:0})-(b-r))==0,'slope 1 probe')
# Selected exact planes include singular and negative pivot cases.
marks=list(combinations(range(4),2)); planes=[]; triples=0; singular=0
for a,b,c,d in product((-1,0,1),repeat=4):
    B=s.Matrix([[1,0],[0,1],[a,b],[c,d]])
    o=s.Matrix([0,0,F(2,3),F(-3,5)])
    charts={k:normalize(B,o,k) for k in marks}
    singular+=sum(v is None for v in charts.values())
    valid=[k for k in marks if charts[k] is not None]
    for k,l in product(valid,repeat=2):
        E,h=charts[k]; J,t=charts[l]
        E2,h2=normalize(E,h,l)
        require(E2==J and h2==t,'coefficient cocycle')
        triples+=1
    planes.append((B,o,valid))

frames=[]; frame_triples=0; frame_singular=0
for q in product((-1,0,1),repeat=4):
    if not any(q): continue
    R=rotation(tuple(map(s.Integer,q)))
    valid=[i for i in range(4) if read_frame(i,R) is not None]
    frame_singular+=4-len(valid)
    require(R==rotation(tuple(map(s.Integer,(-x for x in q)))),'central sign observer')
    for a,b,c in product(valid,repeat=3):
        f=read_frame(a,R)
        g=read_frame(b,write_frame(a,f))
        h=read_frame(c,write_frame(b,g))
        require(write_frame(b,g)==R and h==read_frame(c,R),'frame cocycle')
        frame_triples+=1
    frames.append((R,valid))

# Actual discrete H05 axis operations: partition (retain suffix), rotate
# each triple, support/sign encode. Preserve independent source context.
# Affine parameters move by decode at current pivot then encode at target;
# frame coordinates move by actual matrix reconstruction at each edge.
vertices=('','x','y','xy','z','xz','yz','xyz')
faces=[('', 'x','y'),('', 'x','z'),('', 'y','z'),('z','x','y'),('y','x','z'),('x','y','z')]
canon=lambda s: ''.join(sorted(s))

def setup(B,o,valid,R,validf,shift):
    rows={v:valid[(i+shift)%len(valid)] for i,v in enumerate(vertices)}
    fm={v:validf[(2*i+shift)%len(validf)] for i,v in enumerate(vertices)}
    piv={v:s.eye(4)[list(k),:] for v,k in rows.items()}
    A={v:piv[v]*B for v in vertices}
    O={v:piv[v]*o for v in vertices}
    return fm,A,O


def move(state,op,fm,A,O):
    v,coeff,point,frame,ctx=state
    target=canon(v+op)
    p=A[target]*A[v].inv()*(point-O[v])+O[target]
    f=read_frame(fm[target],write_frame(fm[v],frame))
    require(f is not None,'admissibility')
    if op=='x':
        # explicit split tag is carried by the cube vertex, suffix intact
        new=coeff
    elif op=='y':
        new=tuple(t[1:]+t[:1] for t in coeff)
    else:
        new=tuple(tuple((int(x!=0),x) for x in t) for t in coeff)
    return target,new,p,f,ctx


def path(state,word,fm,A,O):
    for op in word:
        state=move(state,op,fm,A,O)
    return state

face_checks=endpoint_checks=terminal_checks=0
# Factored exact tests: each sampled plane paired with a deterministic
# sampled frame and two independent signed/zero contexts; not full product.
for i,(B,o,valid) in enumerate(planes):
    R,vf=frames[i%len(frames)]
    for spin in (-1,1):
        fm,A,O=setup(B,o,valid,R,vf,i+spin)
        coeff=((0,1,-1),(-1,0,1),(1,-1,0))
        ctx=(spin,0,3*spin,('original','retained'))
        s0=('',coeff,A['']*s.Matrix([F(1,7),F(-2,9)])+O[''],read_frame(fm[''],R),ctx)
        for prefix,x,y in faces:
            st=path(s0,prefix,fm,A,O)
            require(path(st,x+y,fm,A,O)==path(st,y+x,fm,A,O),'face')
            face_checks+=1
        end=path(s0,'xyz',fm,A,O)
        for w in permutations('xyz'):
            require(path(s0,w,fm,A,O)==end,'endpoint')
            endpoint_checks+=1
        require(end[4]==ctx and write_frame(fm['xyz'],end[3])==R,'retained spin and frame')
        require(tuple(tuple(x[1] for x in row) for row in end[1])==tuple(t[1:]+t[:1] for t in coeff),'source codec reopen')
        terminal_checks+=1
print('PASS', 'affine coefficient comparisons',triples,'singular pivots',singular,
      'frame triple paths',frame_triples,'singular frame charts',frame_singular,
      'H05 faces',face_checks,'endpoints',endpoint_checks,'terminals',terminal_checks,flush=True)
