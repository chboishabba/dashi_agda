#!/usr/bin/env python3
"""Cross-check exterior-square generator lifts against repo-standard E6."""
import numpy as np
from itertools import product

from check_f3_e6_exterior_square import (
    MOD, Bp, J, closure, inv_mod, primitive5_action, qprim, tmat
)

def repo_reflect_standard_matrix(k):
    cols=[]
    for j in range(5):
        z=np.zeros(5,dtype=int); z[j]=1
        a,b,c,d,e=z
        if k==0: out=np.array([a,b,c,e,d])
        elif k==1: out=2*np.array([b+c+d+e,a+c+d+e,a+b+d+e,a+b+c+e,a+b+c+d])
        elif k==2: out=np.array([2*b+2*c+2*d+e,2*a+2*c+2*d+e,2*a+2*b+2*d+e,2*a+2*b+2*c+e,a+b+c+d])
        elif k==3: out=np.array([2*b,2*a,c,d,e])
        elif k==4: out=np.array([c,b,a,d,e])
        elif k==5: out=np.array([b,a,c,d,e])
        cols.append(out%MOD)
    return np.stack(cols,axis=1)%MOD

repo_generators=[repo_reflect_standard_matrix(i) for i in range(6)]
repo_image=closure([tmat(g) for g in repo_generators],5)
assert len(repo_image)==51840

D=np.array([
    [0,0,1,2,0],
    [0,1,0,0,1],
    [0,1,1,1,2],
    [0,1,2,2,2],
    [1,0,0,0,0],
],dtype=int)%MOD
Dinv=inv_mod(D)
Bstd=(2*np.eye(5,dtype=int))%MOD
assert np.array_equal((D.T@Bstd@D)%MOD,(2*Bp)%MOD)

def qstd(z):
    z=np.array(z,dtype=int)
    return int((z@z)%MOD)
assert all(qstd((D@np.array(v,dtype=int))%MOD)==(2*qprim(v))%MOD for v in product(range(3),repeat=5))

lifts=[
np.array([[1,0,1,1],[0,1,1,2],[2,2,2,0],[2,1,0,2]],dtype=int),
np.array([[2,0,1,1],[0,2,0,1],[1,2,1,0],[0,1,0,1]],dtype=int),
np.array([[1,0,1,1],[0,1,0,1],[1,2,2,0],[0,1,0,2]],dtype=int),
np.array([[0,0,2,1],[0,0,2,2],[2,2,0,0],[1,2,0,0]],dtype=int),
np.array([[0,0,1,1],[0,0,1,0],[0,2,0,0],[2,1,0,0]],dtype=int),
np.array([[0,0,2,2],[0,0,1,2],[2,1,0,0],[2,2,0,0]],dtype=int),
]

standard_images=[]
for lift,target in zip(lifts,repo_generators):
    assert np.array_equal((lift.T@J@lift)%MOD,(2*J)%MOD)
    prim=np.array(primitive5_action(tmat(lift)),dtype=int).reshape(5,5)
    std=(D@prim@Dinv)%MOD
    assert np.array_equal(std,target)
    standard_images.append(tmat(std))

pgsp_generated_image=closure(standard_images,5)
assert pgsp_generated_image==repo_image

print("PASS repo-standard E6 / PGSp same-object weld")
print("|repo E6 generated image|:",len(repo_image))
print("|PGSp-lift generated image|:",len(pgsp_generated_image))
print("generator-by-generator equality: 6/6")
