#!/usr/bin/env python3
"""OCT369 source-preserving finite geometry and gravity-load preflight.
No PtMn3 material/antigravity/Schumann experimental claim.
"""
from itertools import product
from collections import Counter
from math import isclose

T=(-1,0,1)
nine=set(product(T, repeat=2))
punctured_nine=nine-{(0,0)}
cube=set(product(T, repeat=3))
origin=(0,0,0)
punctured27=cube-{origin}
sheets={z:{p for p in punctured27 if p[2]==z} for z in T}
neg=lambda p:tuple(-x for x in p)
pairs={frozenset((p,neg(p))) for p in punctured27}
strata=Counter(sum(v!=0 for v in next(iter(pair))) for pair in pairs)
K=((0,0,1),(1,0,0),(0,1,0))
def matmul(a,b): return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)) for i in range(3))
assert len(nine)==9 and len(punctured_nine)==8
assert len(cube)==27 and len(punctured27)==26
assert tuple(len(sheets[z]) for z in T)==(9,8,9)
assert len(pairs)==13 and dict(strata)=={1:3,2:6,3:4}
assert matmul(matmul(K,K),K)==((1,0,0),(0,1,0),(0,0,1))
assert all(neg(neg(p))==p for p in punctured27)
assert isclose(70*9.80665,686.4655)
if __name__=="__main__":
    import json
    print(json.dumps({"full_nine":len(nine),"punctured_nine":len(punctured_nine),
      "full_cube":len(cube),"punctured_cube":len(punctured27),
      "punctured_sheets":[len(sheets[z]) for z in T],"antipodal_pairs":len(pairs),
      "projective_strata":dict(sorted(strata.items())),
      "C3_K_cube_identity":True,"70kg_weight_N":70*9.80665,
      "PtMn3_octupole_calibrated":False,"human_levitation_demonstrated_here":False,
      "Schumann_environmental_gain_demonstrated":False},indent=2))
