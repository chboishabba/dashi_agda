import json
import numpy as np
import check_toe_atlas_mirror as M
from toe_cyclotomic_operator import compile_shape,load,apply
from toe_cyclotomic_butterfly import apply_fast
rng=np.random.default_rng(3); v=rng.integers(-2,3,(2,729)).astype(object)
for name,G,lam in [('adapted mirror',M.inv(M.Pa)@M.m@M.Pa%3,2),('mirror',M.inv(M.P)@M.m@M.P%3,2),('rechart',M.inv(M.Pa)@M.P%3,1),('rotation',M.inv(M.P)@M.r@M.P%3,1)]:
 for s in (1,2):
  R=compile_shape(G,lam,s); r=R['rank']; R['scalar']=[1,0,3**(r//2)] if r%2==0 else [-1,-2,3**((r+1)//2)]
  R=load(json.dumps(R)); fast,d=apply_fast(R,v); slow,e=apply(R,v); assert d==e and np.array_equal(fast,slow)
 print('PASS',name,'rank',r,'butterflies',r*243,flush=True)
