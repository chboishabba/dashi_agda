import numpy as np
from toe_cyclotomic_hom_batch import apply_batch,cached
from toe_cyclotomic_operator import compile_shape,apply
import check_toe_atlas_mirror as M
rng=np.random.default_rng(23); v=rng.integers(-2,3,(2,729,90)).astype(object)
for G,lam in [(M.inv(M.Pa)@M.m@M.Pa%3,2),(M.inv(M.P)@M.m@M.P%3,2),(M.inv(M.Pa)@M.P%3,1),(M.inv(M.P)@M.r@M.P%3,1)]:
 for s in (1,2):
  R=compile_shape(G,lam,s); r=R['rank']; R['scalar']=[1,0,3**(r//2)] if r%2==0 else [-1,-2,3**((r+1)//2)]
  f,d=apply_batch(R,v); a,e=apply_batch(R,f,True); assert np.array_equal(a,v*d*e)
  for j in (0,89):
   ref,dd=apply(R,v[:,:,j]); assert dd==d and np.array_equal(ref,f[:,:,j])
  print('PASS',r,s,'all 90 channels roundtrip, two streaming references',flush=True)
print(cached.cache_info())
