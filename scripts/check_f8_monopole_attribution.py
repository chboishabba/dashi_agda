"""Local full-clock receipt comparison and exact affine recurrence identities."""
import json
from pathlib import Path
import numpy as np
import sympy as s
from run_f8_monopole_shadow import maps
from ksw668_f8_fv_source_flux import exact_cell_averages
from run_f8_fused_forward import digest


def exact():
    A,B,G,S,x,y,c,gf,gc=s.symbols('A B G S x y c gf gc',commutative=False)
    xf=A*x+G*gf;yn=A*y+G*S*gc;cn=B*c+gc
    assert s.expand(xf-yn-(A*(x-y)+G*(gf-S*gc)))==0
    assert s.expand(yn-S*cn-(A*(y-S*c)+(A*S-S*B)*c+(G*S-S)*gc))==0
    assert s.expand(xf-S*cn-(xf-yn)-(yn-S*cn))==0
    return 3


def check(work):
    paths=['ledger-378-337-fused.npz','ledger-503-449-fused.npz','ledger-monopole-shadow.npz','ledger-monopole-coarse.npz']
    data=[]
    for path in paths:
        with np.load(work/path,allow_pickle=False) as z:
            assert int(z['k'])==4517
            a={k:z[k] for k in z.files if k in ('X','raw','window','shrink','own_raw','own_window','own_shrink')}
            assert all(digest(v)==z[k+'_sha'].item() for k,v in a.items())
            data.append(a)
    C,F,Y,M=data;assert np.array_equal(C['X'][:,:1],M['X'])
    rows={};count=0
    for k in ('raw','window','shrink'):
        c=C[k][:,:,0];f=F[k][:,:,0];y=Y[k];m=M[k]
        assert np.array_equal(c,M['own_'+k]);count+=c.size
        a,b,d=f-y,y-m,m-c;total=f-c;closure=a+b+d-total
        assert np.max(abs(closure))<=1e-14*max(1.,np.max(abs(total)))
        rows[k]=dict(source=a.tolist(),transport=b.tolist(),observer=d.tolist(),total=total.tolist(),max_abs_closure=float(np.max(abs(closure))))
    I,_,wc,wf=maps();c=exact_cell_averages(.04,np.arange(378)*.008,.008)[0,:-1];f=exact_cell_averages(.04,np.arange(503)*.006,.006)[0,:-1];m=I@c;d=f-m;z=wf*d*d
    cells=[dict(index=int(j),r=float(j*.006),fine=float(f[j]),mapped=float(m[j]),difference=float(d[j]),squared_norm_fraction=float(z[j]/z.sum())) for j in np.flatnonzero(d)]
    return dict(exact_groups=exact(),original_state_bitwise=True,original_observation_bitwise=count,rows=rows,source_cells=cells,source_first_three_fraction=float(z[:3].sum()/z.sum()),source_squared_norm=float(z.sum()))

if __name__=='__main__':
    import sys
    print(json.dumps(check(Path(sys.argv[1]))))
