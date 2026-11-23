"""Analyze completed original native grids; no continuum promotion.
Usage: python check_f8_lvi_refinement.py WORK (coarse at native/receipt.json).
"""
import argparse,json
from pathlib import Path
import numpy as np
import sympy as s

GRID={'coarse':(.012,.016,.0025),'medium':(.008,.012,.0018),'fine':(.006,.009,.0012),'factorial-A':(.008,.012,.0012),'factorial-B':(.008,.009,.0012),'factorial-C':(.006,.012,.0012),'medium-dt-half':(.008,.012,.0009),'fine-dt-half':(.006,.009,.0006)}
FIELDS={'H':'raw_mode_values','E4':'receiver_mode_intrinsic_4D_electric_Weyl','E5':'receiver_mode_projected_5D_electric_Weyl','E4t':'receiver_mode_intrinsic_4D_electric_Weyl_tangent','E5t':'receiver_mode_projected_5D_electric_Weyl_tangent','lap':'receiver_mode_Delta3H','farE4':'far_mode_intrinsic_4D_electric_Weyl','farE5':'far_mode_projected_5D_electric_Weyl'}

def exact():
    t,L,A,B=s.symbols('t L A B', nonzero=True)
    E4=-(A+L)/(4*t*t); E5=-(A+2*B-L)/(2*t*t)
    assert s.simplify(E5-2*E4-(L-B)/t**2)==0
    assert s.simplify(-4*t*t*E4-L-A)==0
    assert s.simplify(L-t*t*(E5-2*E4)-B)==0

def analyze(work):
    exact(); rows={}
    for label,(dr,dy,dt) in GRID.items():
        d=json.loads((work/('native/receipt.json' if label=='coarse' else label+'.json')).read_text())
        assert d['intrinsic_4D_weyl_spatial_operator']=='full_reconstructed_Delta3'
        assert d['step_radial']==dr and d['step_bulk']==dy and 0<d['step_time']<=dt
        assert d['receiver_t']==12 and d['eps']==.04 and d['pulse']==.065 and d['normal_order']==3
        assert d['conservative_source_cell_average'] and not d['affine_stage_homogenized']
        assert d['original_radial_multipoles']==[0,2,4] and not d['numerical_convergence_certified']
        assert d['discrete_support_photon_margin']>0
        vals={k:np.array(d[v]) for k,v in FIELDS.items()}
        assert all(v.shape==(3,) and np.isfinite(v).all() for v in vals.values())
        for k,v in {'H':'retarded_TT_yy_scaled_by_eps4','E4':'receiver_intrinsic_4D_electric_Weyl','E5':'receiver_projected_5D_electric_Weyl','E4t':'receiver_intrinsic_4D_electric_Weyl_tangent','E5t':'receiver_projected_5D_electric_Weyl_tangent','farE4':'far_intrinsic_4D_electric_Weyl','farE5':'far_projected_5D_electric_Weyl'}.items():
            assert np.isclose(vals[k].sum(),d[v],atol=1e-10,rtol=1e-10)
        rows[label]=vals
    factors={}; pairs={}; geometry={}
    for k in FIELDS:
        a,b,c,d=(rows[x][k] for x in ('factorial-A','factorial-B','factorial-C','fine'))
        radial=c-a; normal=b-a; interaction=d-c-b+a; total=d-a
        np.testing.assert_allclose(radial+normal+interaction,total,atol=1e-15,rtol=1e-12)
        factors[k]={key:v.tolist() for key,v in [('radial',radial),('normal',normal),('interaction',interaction),('total',total)]}
        pairs[k]={name:(rows[y][k]-rows[x][k]).tolist() for name,x,y in [('medium_time','medium','medium-dt-half'),('fine_time','fine','fine-dt-half')]}
    for name,x,y in [('radial','factorial-A','factorial-C'),('normal','factorial-A','factorial-B'),('radial_fine_normal','factorial-B','fine')]:
        diff=lambda k:rows[y][k]-rows[x][k]
        L=diff('lap'); E4=diff('E4'); E5=diff('E5'); t=12.
        A=-4*t*t*E4-L; B=L-t*t*(E5-2*E4)
        geometry[name]=dict(E4_spatial=(-L/(4*t*t)).tolist(),E4_acceleration=(-A/(4*t*t)).tolist(),Heta=B.tolist(),dual=(E5-2*E4).tolist())
    return dict(schema='LVI-corrected-finite-refinement',physical_acceptance=False,alias={'factorial-D':'fine'},modes=[0,2,4],rows={k:{f:v.tolist() for f,v in a.items()} for k,a in rows.items()},factorial=factors,time_pairs=pairs,geometry=geometry)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('work',type=Path);a=p.parse_args();print(json.dumps(analyze(a.work),indent=2))
