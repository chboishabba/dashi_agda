"""Audit actual original medium/medium-dt-half receipt pair; no continuum claim."""
import json, math, sys
from pathlib import Path
import numpy as np
import sympy as sp

def audit(paths):
    a,b=(json.loads(Path(p).read_text()) for p in paths)
    S,Seta,A,B,L,t=sp.symbols('S Seta A B L t', nonzero=True)
    E4=-(S*S*B+Seta*A+L)/(4*t*t)
    E5=-(S*S*B+(Seta+2*S)*A-L)/(2*t*t)
    assert sp.expand(E5-2*E4-(L-S*A)/t**2)==0
    a0,b0=sp.symbols('a0 b0')
    assert sp.expand(E4-E4.subs({A:a0,B:b0})+(S*S*(B-b0)+Seta*(A-a0))/(4*t*t))==0
    assert sp.expand(E5-E5.subs({A:a0,B:b0})+(S*S*(B-b0)+(Seta+2*S)*(A-a0))/(2*t*t))==0
    modekeys=['raw_mode_values','receiver_mode_intrinsic_4D_electric_Weyl','receiver_mode_projected_5D_electric_Weyl','receiver_mode_intrinsic_4D_electric_Weyl_tangent','receiver_mode_projected_5D_electric_Weyl_tangent','far_mode_intrinsic_4D_electric_Weyl','far_mode_projected_5D_electric_Weyl','far_mode_intrinsic_4D_electric_Weyl_tangent','far_mode_projected_5D_electric_Weyl_tangent']
    totals=['retarded_TT_yy_scaled_by_eps4','receiver_intrinsic_4D_electric_Weyl','receiver_projected_5D_electric_Weyl','receiver_intrinsic_4D_electric_Weyl_tangent','receiver_projected_5D_electric_Weyl_tangent','far_intrinsic_4D_electric_Weyl','far_projected_5D_electric_Weyl','far_intrinsic_4D_electric_Weyl_tangent','far_projected_5D_electric_Weyl_tangent']
    count=0
    for row in (a,b):
        assert row['intrinsic_4D_weyl_spatial_operator']=='full_reconstructed_Delta3'
        assert not row['numerical_convergence_certified'] and not row['full_Weyl_receiver_certified']
        assert row['discrete_support_photon_margin']>0
        for key,total in zip(modekeys,totals):
            vals=row[key];assert len(vals)==3 and np.isfinite(vals).all()
            assert math.isclose(sum(vals),row[total],abs_tol=1e-10,rel_tol=1e-10);count+=1
        t=row['receiver_t'];s=math.sqrt(1+t*t)/t;se=-1/(t*math.sqrt(1+t*t))
        dx=np.array(row['receiver_mode_Hxx']);lap=np.array(row['receiver_mode_Delta3H'])
        dht=np.array(row['receiver_mode_H_T_derivative_readout_disagreement']);dhtt=np.array(row['receiver_mode_H_TT_derivative_readout_disagreement'])
        for suffix in ('','_tangent'):
            x=np.array(row['receiver_mode_intrinsic_4D_electric_Weyl'+suffix]); old=np.array(row['receiver_mode_intrinsic_4D_electric_Weyl'+suffix+'_legacy_axial'])
            np.testing.assert_allclose(x-old,(dx-lap)/(4*t*t),atol=1e-12,rtol=1e-9);count+=3
        for name,pred in [('intrinsic_4D',-(s*s*dhtt+se*dht)/(4*t*t)),('projected_5D',-(s*s*dhtt+(se+2*s)*dht)/(2*t*t))]:
            key='receiver_mode_'+name+'_electric_Weyl'
            np.testing.assert_allclose(np.array(row[key])-np.array(row[key+'_tangent']),pred,atol=1e-12,rtol=1e-9);count+=3
        assert math.isclose(row['receiver_dual_Weyl_temporal_second_derivative_cancellation'],row['receiver_projected_5D_electric_Weyl']-2*row['receiver_intrinsic_4D_electric_Weyl'],abs_tol=1e-15);count+=1
    for key in ('step_radial','step_bulk','radius_bins','bulk_bins','eps','pulse','receiver_t','normal_order','nominal_receiver_r','far_receiver_grid_r','source_git_blobs','normalized_conservative_cell_moments','affine_stage_homogenized'):
        assert a[key]==b[key],key
    assert a['step_time']>b['step_time']
    print('SymPy 3/3 PASS; actual receipt checks',count,'PASS')
    print('realized dt ratio',a['step_time']/b['step_time'])
    for key in modekeys:
        old=np.array(a[key]); new=np.array(b[key]); delta=new-old
        print(key, 'signed delta',delta.tolist(),'absolute relative change',(abs(delta)/np.maximum(abs(old),1e-50)).tolist())
    return count
if __name__=='__main__':audit(sys.argv[1:])
