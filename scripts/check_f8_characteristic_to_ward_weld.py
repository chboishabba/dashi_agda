"""F8 W1/W3: actual donor graph H normal jets -> controller -> complete Ward.

Unlike the earlier synthetic free H0..H7 interface, this connector computes
uniform rational H0..H7 from the ORIGINAL boundary equation, prescribed
compact Pi and independently supplied second-normal/PDE-residual caps.
The output includes W1/W2/W3 source jet budgets and stencil allowances.
These are CONDITIONAL until original normal and PDE residual bounds exist.
"""
from fractions import Fraction as Q
from check_f8_characteristic_jet_caps import wall_jet_caps
from check_f8_original_source_jet_closure import source_jet_enclosure


def from_normal_history(cutoff, initial_H0, initial_H1, normal2,
                        equation_residual, shear, step=Q(1,1000), drive=1):
    H=wall_jet_caps(cutoff,initial_H0,initial_H1,normal2,equation_residual)
    result=source_jet_enclosure(cutoff,H,shear,step,drive)
    result['H_jets']=H
    result['unpaid_inputs']={
        'H0':'certified original first-order wall magnitude',
        'H1':'certified original first-order wall velocity',
        'normal2_0_to_5':'six original second-normal time-derivative magnitudes',
        'equation_residual_0_to_5':'six source-compatible original PDE residual magnitudes',
        'radial_cutoff':'independent Fourier quadrature and tail enclosure',
        'bulk_boundary':'actual normal and outgoing boundary graph estimate'}
    return result


def exact():
    zeros=[Q(0)]*6
    r=from_normal_history(40,Q(0),Q(0),zeros,zeros,Q(5),Q(1,1000))
    assert len(r['H_jets'])==8
    assert len(r['A2_jets'])==7
    assert all(v>=0 for v in r['H_jets'])
    for key in ('stress_israel','ward_temporal','ward_spatial'):
        assert len(r['source_jets'][key])>=7
        assert r['stencil_error'][key]['D1']>=0
        assert r['stencil_error'][key]['D2']>=0
    altered=from_normal_history(40,0,0,[Q(1)]+zeros[1:],zeros,5)
    assert altered['H_jets'][2]>r['H_jets'][2]
    altered=from_normal_history(40,0,0,zeros,[Q(1)]+zeros[1:],5)
    assert altered['H_jets'][2]>r['H_jets'][2]
    # Genuine Fourier zero mode and no 1/k admission.
    # The controller/positive-volume majorant is scoped to K>0. At K=0
    # use the separate homogeneous characteristic recurrence, never divide
    # by cutoff or pretend a positive-volume controller exists.
    z=wall_jet_caps(0,0,0,zeros,zeros)
    assert all(v==0 for v in z)
    try:from_normal_history(40,0,0,zeros[:5],zeros,5)
    except ValueError:pass
    else:raise AssertionError('missing normal trace admitted')
    print('PASS original F8 wall normal-graph -> H7 -> retarded A2 C6 -> full Ward C6')
    print('Normal second-jet and full residual enclosures remain UNPROVEN for original evolution')

if __name__=='__main__':exact()
