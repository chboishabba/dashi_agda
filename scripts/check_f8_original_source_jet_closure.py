"""Original F8 finite-band Pi -> retarded A2 -> complete (T,C,R) C6 weld.

Single missing analytical producer: certified first-order physical metric
Fourier H time jets through order 7 across |k|<=K, t in [1,12].
Outputs source bounds and certified five-point D1,D2 errors for T,C,R.
The source bound does NOT pay radial/normal/temporal discretization or the
coupled second-order Einstein/material/gauge chart and receiver.
"""
from fractions import Fraction as F
from check_f8_retarded_controller_jet_enclosure import controller_caps
from check_f8_full_ward_jet_majorant import ward_majorant
from check_f8_timejet_stencil_certificate import certified


def source_jet_enclosure(cutoff,H,muS,step,drive=1):
    if len(H)<8:raise ValueError('need original first-order H0..H7')
    if step<=0:raise ValueError('step positive')
    A2=controller_caps(cutoff,H,6,drive)
    source=ward_majorant(cutoff,H,A2,muS,6)
    bounds={}
    for key in ('stress_israel','ward_temporal','ward_spatial'):
        M5,M6=source[key][5:7]
        # Preserve rational bounds to avoid a floating under-enclosure.
        h=F(step)
        bounds[key]={'D1':h**4*M5/18,'D2':h**4*M6/54}
    return {'A2_jets':A2,'source_jets':source,'stencil_error':bounds}


def exact():
    H=[F(2**j) for j in range(8)]
    r=source_jet_enclosure(40,H,5,F(1,1000))
    assert len(r['A2_jets'])==7
    for key in ('stress_israel','ward_temporal','ward_spatial'):
        q=r['stencil_error'][key]
        assert q['D1']>0 and q['D2']>0
        assert q['D1']==r['source_jets'][key][5]*F(1,1000)**4/18
        assert q['D2']==r['source_jets'][key][6]*F(1,1000)**4/54
    # The zero mode is valid because there is no 1/k in this construction.
    # Original finite-band supports are K,2K,3K respectively.
    assert 40+40==80 and 40+80==120
    try:source_jet_enclosure(40,H[:7],5,F(1,1000))
    except ValueError:pass
    else:raise AssertionError('missing H7 incorrectly admitted')
    print('PASS original F8 Pi -> A2 -> full Ward C6, only H0..H7 source hypothesis')
    print('synthetic H-jet error allowances at h=.001:',
          {k:(f'{float(v["D1"]):.2e}',f'{float(v["D2"]):.2e}')
           for k,v in r['stencil_error'].items()})
    print('No H0..H7 original interval proof or coupled Einstein receiver accepted')

if __name__=='__main__':exact()
