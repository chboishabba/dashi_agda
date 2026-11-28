"""Original 24-cell dense/CSR forward and smooth derivative parity."""
import numpy as np
from check_solar_spherical_reverse_integration import fixture
from solar_spherical_cycle import cycle
from solar_spherical_reverse_jvp import campaign_jvp

def run():
    mat,cfg,dh,dl=fixture()
    cfg=dict(cfg,common_stage_atlas=True,retain_history=True,retain_sensitivity=True)
    d=cycle(mat,cfg);s=cycle(mat,dict(cfg,sparse_operator=True))
    assert np.array_equal(np.asarray(d['history']),np.asarray(s['history']))
    assert d['campaign_ledger']==s['campaign_ledger']
    assert d['sensitivity_trace']==s['sensitivity_trace']
    a=campaign_jvp(mat,cfg,dh,dl)
    b=campaign_jvp(mat,dict(cfg,sparse_operator=True),dh,dl)
    for key in ('endpoint','endpoint_jvp'):
        for x,y in zip(a[key],b[key]):assert np.array_equal(x,y)
    assert a['dcampaign_net_J']==b['dcampaign_net_J']
    print(dict(status='SPARSE_SPHERICAL_PARITY_PASS',cells=len(cfg['row_keys']),steps=len(d['history']),physical_admission=False))
if __name__=='__main__':run()
