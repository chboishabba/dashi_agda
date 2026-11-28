"""Compare a separate budget-matched distributed terminal receiver policy."""
from fractions import Fraction as F
import numpy as np
from solar_synthetic_fixture import fixture
from solar_exact_tail_policy import certify_policy


def run():
    m,c,_,_=fixture();n=len(m[0]);c=dict(c,sparse_operator=True,common_stage_atlas=True,
        kinetics=dict(c['kinetics'],ionization_s_inv=[0.,0.]),terminal_load_rate_s_inv=np.full(42,.04/64))
    assert sum(map(lambda v:F(float(v)),c['terminal_load_rate_s_inv']),F(0))<=F(.04)
    out=certify_policy(m,c,np.ones((n,3),bool),[5.]*n,[20.]*n,powers=(16,32,48,64))
    cert=out['reference']['certificate'];assert out['conditional_tail_decay_proved'] and F(cert['rho_upper_exact'])<1
    assert F(cert['step_error_threshold_exact'])>=F(1,2**51)
    print(dict(status='DISTRIBUTED_TAIL_PASS',budget_used=float(sum(c['terminal_load_rate_s_inv'])),certificate=cert,
        tail_start_seconds=float(F(out['tail_start']['sufficient_start_seconds_exact'])),physical_admission=False))
if __name__=='__main__':run()
