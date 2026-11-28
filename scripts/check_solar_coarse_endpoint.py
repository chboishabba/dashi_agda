"""Exact coarse whole-proof negative controls."""
from fractions import Fraction as Q
from solar_coarse_endpoint import endpoint_bounds,backaction_bounds,verdict,refine,classify

def run():
    a=endpoint_bounds((1,1),(0,1),(Q(1,4),Q(1,3)),(Q(4,5),Q(4,5)),Q(1,100))
    assert verdict(a,domain_upper=True)=='EMPTY_ON_DECLARED_DOMAIN'
    assert verdict(a)=='UNRESOLVED'
    b=endpoint_bounds((1,1),(Q(9,10),1),(Q(1,10),Q(1,10)),(Q(1,2),Q(1,2)),Q(1,10))
    assert b==(Q(1,5),Q(3,10))
    assert verdict(b,witness=True,return_verified=True,source_verified=True)=='INHABITED_ON_DECLARED_MODEL'
    assert verdict(b,witness=True,return_verified=True)=='UNRESOLVED'
    c=backaction_bounds((1,2),(Q(1,10),Q(1,5)),(Q(1,10),Q(1,5)),(Q(1,2),Q(3,4)),Q(1,10))
    assert c==(Q(-1,4),Q(6,5))
    d=classify(Q(1,10),{'source':Q(1,5),'mesh':Q(1,100),'material':Q(1,20)})
    assert d['next_residual']=='source'
    assert refine(d['bounds'],(0,Q(1,5)))==(0,Q(1,5))
    try:refine(d['bounds'],(-1,1))
    except ValueError:pass
    else:raise AssertionError('non-nested refinement admitted')
    print('COARSE_ENDPOINT_PASS: 9 assertions')
if __name__=='__main__':run()
