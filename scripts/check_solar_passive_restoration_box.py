"""Exact frozen-chart restoration obstruction and conservative box boundary."""
from fractions import Fraction as F
from solar_passive_campaign_bound import rational_restoration_exclusion

def run():
    assert rational_restoration_exclusion([3,4],1,1,2)['excluded']
    assert not rational_restoration_exclusion([3,4],1,1,3)['excluded']
    assert not rational_restoration_exclusion([3,4],1,1,4)['excluded']
    assert rational_restoration_exclusion([F(3,5),F(4,5)],'1/4','1/4','1/4')['excluded']
    # Rounded binary sum can hide infeasibility; exact mode must use fractions.
    lo=[1.,2.**-54]; assert sum(lo)==1.
    assert sum(map(F,lo),F(0))>F(1)
    print('PASS restoration triangle and rational feasibility boundary')
if __name__=='__main__':run()
