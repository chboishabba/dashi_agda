#!/usr/bin/env python3
"""Original Gibbs D1 remote-pair admissibility no-go, exact Fraction arithmetic.

Finite normalized conditional rows are deliberately NOT physical SU(N)
Wilson Gibbs data. Checks whether the old 'for every admissible pair'
premise can be vacuously satisfied when admissible pairs are empty.
"""
from fractions import Fraction as Q
from itertools import product
import json

rows = {0:(Q(3,4),Q(1,4)), 1:(Q(1,4),Q(3,4))}
assert all(sum(row)==1 for row in rows.values())
def minimum_relative_epsilon(left,right):
    return max(abs(a-b)/a for a,b in zip(rows[left],rows[right]))
L1 = sum(abs(a-b) for a,b in zip(rows[0],rows[1]))
assert L1==Q(1)
assert minimum_relative_epsilon(0,1)==minimum_relative_epsilon(1,0)==Q(2)
q=Q(0)
admissible=set()
assert all(2*minimum_relative_epsilon(*p)<=q for p in admissible)
required={(0,1)}
assert not all(2*minimum_relative_epsilon(*p)<=q for p in required)
assert all(2*minimum_relative_epsilon(*p)>=Q(4) for p in required)
report={
    "result":"PASS exact vacuity no-go",
    "rows":[["3/4","1/4"],["1/4","3/4"]],
    "conditional_row_L1":"1",
    "empty_admissible_q_zero_vacuous":True,
    "required_distinct_pair_rejects_q_zero":True,
    "minimal_relative_epsilon":"2",
    "twice_epsilon":"4",
    "actual_original_SU_N_Wilson_decay":False,
    "YM_4D_mass_gap":False,
}
print(json.dumps(report,indent=2))

if __name__=="__main__":
    pass
