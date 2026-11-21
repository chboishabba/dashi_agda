#!/usr/bin/env python3
"""OCT369: exact Abelian vs non-Abelian gauge curvature commutator control.
Standard Lie algebra and gauge theory; not a Yang-Mills mass gap proof.
"""
import json
import sympy as s
I=s.I
sx=s.Matrix([[0,1],[1,0]])
sy=s.Matrix([[0,-I],[I,0]])
sz=s.Matrix([[1,0],[0,-1]])
A=I*sx; B=I*sy
comm=A*B-B*A
a,b=s.symbols("a b")
checks={
 "su2_commutator":s.simplify(comm+2*I*sz)==s.zeros(2),
 "su2_noncommutative":comm!=s.zeros(2),
 "su2_traceless":s.trace(A)==0 and s.trace(B)==0,
 "u1_scalar_commutes":s.simplify((I*a)*(I*b)-(I*b)*(I*a))==0,
 "su2_hermitian_field_strength":(comm/I).conjugate().T==comm/I,
 "su2_curvature_term_nonzero":comm!=s.zeros(2),
 "u1_curvature_commutator_zero":s.simplify(a*b-b*a)==0,
}
assert all(checks.values()),checks
if __name__=="__main__":
 print(json.dumps({"checks":checks,"passes":sum(checks.values()),
   "su2_commutator":str(comm),"Clay_SU_N_mass_gap_established":False,
   "U1_EM_gap_implies_nonAbelian_Clay_gap":False,
   "original_attribution":"classical Yang-Mills, Wilson, Balaban, Osterwalder-Schrader; DASHI finite comparator only"},indent=2,sort_keys=True))
