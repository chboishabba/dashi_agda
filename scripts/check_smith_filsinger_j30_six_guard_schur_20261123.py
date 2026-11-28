#!/usr/bin/env python3
"""Exact 9-state + 6-event multiple-shooting Schur reduction.

Formal finite-dimensional algebra, not a validated return map or periodic orbit.
In a prescribed-mode source-only hybrid shooting system, with residual R of
nine return coordinates and six event-surface residuals G, the 15x15 Jacobian
is invertible iff every pre-switch guard slope and the saltation-aware
9x9 reduced return derivative are invertible.
"""
import json
from sympy import Matrix,eye,zeros,Rational
from math import prod

def check():
 n,m=9,6
 # Deterministic exact rational witness to nontrivial dense block elimination.
 D=Matrix(m,m,lambda i,j:Rational((2*i+1)*(3*j+2)%17-8,41) if i>j
          else Rational([2,-3,5,7,-11,13][i], [5,7,11,13,17,19][i]) if i==j else 0)
 B=Matrix(n,m,lambda i,j:Rational((11*i+7*j+3)%23-11,37))
 C=Matrix(m,n,lambda i,j:Rational((5*i+9*j+1)%19-9,31))
 M=Matrix.diag(*[Rational(j+2,j+4) for j in range(n)])
 Q=M-eye(n)  # desired reduced saltation-aware return Jacobian
 A=Q+B*D.inv()*C
 J=A.row_join(B).col_join(C.row_join(D))
 L=eye(n).row_join(-B*D.inv()).col_join(zeros(m,n).row_join(eye(m)))
 eliminated=L*J
 target=Q.row_join(zeros(n,m)).col_join(C.row_join(D))
 assert eliminated==target
 assert D.det()==prod(D.diagonal())
 assert Q.det()!=0 and D.det()!=0
 assert J.det()==D.det()*Q.det()
 assert (J.inv()*J)==eye(n+m)
 # This is an algebraic identity for a mode-scheduled event system: the
 # physical model still needs interval brackets for the true 15x15 blocks.
 return dict(status='PASS_EXACT_RATIONAL_SIX_EVENT_SCHUR_DETERMINANT',
   continuous_state_dimension=n,guard_time_dimension=m,augmented_dimension=n+m,
   exact_block_elimination=True,exact_determinant_identity=True,
   det_J_equals_product_guard_slopes_times_det_MminusI=True,
   guard_time_matrix_lower_triangular=True,
   actual_six_guard_physical_jacobian_interval_certified=False,
   actual_fixed_point_proved=False,github_ci_used=False)

if __name__=='__main__':print(json.dumps(check(),indent=2))
