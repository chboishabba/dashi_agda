#!/usr/bin/env python3
"""Scoped SBP2 weak-Israel endpoint compatibility obstruction.

Physical C=DyU-(P-M)/2. Keep existing P and M weak SAT unchanged.
Attempt repair ONLY by changing U_T by V, requiring D_y V=g where
g=(SAT_P-SAT_M)/2 is independent at wall and far face.
Original second-order diagonal-norm SBP D has an exact left null
ell=[(-1)^(n-1),2(-1)^(n-2),..., -2,1], giving
  (-1)^(n-1)*g_wall+g_far=0
as necessary and sufficient solvability condition for boundary-only g.
Unrelated endpoint residuals violate it; joint SATs and modified
discrete constraints remain OPEN and are NOT ruled out.
"""
import json
import sympy as sp

def sbp2(n):
    if n<3:raise ValueError('SBP2 requires n>=3')
    D=sp.zeros(n)
    D[0,0]=-1;D[0,1]=1
    for j in range(1,n-1):
        D[j,j-1]=-sp.Rational(1,2)
        D[j,j+1]=sp.Rational(1,2)
    D[-1,-2]=-1;D[-1,-1]=1
    return D

def left_null(n):
    if n<3:raise ValueError('SBP2 requires n>=3')
    return sp.Matrix([sp.Integer((-1)**(n-1))]
      +[2*sp.Integer((-1)**(n-1-j)) for j in range(1,n-1)]
      +[sp.Integer(1)])

def audit():
    rows=[]
    for n in range(3,14):
        D=sbp2(n);ell=left_null(n)
        assert D.T*ell==sp.zeros(n,1) and D.rank()==n-1
        bad=sp.zeros(n,1);bad[0]=1;bad[-1]=2
        good=sp.zeros(n,1);good[0]=1;good[-1]=-ell[0]
        assert ell.dot(bad)!=0 and ell.dot(good)==0
        assert D.row_join(good).rank()==D.rank()
        rows.append(dict(n=n,bad_left_null=int(ell.dot(bad)),
          compatible_far_when_wall_is_one=int(-ell[0])))
    return dict(original_mode3_physical_constraint='DyU-(P-M)/2',
       original_weak_SAT_P_M_unchanged=True,
       left_null_formula='ell0=(-1)^(n-1), ell_j=2(-1)^(n-1-j), ell_far=1',
       necessary_sufficient_condition='(-1)^(n-1)*g_wall+g_far=0',
       arbitrary_independent_wall_far_Udot_only_repair_possible=False,
       joint_P_M_U_or_nonlocal_boundary_repair_disproved=False,
       rows=rows)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
