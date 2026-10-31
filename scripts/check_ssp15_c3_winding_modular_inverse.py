#!/usr/bin/env python3
"""Small-prime certificate for canonical SSP15 ten-jet reconstruction.

The first fifteen selected exact Eisenstein jet coordinates form a 15x15
integer matrix. A nonzero determinant mod 101 certifies nonsingularity
over Q and gives a small finite-field verification target for Agda/Lean.
This is NOT a rational decoder mod 101; reductions lose integer data.
"""
from check_ssp15_c3_winding_jet_rank import jet_matrix

def det_mod_p(A,p):
    A=[[int(v)%p for v in row] for row in A.tolist()]
    n=len(A); det=1
    for col in range(n):
        pivot=next((r for r in range(col,n) if A[r][col]),None)
        if pivot is None:return 0
        if pivot!=col:
            A[col],A[pivot]=A[pivot],A[col]
            det=-det
        v=A[col][col]
        det=(det*v)%p
        inv=pow(v,-1,p)
        for row in range(col+1,n):
            factor=A[row][col]*inv%p
            for k in range(col,n):
                A[row][k]=(A[row][k]-factor*A[col][k])%p
    return det%p

def main():
    m10=jet_matrix(10)
    selected=m10[list(range(15)),:]
    assert det_mod_p(selected,101)==98
    assert selected.det(method="domain-ge")%101==98
    assert m10.rank()==15
    print("PASS modular SSP15 15x15 certificate: determinant ≡ 98 (mod 101)")
    print("PASS nonzero modular minor => universal rational injectivity")
if __name__=="__main__":main()
