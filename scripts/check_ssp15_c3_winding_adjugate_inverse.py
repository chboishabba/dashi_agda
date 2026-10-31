#!/usr/bin/env python3
"""SSP15 C3 winding: explicit all-input inverse and nine-jet obstruction.

Exactly over Z/Q, not numerical DFT. The actual square minor is 15x15.
The certificate is adj(M)*M=det(M)*I, giving a rational decoder valid
for EVERY signed valuation vector, not just a sample; the 9-jet
nullspace supplies an explicit collision. Not an Agda kernel proof.
"""
from sympy import Matrix, eye, zeros
from check_ssp15_c3_winding_jet_rank import P, jet_matrix

def verify():
    m9, m10 = jet_matrix(9), jet_matrix(10)
    rows = tuple(m10.T.rref()[1])
    assert rows == tuple(range(15)), rows
    minor = m10[list(rows), :]
    det = minor.det(method="domain-ge")
    assert det == -68973567202690493145068231495208746474043983233237147979454873600000000
    adj = minor.adjugate(method="berkowitz")
    assert adj * minor == det * eye(15)
    # Valid for arbitrary valuation vectors by matrix identity:
    # decoder(J) = adj * selectRows(J) / det.
    null = Matrix([-360448,0,1136200,0,-2624622,0,4499352,0,
                   -4686825,2499640,0,-807576,374946,-32890,2223])
    assert m9 * null == zeros(18,1)
    assert (m10 * null)[9] == -571323080827699200
    pos = null.applyfunc(lambda x: max(x,0))
    neg = null.applyfunc(lambda x: max(-x,0))
    assert m9*pos == m9*neg
    assert m10*pos != m10*neg
    print("PASS universal adjugate reconstruction identity; det:",det)
    print("PASS explicit nonnegative 9-jet collision, resolved by jet 10")
if __name__ == "__main__":
    verify()
