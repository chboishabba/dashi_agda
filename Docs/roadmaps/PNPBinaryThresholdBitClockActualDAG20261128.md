# P vs NP — actual #1548 threshold DAG binary bit clock (28 Nov 2026)

## Exact original-owner boundary

Source: `DASHI/Mathematics/Complexity/PNPAggregateGateCountExact.agda`,
which already proves `gateCountExact`, `boundedDecode`,
`boundedEncode`, `clampSound` and `clampComplete` against the
actual native hard-CNF/DAG construction. No expanded truth table needed.
That module's bound k is a Nat. This cut supplies the **binary-input
machine representation** for k without first materialising a unary or
arbitrarily large integer value. It does NOT solve the remaining
polynomial-machine semantic coverage or circuit lower bound.

Let M = sum_rows max(0, length(row)-target(row)), exactly the existing
`excessBound`. Let bits b_1...b_L encode k in binary, leading zeros
permitted. Process left to right:

  s_0 = 0,
  s_{i+1} = min(M, 2*s_i+b_{i+1}).

This returns min(M,k) with every intermediate value <= M. The precise
inductive invariant is s_i=min(M,v_i), where v_i is the integer encoded
by the i-bit original prefix. The single indispensable weld is

  min(M, 2*min(M,x)+b) = min(M, 2*x+b)

for all M,x>=0 and b in {0,1}. Proof: if x<M, inner min equals x;
if x>=M, both outer sides equal M because 2*x+b >= M and
2*M+b >= M. Induction on input length proves the algorithm.

Machine cost: O(L) comparisons/shift-add operations on values with
at most ceil(log_2(M+1)) bits, i.e. O(L*(1+log(M+1))^c) bit operations
with a specified standard multiplication/comparison implementation
and fixed small c. Source row traversal and M computation must also be
charged. This is a polynomial-**representation** weld, not a polynomial
algorithm for SAT and not a lower bound.

The native Agda target is the actual bit-list value equivalence
`saturatedBits bs (excessBound rs) ≡ A.mn (binaryValue bs) (excessBound rs)`,
then rewrite the existing `boundedEncode`/`boundedDecode` receiver
under this equality, keeping original exact gate counts. Implement
using the existing Nat/list/cost owners, not a parallel threshold circuit.

## Exact regression

`scripts/check_pnp_aggregate_binary_clamp_bitclock_20261128.py`
performs 15,342 exact step/prefix checks including all 2^L words for
0<=L<=10 and a 131,072-bit long original input whose full integer is
never constructed in the streaming algorithm. Equivalence to ordinary
integer decoding is checked on small words. The binary-to-Agda Nat
semantic equivalence is mathematical induction above, not yet native
kernel certified.

## Remaining endpoint

N1-N3 original SAT/poly-time semantic coverage with faithful witness
decode remains the first enabling proof. U2-U4/A2 global sharing-stable
lower bound OR a genuine polynomial constructive decision procedure
is still original Clay P vs NP. Retain Karp-21 sign+residual size
noninjectivity and FRACDASH original-machine BIDI as donors, but do not
call a bounded finite DAG certificate a uniform asymptotic theorem.
