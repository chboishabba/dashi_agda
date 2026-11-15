# Koenigs P1: all-degree formal exponential–logarithm identity

**Scope:** exact algebraic identity over the rational formal power-series ring; finite Bishop-real geometric derivative theorem source-written separately. Does **not** yet establish the analytic identity for the particular Bishop complex exponential.

## Original task

Construct the ordinary-complex exponential's selected upper fixed point and a locally invertible logarithmic germ on the original Bishop carrier; prove a nonconstant Koenigs/Schröder coordinate and Abel chart, then the normalized global Kneser tetration and same-object modular-\(j\) observable.

The immediately useful identity is \(\exp_C(L(w))\approx_C1_C+w\), for the **constructed convergent** source series
\[
L(w)=\sum_{k\ge1}\ell_k w^k,\qquad
\ell_k=\frac{(-1)^{k+1}}k.
\]

## Theorem — formal inverse for all degrees

In \(\mathbb Q[[X]]\), put \(L(X)=\sum_{k\ge1}(-1)^{k+1}X^k/k\) and
\[
E(X)=\exp(L(X))=\sum_{n\ge0}e_nX^n
\]
with \(e_0=1\). Formal differentiation and Cauchy multiplication give
\[
E'=L'E,\qquad
n e_n = \sum_{k=1}^n k\ell_k e_{n-k}
       =\sum_{k=1}^n(-1)^{k+1}e_{n-k}.
\]
For \(n=1\), \(e_1=e_0=1\). Assume inductively that \(e_j=0\) for every \(2\le j<n\), with \(n\ge2\). Only \(n-k=1\) and \(n-k=0\) contribute:
\[
n e_n=(-1)^n e_1+(-1)^{n+1}e_0=0.
\]
Since the coefficient ring is \(\mathbb Q\), \(e_n=0\). Induction proves
\[
\boxed{\exp\!\left(\sum_{k\ge1}\frac{(-1)^{k+1}X^k}{k}\right)=1+X}
\]
as an exact identity in \(\mathbb Q[[X]]\), simultaneously in **every degree**, not only through a chosen cutoff.

The same argument holds in formal power series over any commutative \(\mathbb Q\)-algebra. It does **not** establish termwise differentiation of analytic Bishop-complex functions, nor that the original Cartesian exp/sin/cos exponential agrees with the exponential power-series operation on the Bishop complex.

## Finite derivative identity as an independent direct algebraic check

Let \(P_N(X)=\sum_{k=0}^{N-1}(-X)^k\), the polynomial derivative of the truncated \(L_N(X)\). A finite telescoping computation yields
\[
(1+X)P_N(X)=1-(-X)^N
\]
for every natural \(N\). The direct Bishop-real source-written theorem is
\`DASHI.Moonshine.AbelBishopLogFiniteGeometricDerivativeExact.originalBishopFiniteLogDerivativeGeometricIdentity\`.
It avoids asking a solver to inspect an infinite series. **Agda 2.9 acceptance is still pending.**

## Independent finite exact regression

\`scripts/analytic_j_tetration_exp_log_formal_recurrence.py\` calculates coefficients using \`fractions.Fraction\` and verifies through degrees \(1,2,3,6,12,32,64,100\) that \(e_0=e_1=1\), \(e_n=0\) for \(2\le n\le N\). The script is integrated into the fail-closed local acceptance runner. Exact finite computation is a regression; the inductive proof above is the mathematical all-degree justification.

## Remaining original Agda seams, max-cut order

1. **P0:** typecheck the added norm-power, coefficient, finite-derivative and limit files on the exact current PR head under Agda 2.9 \`--safe\`; fix any actual failures. Existing source written is not a kernel receipt.
2. **P1.01d:** formalize the above recurrence in the original finite rational/power-series algebra, using existing Cauchy-product and series-extensionality owners where applicable. The rational identity should be source-checked for all \(n\), not merely numerically tested.
3. **P1.01e:** transport formal coefficient equality to the actual constructed Bishop complex exponential \`BishopSetoidComplexExact.expC\` and the literal \`originalBishopLogOnePlusCanonicalLimitOnUnitDisk\`: requires genuine complex exp Cauchy-product/derivative or analytic power-series uniqueness and uniform convergence. No authority record asserting the inverse is acceptable.
4. **P1.02:** construct selected nonreal fixed point \(p\), original complex inverse \(p^{-1}\), and a disk witness for \(w=(z-p)/p\). Use local \(g(z)=p+L(w)\), \(\exp_C(p)\approx_Cp\), and the actual exponential addition law to prove \(\exp_C(gz)\approx_Cz\). Its principal-branch identity is optional for **local** conjugacy but required for global branch continuation.
5. **P1.03–06:** prove the original quadratic bound, geometric Koenigs increments, common uniform Cauchy modulus and holomorphic limit; use existing Bishop series/telescoping/Cauchy completions.
6. **P1b/P1g:** coherent punctured-sector logarithm and winding cocycle; conjugate-pair continuation, fundamental region, real normalization, global Kneser uniqueness.
7. **P2–P4:** selected Bishop trigonometric period, true \(q(\tau+1)=q(\tau)\), original \(E_4/E_6/\Delta/j\), level-27 relative-fine analytic compatibility, certified Kouznetsov contours.

**Non-promotion:** a formal identity in \(\mathbb Q[[X]]\) alone cannot be used as a claim that a global complex tetration exists, that the Bishop source logarithm is the principal branch, or that \(\Theta_{E8}=E_4\) has been completed.
