# YM CMP102 Section 41 — exact original two outer Cauchy wings

**Scope:** A source-native Bishop finite-order construction for the TWO remaining original CMP102 scalar wing inequalities. **Not** an interacting Wilson loop, reflection-positivity, or mass-gap proof. Written at the precise original coefficient/Fin triangle cutoffs; Agda elaboration and safe import audit **pending**.

## Original coefficient and indexed geometry — no new analytic series

Fix original signed represented Bishop (X) with (u=|X|\le q=1/4), and (c\ge1). From the original `CMP109.term` source, write

- (a_i=\mathrm{CMP102.aCoefficient}(i)=1/(2i+2)!\ge0);
- (b_i=\mathrm{CMP102.bCoefficient}(i)=1/(2i+3)!\ge0);
- (A_c=\sum_{i<c}a_iX^i), (B_c=\sum_{i<c}b_iX^i).

The original `Row.trianglePartial` at count (k) contains exactly (i+j<k), and `Rectangle.rectangleSum` contains exactly (0\le i,j<c). Thus the existing `Tail.originalAWing X c` and `Tail.originalBWing X c` (no substituted triangle or rectangle) have finite, source-defined expansions

\[
W_A(c)=\sum_{\substack{0\le i,j<c\\i+j\ge c-1}}
 a_i a_j X^{i+j},\qquad
W_B(c)=\sum_{\substack{0\le i,j<c\\i+j\ge \max(c-2,0)}}
 b_i b_j X^{i+j}.
\]

These are finite Fins, not infinite series or analytic reindexing. The original **shifted** donors are `BishopFiniteCauchyShiftedWingAbsoluteExact.originalWingOneEarlierAbsolute` and `originalWingTwoEarlierAbsolute`, with the actual `YMClayCMP102OriginalShiftedWingOrderExact.originalBCountOneSingleton` when (c=1). The ordinary unshifted Mertens tail alone is insufficient.

## Universal source-geometric outer-wing estimate

For (i+j\ge c-1), (i+j+1\ge c). Because (0\le u\le q\le1),

\[
u^{i+j+1}\le q^{i+j+1}\le q^c.
\]

Finite triangle inequality, multiplication order and nonnegative coefficients therefore give

\[
\begin{aligned}
|XW_A(c)|
 &\le \sum_{\substack{i,j<c\\i+j\ge c-1}} a_ia_j u^{i+j+1}\\
 &\le q^c\sum_{i,j<c}a_i a_j
   =q^c\bigl(\sum_{i<c}a_i\bigr)^2\\
 &\le q^c(6/11)^2
   =q^c\,36/121\le q^c.
\end{aligned}
\]

For (c\ge2), (i+j\ge c-2\) implies (i+j+2\ge c), and similarly

\[
|X^2W_B(c)|\le q^c\bigl(\sum_{i<c}b_i\bigr)^2
\le q^c(10/57)^2=q^c\,100/3249\le q^c.
\]

**Exceptional count (c=1):** the original B triangle cutoff (c\mathbin{\dotminus}2=0) is empty, so (W_B(1)=b_0^2), not a nonexistent two-earlier wing. The B contribution has exponent (2\ge c=1):

\[
|X^2W_B(1)|=b_0^2u^2\le b_0^2q^2\le q^1 (10/57)^2\le q.
\]

This includes (X=0) and negative (X). For **(c=0)**, do not apply the positive-wing formula: existing Section37 source pays (G_0=1\le3q^0). The original omitted B last row is already paid in `YMClayCMP102OriginalOmittedBPositiveWingExact` (Section39).

Thus, once the following exact native Bishop transports elaborate, `YMClayCMP102OriginalTwoOuterWingsToLimitExact.OriginalOuterTwoWings X` is paid from source without an independent proposition, and the EXISTING original scalar rate receiver yields (|G_c(X)|\le3q^c) and its represented (G(X)\simeq0).

## The precise Agda implementation/dependency welds

1. **Index cutoff:** bridge the original `Row.trianglePartial` and `Rectangle.rectangleSum` via actual Fin rows into the finite predicate (0\le i,j<c\), (i+j\ge k\), using the existing `BishopFiniteCauchyRowReindexExact` and `BishopFiniteCauchyShiftedWingAbsoluteExact`; do NOT assert that an arbitrary Cauchy-triangle series reduces definitionally to a filtered square.
2. **Coefficient absolute transport:** use the original `CMP109.aNN/bNN`, `Seq.∣xⁿ∣≃∣x∣ⁿ` and original Bishop `P.∣x*y∣≃∣x∣*∣y∣` to build the absolute upper sum on the real original aTerm/bTerm.
3. **Degree monotonicity:** for every real exponent (m\ge c) show (u^m\le q^c) from (u\le q\le1), using the original finite power-order theorem (not a floating numerical bound).
4. **Finite positive subset/rectangle:** filtered sum \(\le\) whole positive square rectangle. Use `BishopFiniteCauchyWingAbsoluteBoundExact` / `BishopFiniteCauchyTriangleInsideRectangleExact`, or implement the missing finite `Fin` predicate monotonicity in one reusable foundation lemma.
5. **Original finite coefficient masses:** consume `YMClayCMP102OriginalFactorialMassBudgetExact` through `YMClayCMP102OriginalFactorialRatioBishopExact` for EVERY c, with constants \(6/11\) and \(10/57\); **audit the rational cross-product proof against the actual library** before claiming these are kernel theorems.
6. **Both scalar leaves and rate:** handle (c=1) B explicitly, then build `OriginalOuterTwoWings X` from the two all-count inequalities and call the existing native rate receiver. Finally run the pinned **Agda 2.9 --safe graph**. Until then: **SOURCE CONSTRUCTION ONLY / PENDING KERNEL**.

## Exact residual boundary

Even complete CMP102 scalar native acceptance would **not** establish the Clay Yang–Mills conjecture. Independent debts remain: nontrivial interacting four-dimensional SU(N) continuum measure, original connected Wilson/OS reflection positivity, the original physical Hamiltonian (H\), and a strictly positive same-(H\) spectral mass gap. Do not promote scalar Cauchy calculus into that physical theorem.
