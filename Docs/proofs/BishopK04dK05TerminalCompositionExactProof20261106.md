# K04d/K05 terminal analytic identities: common original-series proof

This note records the exact mathematical proof that must be transported to the pinned
Bishop setoid, not a new analytic carrier or an Agda kernel receipt. It deliberately
does not promote `ZetaHalfPlaneLayer`'s unconstrained `Set` fields to semantic equality.

## A. Negative logarithm: coefficient proof, avoiding differentiation of limits

Write
\[
L(X)=\sum_{n\ge1}\frac{X^n}{n},\quad
F(X)=\sum_{m\ge0}\frac{(-L(X))^m}{m!}.
\]
All expressions below first live in \(\mathbb Q[[X]]\), with \(L(0)=0\)
so each coefficient of the composition is a **finite** sum. Formal differentiation:
\[
L'(X)=\frac{1}{1-X},\quad F'=-L'F,\quad
(1-X)F'+F=0,\quad F(0)=1.
\]
For \(F=\sum a_nX^n\), the constant coefficient is
\(a_1+a_0=0\); the coefficient of \(X^n\), \(n\ge1\), is
\((n+1)a_{n+1}+(1-n)a_n=0\). Hence \(a_0=1\), \(a_1=-1\),
\(a_2=0\), and every subsequent coefficient vanishes. Thus
\[
\boxed{F(X)=1-X\text{ in }\mathbb Q[[X]].}
\]
The universal recurrence uniqueness is already written in
`BishopNegativeLogExpFormalRecurrenceUniquenessExact`. Do **not** reprove it.

### Absolute convergence and evaluation

For any real radius \(0\le r<1\),
\[
\sum_{n\ge1}\left|\frac{x^n}{n}\right|
\le\sum_{n\ge1}r^n=\frac r{1-r}
\quad(|x|\le r).
\]
For the absolute nested exponential sum, expand the \(m\)-th power using
finite Cauchy products before passing to the limit:
\[
\sum_{m\ge0}\frac1{m!}
 \left(\sum_{n\ge1}\frac{r^n}{n}\right)^m
\le \sum_{m\ge0}\frac1{m!}
  \left(\frac r{1-r}\right)^m<\infty.
\]
Consequently the infinite double/multiple sums admit absolute rearrangement
by finite-rectangle tails and Bishop Cauchy convergence. The coefficient of
each \(X^k\) is the finite formal coefficient already computed. It follows,
*after* proving the original Bishop evaluation map preserves this
absolutely convergent composition, that
\[
 \operatorname{exp}_B(-\operatorname{sourceNegativeLogValue}(x))\simeq1-x
 \qquad (0<x<1).
\]
This last transport is an **Agda implementation obligation**, not a premise
that may be inserted as a record field.

An independent quantitative option uses the finite polynomial
\(L_N(x)=\sum_{n=1}^Nx^n/n\). For \(0\le x\le r<1\), the finite
identity \(L_N'=(1-x^N)/(1-x)\) implies
\[
\left(\frac{e^{-L_N(x)}}{1-x}\right)'
=\frac{e^{-L_N(x)}x^N}{(1-x)^2}.
\]
Since \(L_N\ge0\), finite-product positivity gives
\[
0\le\frac{e^{-L_N(x)}}{1-x}-1
\le\frac{r^{N+1}}{(1-r)^2}.
\]
The bound tends to zero uniformly on \([0,r]\). This route requires
a Bishop finite-polynomial chain-rule/integral comparison, so it is an
alternative rather than an unlicensed classical MVT import.

## B. Machin: formal composition and absolute evaluation

Let
\[
A(X)=\sum_{n\ge0}\frac{(-1)^nX^{2n+1}}{2n+1}
\in\mathbb Q[[X]],\qquad
E(X)=\exp(2iA(X))\in\mathbb Q[i][[X]].
\]
Then
\[
A'(X)=\frac1{1+X^2},\qquad
E'(X)=\frac{2i}{1+X^2}E(X),\qquad E(0)=1.
\]
The *actual* Cayley formal series
\(C(X)=(1+iX)/(1-iX)\) obeys the same initial-value equation:
\[
(1+X^2)C'(X)=2iC(X),\qquad C(0)=1.
\]
Coefficient induction (no division by a zero integer in characteristic
zero) yields \(E=C\) degree by degree. The existing
`BishopMachinOriginalCayleyFormalSeriesExact` proves the denominator
recurrence for \(C\); the missing source-native portion is to identify
the coefficients of the **nested original** \(\exp_C(2iA)\) with that
recurrence, not to construct a new Cayley series.

For \(|t|\le1/2\),
\[
\sum_{n\ge0}\left|\frac{t^{2n+1}}{2n+1}\right|
\le \frac{|t|}{1-|t|^2}\le\frac23.
\]
Hence the absolute magnitude of every finite exponential composition
is dominated by \(\sum_{m\ge0}(4/3)^m/m!\), and its rearrangement
is justified by a **single** summable majorant, independent of the
selected Machin point. Native complex-factorial finite Cauchy
reindexing plus limit transport must establish the evaluation homomorphism.
Only then conclude, for the original series at both \(t=1/5\) and
\(t=1/239\),
\[
\boxed{\exp_C(2i\operatorname{atan}_B(t))
\simeq\frac{1+it}{1-it}.}
\]
Reuse the existing two-point Machin compiler, phase-quarter proof,
and first-sine-zero consumer; do not introduce a parallel pi.

For comparison, the finite atan polynomial
\(A_N(t)=\sum_{n<N}(-1)^nt^{2n+1}/(2n+1)\)
satisfies \((1+t^2)A_N'=1-(-t^2)^N\).
The uniform derivative residual is already source-written with
\(4^{-N}\) bound in
`BishopOriginalLogAtanUniformDerivativeRemainderExact`.
Pointwise derivative convergence alone is **not** the required
infinite composition transport.

## C. Selected zeta and completed xi

The present original-series Basel majorant proves uniform summability
on selected compact charts of \(\Re s>2\). For \(\Re s\ge2+\delta\)
one may dominate all original terms by \(n^{-2-\delta}\le n^{-2}\)
(where the Bishop order/exp-log weld is established).
The existing `BishopUniformLimitSequentialContinuityExact`
and `BishopOriginalExponentialUniformCompactTailExact`
supply the generic limit and exponential steps; do not duplicate them.

**Semantic ownership is the remaining separate issue.** Construct a
concrete selected \(\zeta_B(s)\) as the Bishop limit of the *actual*
term series \(\exp_C(-sL_n)\) and provide:
1. termwise original-log/exponential identification with \(n^{-s}\);
2. equality of that limit with the chosen `ZetaHalfPlaneLayer.zetaHalfPlane`,
   proved as a value equality, not as a free `Set` witness;
3. the **definitionally selected** completed factor
   \(\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)\),
   including original Bishop gamma and power semantics, and proof of
   equality on the chosen domain.

The constructed Dirichlet function can be shown continuous on the
selected charts now; the equalities in (2) and (3) cannot be extracted
from an unconstrained substrate. They are not consequences of merely
naming the functions.

## D. Golden kernel acceptance checklist

- Import and instantiate the exact original Bishop `sourceNegativeLogTerm`,
  `bishopExp`, original atan terms, original `BishopSetoidComplexExact.expC`.
- Define finite degreewise nested-composition coefficients and prove that
  evaluating the source limits preserves these coefficients under the
  explicit common majorants above.
- Apply existing recurrence-uniqueness proof owners; emit the original
  LOG and two Machin values, with no new assumed arguments.
- Construct the selected zeta and xi same-object equalities.
- Use `run_agda29_parallel_check.sh` with `--safe` on exact PR head.
  A source-level argument, this document, and numerical regression are
  **not** an Agda acceptance receipt.

This is a concrete *mathematical* closure strategy for the two infinite
compositions; it is **not yet the complete machine-checked K04d/K05
max-cut**. Attribution: original Bishop/Bridges, Murray/Csimma,
Cauchy, Machin, and existing DASHI proof owners.

## E. K05-PRODUCT source-owner re-audit (same head)

The original source-level product **does already have its full terminal
implementation**. In
`DASHI/Foundations/BishopRound11SignedFactorialDegreeBinomialExact.agda`:

- `originalEvenSignedFactorialDegree` proves the shifted odd/odd
  correction against literal original cosine coefficients;
- `originalOddSignedFactorialDegree` proves the original sine
  convolution equality;
- `originalImaginaryExponentialMultiplicative` invokes
  `Native.round11ProductFromOriginalFactorialDegreeSplits` for **all**
  original Bishop-real arguments;
- `originalSineCosineAdditionFromNativeFactorials` obtains both addition
  laws on the exact selected Bishop setoid-complex carrier.

`BishopRound11NativeComplexRectangleExact.agda` independently implements
four source-absolute Cauchy triangles, their convergence to the original
complex exponential product, the odd/odd vanishing correction and the
finite telescope. **No additional product lemma needs to be invented**.
The remaining K05-PRODUCT task is exact-head Agda elaboration and repair
of any actual elaboration failures, not mathematical implementation.
