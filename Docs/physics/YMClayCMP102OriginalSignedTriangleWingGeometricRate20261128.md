# CMP102 Section 30 — original finite signed triangle plus Cauchy wings

28 November 2026. Source owner: Agda PR #1536. Preserve the original
Bałaban CMP102/CMP109, Bishop/Bridges and pinned Murray/Csimma
provenance; all other construction and extension attribution follows
its actual owner. No native Agda kernel acceptance is claimed.

## New geometry: the *exact* original finite residual

Use the source's true `Seq.SeriesOf terms count` convention (indices
0,...,c-1), and the exact original factorial terms

  a_j = 1/(2j+2)!, b_j = 1/(2j+3)!,
  A_c(X)=Σ_{j<c} a_j X^j,
  B_c(X)=Σ_{j<c} b_j X^j,
  G_c(X)=1-2A_c-X A_c²+2XB_c+X²B_c².

For c>=1, write the original signed Cauchy row
t_k=oddPart(k)-evenPart(k) with the actual endpoint conventions
oddPart(0)=1 and evenPart(0)=2a_0. The previously written
shiftedNativeBracketCoefficientZero proves t_k=0 for EVERY k.

Define the ACTUAL signed triangle evaluated on the Bishop source:

  T_c(X)=Σ_{k<c} t_k X^k = 0.

The new native Agda module
`YMClayCMP102OriginalSignedTriangleZeroExact.agda` proves this
last equality for all c and all real signed X by pointwise native
multiplication of the existing original signed coefficient theorem
and native Sequence.SeriesOf finite induction. It does not invent a
new all-degree Cauchy theorem.

Let `a(X)`, `b(X)` be the literal original CMP109 term families.
Define `Rectangle_c(a,a)` and
`Triangle_m(a,a)=Σ_{j<m} Σ_{i=0}^j a_i(X)a_(j-i)(X)`
using the existing original `BishopFiniteSeriesRectangleProductExact`
and `BishopFiniteCauchyRowReindexExact` objects. At c>=1:

  W_A(c)=Rectangle_c(a,a)-Triangle_(c-1)(a,a)
  W_B(c)=Rectangle_c(b,b)-Triangle_(max(c-2,0))(b,b)
  L_B(c)=2X b_(c-1) X^(c-1).

Then the exact original *finite* algebraic identity is

  G_c(X) = T_c(X) - X W_A(c) + L_B(c) + X² W_B(c).

This is not merely a sketch of the analytic limit: it is an
unbounded-index finite-polynomial identity, obtained by distributing
the two square products and splitting the original finite Cauchy
rows at the exact c cutoff. It keeps the omitted final B term.
For c=0 the separate original source value is G_0=1 (not zero).

The actual source Bishop objects have now been committed in
`YMClayCMP102OriginalFiniteTailGeometryExact.agda`, with both
rectangle-product crosswalks and T_c=0 consumers.

**Native proof status:** the all-c equality `G_c=T_c-XW_A+L_B+X²W_B`
is presently an exact rational all-degree derivation and
a checked finite algebraic certificate, NOT yet a proved Agda
theorem. The Agda module explicitly does not declare it as
kernel-checked. Its remaining proof is the original
rectangle/triangle Fin-index split; the underlying 0-valued
signed triangle and native square/rectangle identities are already
source-written.

## Stronger, source-native positive Cauchy majorant

The earlier 23 Nov owner already established the ordinary
`|G_c(X)|<=3*4^-c` bound mathematically. This Section 30
decomposition sharpens the constant while exposing the original
positive/negative wing geometry.

The finite SOURCE owners
`BishopFiniteSeriesAbsoluteBoundExact.finiteSeriesAbsoluteBound`
and `BishopFiniteCauchyWingAbsoluteBoundExact.finiteCauchyWingAbsoluteBound`
provide, for all c, literal Bishop real absolute-prefix bounds and
the signed rectangular A/B Cauchy wing bounded by their positive
triangle tail. The new source-specific consumers are
`YMClayCMP102OriginalFiniteCauchyWingBoundsExact.agda`:
`originalAPrefixAbsoluteBound`,
`originalBPrefixAbsoluteBound`,
`originalASquareCauchyWingFiniteBound`,
`originalBSquareCauchyWingFiniteBound`,
`originalASquareIsOriginalRectangle`, and
`originalBSquareIsOriginalRectangle`.

Because every surviving A/B wing monomial has degree >=c,
on |X|<=1/4 each term contains |X|^c as a factor. The original
positive factorial coefficient sums obey
  sum_{j<c}a_j <= 6/11 and sum_{j<c}b_j <= 10/57.
Thus for every c>=1:

  |G_c(X)| <=
    ( (6/11)^2 + 2*(10/57) + (10/57)^2 ) |X|^c
   = (267004/393129)|X|^c
   < (3/4)*4^-c.

The last strict rational inequality is exact:
  4*267004 = 1,068,016 < 1,179,387 = 3*393129.

This improves the older constant 3 to less than 3/4 for every
positive c and retains original c=0 separately with G_0=1<=3.
The analytic limit is unchanged: the same actual
`YMClayCMP102OriginalAbsoluteRateReceiverExact.agda` consumes
an original Bishop absolute finite error no larger than the
already verified 3*4^-c rate.

**Exact remaining native welds:**
1. Prove original finite G/triangle/wing equality in the actual
   Bishop `Seq.SeriesOf`/`Fin` constructors, using the already
   paid finite rectangle product and triangle reindex.
2. Bound each of the actual native positive Cauchy wing tails
   by |X|^c times its original positive coefficient mass (a finite
   Bishop order and power inequality), and consume the existing
   factorial-ratio order owners.
3. Combine the one absolute original bound with the existing
   `originalGZeroFromAbsoluteRate` receiver and actually run
   pinned Agda 2.9 including the transitive `--safe` import graph.
No new analytic source, no all-degree Cauchy axiom, no assumption
that G=0, and no independent Hodge/NS/RH/PNP theorem promotion.

## Independent exact execution

Committed
`scripts/check_ym_cmp102_original_tail_geometry.py`,
commit 7d7b50333e57a4943df21917de0f4a9149fa3060.
Local rational implementation was executed and gave
**3,624 / 3,624 PASS** across original prefix counts 0..64.
It verifies the explicit source polynomial decomposition at all
evaluated degrees, zero signed coefficients, first surviving
coefficient 2/(2c+2)!, separate A/B positive square-wing
mass ceilings, both signed quarter-radius endpoints, the
strict constant 267004/393129, and seven omitted-last-B negative
controls. The local script file Git blob e57892dfaeb0c6aab78d94400a30ec45534e5273
is NOT equal to the GitHub-created blob
4314cbd85e9a61c19ba52ea745c961eec49cf313; equivalent source
logic was run locally, not a byte-identical remote checkout.
The mathematical all-degree identity is justified independently by
finite Cauchy algebra, not extrapolation from 64 finite counts.

## Physical nonpromotion and proof execution

Scalar CMP102 G(X)=0, once accepted in Bishop Agda, is not the
4D interacting Wilson cluster expansion, original selected
CMP119/122 background field T, original nonfactorizing shared
F19 plaquette, uniform CMP116 rooted absolute shell, reflection
positive OS Hilbert construction or its same-H positive mass gap.
All E1/D2/N1/G1 physical obligations remain distinct.
