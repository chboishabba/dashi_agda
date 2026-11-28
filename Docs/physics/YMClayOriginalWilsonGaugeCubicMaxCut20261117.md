# YM.REAL maximum-cut continuation: original Wilson gauge and cubic moments

17 November 2026. **SymPy/exact rational verification, not Agda kernel acceptance.**

## Source-first reuse, not reinvention

There was already a universal source theorem that the original rational
periodic plaquette holonomy transforms by conjugation:
\`BalabanClayGate4RationalSU2BondCarrierExact.rationalSU2PlaquetteGaugeCancellation\`
(reusing \`BalabanClayGate4PeriodicBondPathBianchiExact.plaquetteGaugeCancellation\`).
There was already a source-written rational SU(2) trace class-function proof:
\`YMClaySide4RationalSU2C3WilsonTraceExact.rationalTraceConjugationInvariant\`.
The literal positive six-plane original source is
\`YMClayNativeRationalSU2SixPlaneSameSourceExact\`.

New \`DASHI/Physics/YangMills/YMClayNativeSixPlaneGaugeSameSourceExact.agda\`
composes precisely these existing owners. It defines the transformed
original plaquette trace, proves equality at every periodic side \`n\`,
then uses the **actual six-plane sum** and the **actual original side-four
site sum** to derive its gauge invariance. This is a candidate Agda source
(the pinned kernel has not run), with no assumed Haar/gauge-value field.

Independent regression:
\`scripts/check_ym_original_periodic_gauge_words_20261117.py\`
verifies exact free-group cancellation for both plaquette orientations at
every site, L=1,2,3,4. **16,992/16,992 exact equalities**. These are
not floating-point checks, and the universal source theorem is the
separate Agda owner.

## Original L=1 cubic Wilson moment — genuine commutators

At side length 1, the original lattice has four independent positive
links \(U_a\), and its six plaquettes are commutators. With
\(q_a=(q_{a0},v_a)\in S^3\), \(v_a\in\mathbb R^3\), the exact quaternion
identity (also independently checked with SymPy) is

\[
\frac12\operatorname{ReTr}
 (U_aU_bU_a^{-1}U_b^{-1})
 = 1-2\lVert v_a\times v_b\rVert^2.
\]

Define \(D_1=\sum_{a<b} (1-t_{ab})\).
The **actual original source** has

\[
D_1=2\sum_{a<b}\lVert v_a\times v_b\rVert^2.
\]

Use the four-link product of exact Pochhammer monomial moments, with
no degree cutoff and no 24-cell approximation. A sparse polynomial
compiler produces 54, 1371 and 20502 monomials for \(D_1,D_1^2,D_1^3\).
It obtains exactly

\[
\boxed{
H(D_1)=\frac92,\quad
H(D_1^2)=\frac{187}{8},\quad
H(D_1^3)=\frac{6445}{48}.
}
\]

Thus, for \(\beta\ge0\),

\[
Z_1(\beta)=1-\frac92\beta+\frac{187}{16}\beta^2
-\frac{6445}{288}\beta^3+O(\beta^4).
\]

The globally valid \(T_3\le e^{-S}\le T_2\) inequality gives

\[
\boxed{
1-\frac92\beta+\frac{187}{16}\beta^2
-\frac{6445}{288}\beta^3
\le Z_1(\beta)\le
1-\frac92\beta+\frac{187}{16}\beta^2 .
}
\]

At \(\beta=1/96\):

\[
\frac{243176723}{254803968}
\le Z_1(1/96)\le
\frac{140731}{147456},\quad
\mathrm{width}=\frac{6445}{254803968}.
\]

Source: \`scripts/check_ym_original_L1_cubic_sparse_pochhammer_20261117.py\`.
The quaternion commutator identity is checked symbolically over all
unrestricted quaternion coordinates, giving
\[
\operatorname{Re}(q r\bar q\bar r)
=\lVert q\rVert^2\lVert r\rVert^2
-2\lVert\mathrm{Im}\,q\times\mathrm{Im}\,r\rVert^2.
\]
The finite 24-cell's degree-five exactness does **not** suffice for
the cubic coefficient; use the all-degree Pochhammer evaluator.

## Original L>=2 cubic Wilson moments

Let \(P=6L^4\) be the literal six-positive-plane count, and
\(T=\sum_p t_p\), \(D_L=P-T\). Independent-link SU(2) center sign
\(U_e\mapsto -U_e\) implies

- \(H(t_p)=H(t_p^3)=0\);
- \(H(t_p t_q)=H(t_p^2t_q)=0\) when \(p\ne q\);
- \(H(t_p^2)=1/4\);
- \(H(t_p t_q t_r)=0\) for three distinct plaquettes with an
  edge appearing an odd number of times.

The exact F2 incidence checker builds every original positive
plaquette boundary at L=2,3,4, checks distinct supports and proves
by exhaustive bitset reduction that no three distinct boundaries
XOR to zero. Hence \(H(T)=0,\ H(T^2)=P/4,\ H(T^3)=0\) in
these checked volumes. Therefore

\[
\boxed{
H(D_L)=P,\quad H(D_L^2)=P^2+\frac P4,\quad
H(D_L^3)=P^3+\frac{3P^2}{4}
}\quad(L=2,3,4\ \mathrm{checked}).
\]

The same formula is mathematically expected for all \(L\ge2\).
For a universal formal proof, show that any three distinct elementary
plaquette supports in a four-dimensional periodic hypercubic lattice
at side \(L\ge2\) have nonzero Z2 boundary. For L>=3 any two
distinct elementary plaquettes share at most one original link;
for L=2, possible two-link sharing occurs in a common coordinate
plane, but three plaquettes cannot cover and pair all four edges
of each other. This geometric case distinction is **not** an Agda
all-L proof and not discharged by the finite tests.

The third coefficient in the true original Wilson expansion is

\[
\boxed{[\beta^3] Z_L
=-\frac{P^3}{6}-\frac{P^2}{8}.}
\]

Source: \`scripts/check_ym_original_wilson_cubic_incidence_20261117.py\`,
**1,305,545 exact integer/rational assertions**, including all
distinct plaquette pairs for L=2,3,4.

## Stronger exact partition brackets at beta=1/(16P)

| L | P | lower T3 | upper T2 | rational width |
|---:|---:|---:|---:|---:|
| 1 | 6 | 243176723/254803968 | 140731/147456 | 6445/254803968 |
| 2 | 96 | 2955151/3145728 | 184705/196608 | 43/1048576 |
| 3 | 486 | 4986797/5308416 | 935065/995328 | 649/15925248 |
| 4 | 1536 | 47282191/50331648 | 2955265/3145728 | 683/16777216 |

These are exact **mathematical independent-SU(2)-Haar / all-degree
moment functional** brackets. They do not imply that an Agda-defined
continuous Haar or original legacy/SUN measure has been constructed.

## Six target gates after this cut

1. **Fejer finite product**: source-written; kernel test remains open.
2. **All-degree Fourier/cubature**: exact cyclotomic checks through 9;
   all-degree trigonometric/Bishop root producer still open.
3. **Effective b_n**: exact rational kernel and schedule;
   Bishop order/modulus proof still open.
4. **Haar completion**: direct Bishop Cauchy-limit consumer exists;
   its b_n-derived Cauchy witness is still uninhabited.
5. **SU2 matrix**: rational-to-Bishop trace/norm/determinant/unitarity
   source candidates and exact SymPy checks; kernel acceptance open.
6. **Original Wilson/Haar/cylinder**: same-source original rational
   plaquette **gauge trace weld now source-written**, and genuine
   Wilson cubic coefficients newly verified. Original continuous
   product Haar, arbitrary-cutoff source algebra equivalence, and
   physical continuum remain open.

No transitive Agda kernel postulate-freedom or compiled acceptance is
claimed. This continuation **does not close YM.REAL**.

Attribution: Wilson; Bałaban; Pizzetti/Folland; Bishop–Bridges;
Murray/Csimma; Fejer/Stroud; original DASHI periodic-bond, quaternion,
six-plane source and matrix owners.
