# YM P0 CMP102 — original A/B series uniform-modulus completion

23 November 2026; PR #1536 master-based branch. Source-first mathematical certificate; **no Agda kernel or CI execution**.

## Original source and exact scope

The original CMP109 positive series coefficients are a_n=1/(2n+2)!, b_n=1/(2n+3)!. The existing `BalabanCMP109BishopRootFreeSeriesExact.agda` on current `master` already constructs Bishop `aSeries X inside` and `bSeries X inside` as limits of `Seq.SeriesOf (term aCoefficient X)` and its B counterpart for |X|<=1/4. This original analytic module is **not present on the current #1536 head**; importing it there, or moving the new CMP102 finite theorem to a compatible master head, is a separate branch/kernel operation. Nothing below redefines the represented limits.

The new original #1536 `YMClayCMP102OriginalEndpointCauchyShiftExact.agda` is a **source-written, kernel-pending** proof of the coefficient identities e_n=o_n at every degree, with e_0=2a_0, e_n=2a_n+sum_{i+j=n-1}a_i a_j for n>=1, o_0=1, o_1=2b_0, o_n=2b_{n-1}+sum_{i+j=n-2}b_i b_j for n>=2. Its precise endpoint/sign identifications remain a pinned-Agda verification obligation.

## Direct analytic completion without an infinite-product Cauchy reindex

For N>=1 set A_N(X)=sum_{n=0}^{N-1}a_n X^n and B_N analogously, and G_N(X)=1-2A_N(X)-X A_N(X)^2+2X B_N(X)+X^2 B_N(X)^2. All coefficients of degrees 0,...,N-1 are exactly zero by the original finite CMP102 source identities, including the exceptional odd singleton and both even endpoints. Thus G_N is a polynomial supported only in degrees n>=N.

The original factorial ratios are exact:

- a_{n+1}/a_n=1/((2n+3)(2n+4))<=1/12;
- b_{n+1}/b_n=1/((2n+4)(2n+5))<=1/20.

Consequently 0<=a_n<=(1/2)12^{-n}, 0<=b_n<=(1/6)20^{-n}, and the positive coefficient sums of every A_N and B_N satisfy A_N(1)<=6/11, B_N(1)<=10/57. The complete coefficient l1 norm (before cancellation) of G_N is bounded by

  1+2(6/11)+(6/11)^2+2(10/57)+(10/57)^2 = 1089001/393129 < 3.

Since G_N has no degrees below N, **for every signed real X with |X|<=1/4**,

  |G_N(X)| <= 3*4^{-N}.

This is an all-N exact coefficient-support proof, not extrapolation from a sampled grid or the first 48 polynomials. Furthermore the original factorial ratios give explicit uniform limit tails

  |A(X)-A_N(X)| <= (24/47)*48^{-N},
  |B(X)-B_N(X)| <= (40/237)*80^{-N}.

The full represented limits and partial sums are bounded respectively by 6/11 and 10/57 in absolute value on the original disk. Therefore the elementary difference-of-squares inequalities yield

  |G(X)| <= 3*4^{-N} + (25/11)*(24/47)*48^{-N} + (119/228)*(40/237)*80^{-N},

where G(X)=1-2A(X)-X A(X)^2+2X B(X)+X^2 B(X)^2, and this inequality holds for every N>=1. The RHS tends to zero effectively and independently of X, proving the **mathematical same-represented-series identity G(X)=0 on |X|<=1/4**, conditional in Agda on kernel certification of the finite row witnesses and the explicit source attachment of the already-constructed master CMP109 limits. It does not require new series or a formal Cauchy-product theorem.

## Exact acceptance and negative control

`scripts/check_ym_cmp102_uniform_analytic_modulus_20261123.py` locally executed with Python `fractions.Fraction`: **2072/2072 assertions PASS**. Checks ratios and coefficient majorants n=0..127, first N=1..48 full polynomial low-degree cancellation, full coefficient-norm envelope, omission of the final A endpoint (producing nonzero coefficient 2a_{N-1}), and signed test arguments including both original quarter-radius endpoints. The test supports the general symbolic proof above but is not its proof or an Agda kernel test.

## Precise remaining P0 obligations

1. **Kernel/branch:** reconcile current master native CMP109 Bishop represented limits and #1536 original CMP102 finite theorem on one safe import graph, then typecheck pinned Agda 2.9 with all transitive imports. Do not treat a source comment, a `machineChecked` tag or Fraction check as kernel acceptance.
2. **Source analytic:** implement the specific polynomial/limit comparison above using existing `Sequence` convergence and real polynomial continuity; identify the actual CMP102/Bishop chart argument X=-w, not an arbitrary renamed formal variable.
3. **Geometry:** source-selected Bishop quaternion norm, normalized SU(2) chord/trace deficit, CMP98 nonlinear background Q and actual CMP102 plaquette/minimizer domain. Earlier #1444 consumer remains conditional until a true same-module import/definition equality.
4. **Dominant physical P0:** original interacting 4D Wilson/Haar/F19 and actual CMP119/122 physical T, termwise absolute CMP116/W3 rooted-shell bound uniform in cutoff/volume, interacting E1 reflection-positive continuum, dense same-H OS gap, N1/G1. No Clay theorem conclusion follows from this analytic identity.

Attribution: original Wilson/Haar, Bałaban CMP98/102/109/116/119/122, classical factorial/Cauchy algebra, Bishop/Bridges and Murray/Csimma Bishop backend, prior DASHI original named owners. No substitute operator, new postulate, auxiliary gauge measure, or weakened radius.
