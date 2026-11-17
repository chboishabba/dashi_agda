# YM.REAL root-free Fejer cubature: maximum-cut status (2026-11-17)

**Trust:** Source-written, not Agda-kernel checked. Original Bishop SU(2) Haar and Wilson-source weld remain OPEN. Keep ESD untouched and retain Fejer, Stroud, Pizzetti/Folland, Bishop/Murray/Csimma, Wilson, Balaban and existing DASHI attribution.

## Correct root-free product construction

For m>=1 define M=2m, J=m-1 and angles
\[
\psi_a=a\pi/(m+1),\quad
\theta_b=(2b-1)\pi/(2M),\quad
\phi_c=2\pi c/(2m).
\]
The sphere point is
\[
v_{abc}=(\cos\psi_a,\sin\psi_a\cos\theta_b,
\sin\psi_a\sin\theta_b\cos\phi_c,
\sin\psi_a\sin\theta_b\sin\phi_c).
\]
The **probability** weights are
\[
w_a^{CII}=\frac{2\sin^2\psi_a}{m+1},\qquad
w_b^{FI}=\frac1M\left(1-2\sum_{j=1}^{m-1}
\frac{\cos(2j\theta_b)}{4j^2-1}\right),\qquad
w_c^{circle}=\frac1{2m}.
\]
**Corrections:** The familiar Fejer-I factor 2/M integrates dt and has total mass 2; integrating dt/2 requires 1/M. The product uses **4m^3**, not 2m^3 nodes.

A one-line telescoping estimate proves **strictly positive** Fejer weights:
\[
2\sum_{j=1}^{J}\frac{1}{4j^2-1}
=1-\frac{1}{2J+1},\qquad
\boxed{w_b^{FI}\ge\frac{1}{M(2J+1)}>0}.
\]
Midpoint-cosine discrete orthogonality implies for k<M:
\[
\sum_b w_b^{FI}T_k(\cos\theta_b)=
\begin{cases}
1 & k=0\\
0 & k\text{ odd}\\
(1-k^2)^{-1}&k\ge2\text{ even}
\end{cases}
=\frac12\int_{-1}^1 T_k(t)\,dt.
\]
Together with Chebyshev-II and 2m-circle Fourier exactness this yields
\[
\boxed{H(P)=\sum_{a,b,c}w_a^{CII}w_b^{FI}w_c^{circle}P(v_{abc}),
\quad\deg P\le2m-1.}
\]
The monomial parity reduction removes odd angular terms and converts remaining roots to polynomials. For every degree d, choose m with 2m-1>=d; positive cubature yields non-circular polynomial positivity.

## Reuse the simpler effective S3 approximation

The already-derived polynomial b_n(q,v)=((1+q dot v)/2)^n has normalizer c_n=(3/2)_n/(3)_n and first moment 3/(n+3). For degree-(n+1) positive cubature define
\[
Q_n f(q)=c_n^{-1}\sum_jw_j f(v_j)b_n(q,v_j),\qquad
\|Q_nf-f\|_\infty\le\omega_f(\delta)+\frac{12M_f}{(n+3)\delta^2}.
\]
This evaluates f **only on S3** and provides explicit uniform-approximation schedules. Do not replace it with the proposed Jackson identity: the claimed equality of a fourth power of the sine quotient and the square of a Chebyshev sum is false at N=1, theta=pi/2 (1/4 versus 1).

## Bishop completion, then original Wilson

Existing source owners: YMClayP0BishopRealCarrierInstancesExact, BalabanCMP109116BishopRealSetoidInstantiationExact, YMClayBishopSetoidFiniteAdjointTraceExact, YMClayNativePositiveBondEnumerationVectorExact, YMClaySUNVariablePhysicalCutoffFamilyExact, BishopPowerSeriesElementaryBridgeExact, BishopFastCauchyCommonCompletionExact.

Choose effective n(k) and a_k=H(Q_{n(k)} f) with dyadic errors; prove absolute convergence of telescoping a_0+sum_k(a_{k+1}-a_k) to use the actual Bishop series-limit API. Then construct I(f), prove linearity, positivity, setoid extensionality and left/right quaternion invariance using polynomial density.

Attach I to the canonical 4(n+1)^4 positive links and 6(n+1)^4 six-plane plaquettes. On the **same source** prove the quaternion/matrix trace weld, Wilson action gauge naturality, Bishop exponential order/positivity, and
\[
Z_n=I^{\otimes4(n+1)^4}(e^{-S_n}),\qquad
e^{-12\beta_n(n+1)^4}\le Z_n\le1,\quad Z_n>0.
\]
Legacy RealAnalysisAxioms real equality is *not* interchangeable with Bishop setoid equality.

The pinned vendor Bishop real itself does not define all sin/cos/exp/log operations on its main branch; the repository's BishopPowerSeriesElementaryBridgeExact owns the power-series construction and has further analytic obligations. Avoid assuming those functions are immediately available.

## New producer and reference receipts

* DASHI/Physics/YangMills/YMClaySU2FejerProductFiniteExact.agda: finite cartesian product construction with an intrinsic proof that product weights are strictly positive **given** positive factors. No concrete trig factor producer or all-degree exactness is supplied in this file. Agda kernel not run.
* scripts/check_ym_su2_fejer_rootfree_20261117.py: **1,132** exact rational assertions across degrees 7 and 9, normalized Fejer moments, telescoping positive weight floor, and circle Fourier coefficient arithmetic. The code uses mathematically derived DCT moments; it is not a kernel proof of the DCT identities.

**Verdict:** Mathematical root-free cubature construction and reference checks advance YM.REAL; the all-m trigonometric producer, Bishop completion and exact original Wilson/Haar source attachment are still OPEN. Do not change the 19/28 expanded count.


## Source-first continuation on 17 November 2026 (no kernel acceptance claim)

Five additional theorem owners were attached to the SAME TOE import graph, using existing Bishop and finite Wilson source:
- YMClayBishopFiniteWeightedIntegralLawsExact: recursive finite weighted sum; proves congruence, normalized constant-one and preservation of nonnegativity from actual finite weights.
- YMClayBishopSU2QuaternionTraceWeldExact: native Bishop 2×2 quaternion matrix trace and proved concrete half cancellation using BP.ℝ-Solver.
- YMClayBishopSU2DeterminantExact: determinant algebra is norm-square, and a norm-one quaternion gives determinant one; explicit unit norm is the physical domain condition.
- YMClayBishopSU2UnitarityExact: entrywise 2×2 U(q)†U(q) matrix identity, reduced to the original Bishop real solver. Local SymPy checks validate the 8 component polynomial expressions, not an Agda receipt.
- YMClayBishopSU2HaarSeriesLimitExact: selects the ACTUAL Bishop.bishopSeriesLimit of a finite polynomial integral telescope, proves limit convergence/uniqueness from the original Bridge API; the absolute-telescope convergence certificate remains a mathematical producer and must be inhabited by the b_n approximation schedule.
- YMClayBishopFiniteWilsonNormalizedExact: uses actual Inv._⁻¹ on positive finite partition, proves expectation-of-one and extensionality. This does not construct the positive partition from physical exponential/Haar.

Acceptance scripts and trust scanner were extended for these source modules. The numerical and symbolic reference verifiers are not Agda kernel acceptance. Existing imported Bishop complex/bridge owners may also carry non-safe transitive dependencies, and must be checked by the pinned compiler before asserting --safe.

**Outstanding after this continuation:**
1. Inhabit all-m Bishop Fejer/Chebyshev-II/circle trigonometric nodes/weights and prove exact cubature equals Pochhammer moments in Agda.
2. Transport effective b_n approximation bounds to real setoid inequalities, produce dyadic n(k), and prove the telescoping series absolutely convergent, rather than merely consuming a record.
3. Establish the same physical original SU2 compact group/link map and six-plane action, Bishop exponential positivity, actual completed product Haar and positive finite partition, then original cylinder identity.
4. Run pinned Nix/Agda source checks and transitive postulate audit; no such run happened in this environment.

**Status remains YM.REAL OPEN; 19/28 expanded gates OPEN.** Do not replace the legacy RealAnalysisAxioms.ℝ by a propositional equality, and do not relabel a Bishop-safe consumer as an original source producer.


## 17 November continuation: corrected YM.REAL trust and proof cut

The six requests are NOT closed. The following new proof transformations are source-written:

1. **Bishop direct Cauchy limit.** YMClayBishopSU2HaarSeriesLimitExact now imports the pinned Sequence directly rather than BishopConstructiveRealBridgeExact, which itself imported RealAnalysisAxioms. The new EffectiveHaarCauchyApproximation consumes an actual Cauchy proof and constructs its limit, convergence and uniqueness through Sequence.fast-cauchy⇒convergent and Sequence.lim. The b_n cubature *producer* of the Cauchy witness is still unpaid. Absolute telescoping convergence is no longer necessary.

2. **Strict finite weighted positivity.** YMClayBishopFiniteWilsonNormalizedExact now derives nonnegative finite weighted sums by structural induction, and a strictly positive sum from a nonempty list with a positive first weight/integrand and remaining nonnegative contributions. This is a theorem on the actual Bishop ordered real, not a new partition-positive assumption. To instantiate it physically, original Wilson exp(-S) strict positivity and positive original Haar node weights must be proved separately.

3. **SU(2) quaternion matrix identities.** The trace, determinant and U-dagger U Agda source is present, but kernel acceptance pending. Independent exact symbolic identities give RealTr U(q)=2q0, det U(q)=||q||^2, and U†U=UU†=||q||^2 I2. The *original* SUN.CertifiedSUNMatrixTheory carrier is propositionally typed and cannot be silently equated to Bishop setoid equality.

4. **Trust correction.** The canonical TOE regression is declared --safe; the non-safe candidate complex/matrix/Wilson modules were removed from direct imports and reaggregated under the separate non-safe DASHI.Unified.YMClayBishopRealCandidateRegression. The two safe-only finite algebra modules remain in the canonical TOE import graph. A local --safe pragma by itself is not an Agda acceptance receipt.

5. **Existing all-m Fejer gap.** Complete source proof of Fejer/Chebyshev-II/circle trigonometric nodes, Fourier orthogonality and Pochhammer equality remains open. The 1,132 exact-rational assertions do not establish that Agda theorem.

6. **Existing Bishop/Wilson gap.** Effective b_n approximation as a Bishop real theorem, constructive Haar on all admissible continuous functions, and original Wilson exponential, same-link cylinder and gauge/source identities remain open.

No Agda compiler or Nix environment was available; all new modules are source-written and not kernel typechecked. YM.REAL OPEN; expanded ledger 19/28 OPEN.

Attribution: Wilson/Balaban; Fejer/Stroud; Pizzetti/Folland; Bishop/Bridges/Murray/Csimma; prior DASHI original quaternion and real proof owners.
