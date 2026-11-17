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
