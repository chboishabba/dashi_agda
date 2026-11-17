# YM.REAL: exact original six-plane low-order and dyadic cyclotomic maximum cut — 17 November 2026

**Source status:** This is a new exact finite mathematical certificate and pinned numeric Nat ledger on the existing PR #1444 branch. The actual all-degree Agda/Bishop Haar/Wilson source closure remains OPEN. No Agda binary/Nix installed in the active execution container, no kernel test conducted.

## 1. Original Wilson, not a toy plaquette lattice

Reuse:
- YMClayNativePositiveBondEnumerationVectorExact original 4D periodic 4L^4 bonds and exact decoder
- BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact.PositivePlane4, six a<b axes
- YMClayNativeRationalSU2SixPlaneSameSourceExact and YMClayNativeSixPlaneOrderedIdentityExact, genuine native boundary/trace and distinction from the **16 ordered-axis** convention.

At L=4 the canonical source has 4*4^4=1024 positive bonds and P=6*4^4=1536 positive plaquettes. The new exact script builds every 4-link plaquette in periodic Z/LZ, and checks distinct link supports and their symmetric differences for L=3,4. All different plaquette pairs have at least one link appearing only once, so the independent-link central sign involution sends t_p t_q to its negative, giving expectation zero when p!=q.

On the true normalized SU2 one-link moment functional H, H(t_p)=0, H(t_p^2)=1/4. The latter follows by integrating one independently Haar-distributed link and using the exact S3 coordinate moment H(q0^2)=1/4. Because each Taylor coefficient up to beta^2 has degree <=2 in each link, any per-link cubature that matches SU2 Haar moments through degree 2, including the positive rational 24-cell, yields the SAME coefficients.

For the original periodic six-plane Wilson deficit action S=beta*sum_p(1-t_p), with P=6L^4,
\[
H_{\rm links}\Big(\sum_p(1-t_p)\Big)=P,\qquad
H_{\rm links}\Big(\sum_p(1-t_p)\Big)^2=P^2+P/4,
\]
\[
\boxed{Z_L(\beta)=1-P\beta+
  \left(P^2/2+P/8\right)\beta^2+O(\beta^3).}
\]

At L=4:
\[
\boxed{Z_4(\beta)=1-1536\beta+1179840\beta^2+O(\beta^3).}
\]
At L=3: P=486 and beta^2 coefficient=472635/4.

The new safe arithmetic owner YMClayOriginalWilsonSecondOrderCombinatoricsExact.agda pins the canonical side-four 1024-link count and exact numerator 8*(1179840)=4*1536^2+1536. It does **not** prove measure integration or any unknown coefficient. The geometry and 24-cell degree-two link moments are covered in the exact Python reference. In particular, this is NOT a proof of all-degree Haar and not a physical continuum solution.

Reference: scripts/check_ym_original_wilson_loworder_20261117.py, 42,517/42,517 locally executed exact assertions.

## 2. Fully explicit fast-Cauchy b_n schedule

The existing exact Pochhammer kernel b_n(q,v)=((1+q·v)/2)^n has
\[
c_n=(3/2)_n/(3)_n,\quad
H_v((1-q\cdot v)b_n)/c_n=3/(n+3),
\quad
H_v((q\cdot v)^2b_n)/c_n=
\frac{n^2+n+3}{(n+3)(n+4)}.
\]
For f bounded by B and L-Lipschitz, pick eps_k=2^{-(k+3)}, delta_k=eps_k/(2L), and n_k=ceil(96 B L^2/eps_k^3). Then
\[
\|Q_{n_k}f-f\|_\infty
\le L\delta_k+\frac{12B}{(n_k+3)\delta_k^2}
\le\varepsilon_k.
\]
Thus, **provided actual degree-(n_k+1) positive cubature**, the polynomial integrals a_k=H(Q_{n_k}f) obey
\[
|a_j-a_k|\le\varepsilon_j+\varepsilon_k
\le 2^{-(k+2)}\qquad(j\ge k).
\]
This gives a direct quantitative Cauchy witness for the existing native Bishop Sequence.fast-cauchy⇒convergent. The constructive **Lip/bound evidence, all-degree cubature source and Agda inequality transport** remain uninhabited.

Reference: scripts/check_ym_bn_cauchy_schedule_20261117.py, exact rational tests.

## 3. True cyclotomic dyadic Fourier verification (no pi or floating trig)

Let A, M, L be independent powers of 2, with
2(A-1)-1>=d, M>d and L>d. The Chebyshev-II × Fejer-I × circle rule has (A-1)ML positive nodes mathematically.

The algebraic checker computes all angular sums exactly in
\[
K_N=\mathbb Q[z]/(z^N+1),\quad N\in\{A,2M,L\}
\]
using z^(2N)=1, z^N=-1 and formal cos(kθ)=(z^k+z^{-k})/2. Circle sin uses i=z^(L/2). Finite polynomial arithmetic proves the actual discrete Chebyshev-II and Fejer-I filtered moments, all odd-parity cancellations and the full Pochhammer monomial basis for d=3,5,7,9. No classical pi, floating arithmetic or general Legendre roots are invoked.

Reference: scripts/check_ym_dyadic_cyclotomic_full_20261117.py, 1,374/1,374 exact assertions. **This is not an Agda theorem for arbitrary d**: a reusable cyclotomic finite quotient ring and the ordered Bishop dyadic root embedding (including positivity of weights and points on the true sphere) must still be constructed/accepted in Agda.

## Original six open gates and newly reduced cut

1. Finite Fejer product: finite cartesian/positive combinator source; exact dyadic Fourier algebra reference. No kernel acceptance.
2. All-degree Fourier and product cubature: proof strategy sharpens to cyclotomic quotients plus Bishop root tower, but no actual all-degree Agda producer.
3. Effective b_n: explicit *rational* Lipschitz dyadic schedule and tests; source Bishop inequalities/cubature still open.
4. Bishop Haar: actual Sequence Cauchy-limit consumer present; source Cauchy witness not inhabited in Agda.
5. SU2 trace/determinant/unitarity: existing source-written equations; still no kernel acceptance or same-original SUN matrix carrier identity.
6. Original Wilson exponential/Haar/cylinder: Bishop finite Gibbs positivity/normalization and now original second-order Wilson coefficient checks; full source-product Haar, same-carrier cylinder and original real migration open.

There is no license to mark YM.REAL closed. Maintain 19/28 expanded open count until independent kernel and source verification. Attribution: Wilson, Bałaban, Fejer, Stroud, Pizzetti/Folland, Bishop/Bridges, Murray/Csimma, and preceding DASHI original source owners.
