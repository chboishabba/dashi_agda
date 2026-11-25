# BSD P0 — projected period return and exact fourth-difference unit-factor cut

26 November 2026. Parent c253ac086e1d1cdd43035612364cf4ab3b88ec72, PR #1551. Reuse actual full-distribution kernel and Fricke–Ramanujan–Kloosterman estimates in ClayBSDRankFourAdditivePeriodReturn20261126.md, actual ordinary symbol residues in ClayBSDRankFourActualCyclotomicSymbols20261125.md, full tower and existing complex-order/barycentre owners. This improves the source-specific factorization, NOT the complex rank result.

## A2f — existing theorem and correction of the scope of the residual

Wenzhi Luo and Dinakar Ramakrishnan, Determination of modular forms by twists of critical L-values, https://www.its.caltech.edu/~dinakar/papers/det.pdf, Theorem A and Proposition 2.2 (printed p7), Theorem D (printed p23), actual rendered pages read. Their Theorem A determines a normalized newform using wild p-power characters; Theorem D determines it from one suitable tame branch of its p-adic L-function. At weight2, tame type0 is within the theorem. Thus full trivial tame branch determines the original newform, not just the full ordinary measure. Original finite reflected-vector nonfactorization from A2e remains correct on its declared broad domain, but is NOT an obstruction to recovery on actual modular newforms with the complete projected tower. Attribution to Luo–Ramakrishnan for this established determination result; no priority claim for our explicit kernel version. In particular, one need not prove order4 on every nontrivial Teichmuller sector, and no separate universal sector reconstruction is compulsory. This theorem uses the entire branch and not just its order, first four coefficients, unit status or characteristic ideal.

## A2g — quantitative projected additive return on the original curve

Let q=p^n, h=q/p, n>=2, p=5 or11. Let H_q be the group of (p-1)-st roots mod q. P_H on functions of units is average over H_q, so P_H lambda(a/q)=(1/(p-1)) sum_zeta lambda(zeta*a/q); analogous Dbar_n=P_H D_n. Pairings with the finite additive Fourier kernel exchange projection onto either side. Define Cbar_q(k)=1/phi(q) sum_a P_H lambda(a/q)e_q(-ka). For fixed positive p-unit k,
 Cbar_q(k)=(1/(p-1)) sum_zeta C_q(k*zeta_q).
The prior evenness gives identical contributions from +/-1. We prove that every other summand tends to zero, with a uniform bound sufficient for the actual exponentially decaying Mellin kernel.

Let zeta be a nonrational Teichmuller root, of order d>2, algebraic degree e=phi(d). For p5 the maximal e is D=2, for p11 D=4. For the direct Ramanujan side of the prior Fricke split at y=q^(-3/2), any nonzero alias m must obey m= +/- k*zeta_q mod h. Thus h divides the nonzero integer Norm_(Q(zeta)/Q)(m - (+/- k) zeta), the homogeneous cyclotomic polynomial; every conjugate has absolute value <=m+k. Therefore
 (m+k)^e >= h.
For k<=h^(1/D)/2 this implies m>=h^(1/D)/2. The two residue classes of positive m modulo h have at most two first representatives below h; their total normalized direct contribution is O(h^((-1/2+eps)/D)) from |a_m/m|<=C_eps m^(-1/2+eps). Remaining m in each class >=j h for j>=1 yield O(q^(-1/4+3eps/2)) as in prior alias bound. The reflected Kloosterman sum with u=-k*zeta_q has gcd(u,q)=1, so its normalized total is O((n+1)q^(-1/4+eps/2)); absorb n+1 in O(q^eps). Standard Weil–Estermann bound as in https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/jlms.70291 (1.4). The rational +/-1 sectors have the prior main coefficient and error, now with reflected gcd=1 too. For k in stated range, uniform (apart from original damping term) estimate
 Cbar_q(k)=a_k/((p-1)k Omega_E)+O(q^(-delta)+k^(1/2+eps) q^(-3/2)),
 delta=min(1/4-3eps/2,(1/2-eps)/D), 0<eps<1/6.
For k beyond this range use the prior balanced-height polynomial bound O(q^(1/2+eps)) on any finite contraction, and exponential tail of the same K_p. Thus
 M1 = lim_(n->infty) ((p-1)/2) Omega_E/phi(q) sum_a P_H lambda(a/q) K_p(a/q)
    = lim_(n->infty) ((p-1)/2) Omega_E alpha^n/phi(q) sum_a Dbar_n(a) K_p(a/q).
The second equality uses exact lower-residue cancellation at all p-unit additive frequencies even after averaging H_q. Error O_(E,p,eps)(q^(-delta)); p5 or p11 independently. The factor (p-1)/2 is essential: only two rational tame multipliers survive the fixed additive coefficient limit. This is an explicit bounded-error projected return on the actual original source. It does not contradict the earlier finite-vector collision: generic finite vectors do not have the original cusp split and coefficient growth. No claim finite-level projections already equal the full vector or that this is a new determination theorem.

## A2h — consume actual T^4 and reverse-solve the adjoint kernel

Let g=1+p, addresses j mod h. Write d_j=sum_(zeta in H_q) D_n(zeta*g^j), so P_n(X)=sum_j d_j X^j is the actual finite image of L_p. Set Kbar_n(j)=1/(p-1) sum_zeta K_p((zeta*g^j mod q)/q). Then sum_a Dbar_n(a)K_p(a/q)=sum_j d_j Kbar_n(j). This exactly retains the same trivial tame projection used in the rank4 Iwasawa result.

The established L_p=T^4 U_p, U_p integral unit, gives P_n=(X-1)^4 U_n in the finite p-adic ring, T=X-1. All d_j are algebraic over Q, in Q(alpha), under the earlier exact normalization. In Q(alpha)[C_h] the fourth augmentation multiplication has kernel precisely the uniform Reynolds line and image the augmentation ideal; P_n has zero augmentation. Choose the unique algebraic quotient V_n with zero augmentation and P_n=(X-1)^4 V_n. After p-adic embedding, V_n differs from actual U_n by a multiple of the Reynolds idempotent. Do not assume V_n itself is a p-adic integral unit or that every coefficient of U_n is algebraic. The uniform ambiguity is annihilated in the pairing below.

Writing V_n=sum_j v_j X^j, exact transposition gives
 sum_j d_j Kbar_n(j)=sum_j v_j (Delta_g^4 Kbar_n)(j),
 Delta_g H(j)=H(j+1)-H(j).
Hence the actual unpaid scalar can be written
 M1=lim ((p-1)/2) Omega_E alpha^n/phi(q) sum_j v_j (Delta_g^4 Kbar_n)(j).
This is a single actual branch, with original algebraic finite quotient and explicit real kernel; no identification between p-adic and real log. The zero condition remains exactly the original Lambda''(1)=0.

Could the fourth multiplicative difference itself become small under refinement? No: define L(x)=sum_(i=0..4)(-1)^(4-i)binom(4,i) K_p(g^i x), periodic. Then Delta_g^4 Kbar_n(j)=P_H L(g^j/q), evaluating residues mod q. L has zero mean and is not identically zero: the least positive frequency of K_p with nonzero coefficient is untouched by all i>=1 terms at that frequency, since those have frequencies multiplied by g^i. L is even. For a nonrational zeta in H_q, the pair (a/q,zeta*a/q) over uniform units equidistributes in the two-torus. Indeed a nonzero integer frequency (u,v) gives u+v*zeta!=0 in Q_p, so fixed p-valuation eventually; Ramanujan sum is exactly zero for sufficiently large q. Thus mean of L(a/q)L(zeta*a/q) tends to (int L)^2=0 for these ratios, while +/-1 contribute int L². Average over all j equals unit average of the H-invariant quantity. Consequently
 lim_(n->infty) (1/h) sum_j |Delta_g^4 Kbar_n(j)|² = (2/(p-1)) int_0^1 |L(x)|² dx >0.
This is the actual-kernel proof of failure of the proposed small-fourth-difference argument, not a model perturbation. It does not assert that pairing with the particular v_j cannot cancel. It isolates the remaining arithmetic identity as cancellation against a nonzero explicit real kernel, not an automatic consequence of the T^4 factor or the integral-unit property.

## Actual finite arithmetic checks and source boundary

Original m=1 projected residues from the 244-symbol computation: p5 [1,1,1,1,1], p11 [4,7,0,7,7,7,7,0,7,4,5]. Dividing their canonical polynomials by (X-1)^4 over F_p[X] gives respectively 1 and 5X^6+2X^5-4X^4+3X^3+2X^2+X+4. Values at X=1 are 1 mod5, 2 mod11, agreeing with prior actual unit leading residues. These are finite modulo-p quotient representatives, not the infinite unit factor or its complex embedding. The exact transpose verified on every coordinate test. For the first additive cosine mode, finite projected fourth differences nonzero at all 5,25,11 addresses at original levels q25,125,121 (mode control, not full kernel).

scripts/check_clay_bsd_234446_projected_return.py local normal and -O timeout90 each 20870/20870 PASS, blob 60c95417512f7dc22cb46d4b21eb880176e91ceb byte-matched. Exact Hensel tame roots, homogeneous norm divisibility and height separation through n10 for p-unit k<=64, actual previously computed residue quotient and adjoint checks, finite mode controls. No new cusp evaluation or numeric derivative. Analytic estimates and mean-square result are mathematical proofs, not inferred from finite checks. No native kernel, CI, donor edits or universal promotion.

Remaining selected S: prove actual unit-factor pairing limit zero by independent arithmetic identity (or bypass via original rank-two complex descent); the full branch determination is paid classically and explicit evaluator refined. Not necessary to compute further tame sectors, or rebuild Selmer, Mellin, jets, barycentre or Schur. The complex order remains {2,4}; universal B-M1/M2 unchanged. No claim that another reformulation solves the conjecture.
