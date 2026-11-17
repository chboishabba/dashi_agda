# YM.REAL universal S³ → Bishop Haar → original Wilson max-cut, 17 Nov 2026

**Trust:** Mathematical all-degree finite-sum argument plus executable exact
rational/SymPy checks; **NO pinned Agda kernel receipt**, no continuous
Yang–Mills/Clay claim. Source-first: Fejer, Stroud, Pizzetti/Folland,
Bishop–Bridges, Murray/Csimma, Wilson/Balaban and original DASHI owners.

## Universal root-free Fejer/Chebyshev-II/circle mathematical theorem

For any total polynomial degree d choose powers of two A,M,L with
2(A-1)-1 >= d, M>d, L>d. The product sphere rule has (A-1)ML nodes,
using Cheb-II x_a=cos(pi*a/A), weights 2 sin²(pi*a/A)/A, Fejer-I
midpoints y_b=cos((2b-1)pi/(2M)), probability weights

\[
w_b=\frac1M\left(1-
2\sum_{h=1}^{\lfloor(M-1)/2\rfloor}
\frac{\cos(2h(2b-1)\pi/(2M))}{4h^2-1}\right),
\]

and the L uniform circle nodes. Fejer positivity follows from

\[
2\sum_{h=1}^J(4h^2-1)^{-1}=1-(2J+1)^{-1},\qquad
w_b\ge 1/[M(2J+1)]>0.
\]

Let C_A(k)=sum_{a=1}^{A-1}cos(pi*k*a/A).
The finite geometric-series identity gives C_A(k)=A-1 if 2A|k,
-1 for other even k, and 0 for odd k. Consequently the Cheb-II
weighted sum of U_k is [C_A(k)-C_A(k+2)]/A=delta_{k0} through
k<=2A-3. Midpoint cosine orthogonality shows the Fejer-I weighted sum
of T_k equals 1 for k=0, 0 for odd k, and (1-k²)^(-1) for even k>0,
through k<M; this is exactly (1/2)int_{-1}^1 T_k(t)dt.
The L-circle root-of-unity filter annihilates all nonzero Fourier
modes |k|<L. The exact tensor product, parity and beta factorization
therefore match EVERY monomial degree<=d to the functional

\[
H(\prod_i q_i^{e_i})=
\begin{cases}
0&\text{some }e_i\text{ odd},\\
\frac{\prod_i(1/2)_{e_i/2}}{(2)_{\sum e_i/2}}
&\text{all }e_i\text{ even}.
\end{cases}
\]

This is a general mathematical finite-character proof, not just a
fixed-degree numerical extrapolation. Exact finite positive cubature
at each polynomial's degree yields P>=0 on S3 => H(P)>=0,
and H(1)=1 gives |H(P)|<=||P||_infty.

The dyadic nodes can be constructed algebraically by positive
half-angle square roots of primitive dyadic roots of unity, avoiding
the still-open identity between the constructed Bishop Machin value
and the trigonometric period. The ordered-Bishop root-tower
realization and universal Agda Fourier theorem remain OPEN.

New executable:
scripts/check_ym_universal_cubature_producer_20261117.py
accepts --degree d and uses exact F fractions/SymPy, not sampled trig.

## Uniform approximation and actual Bishop Cauchy limit

Set b_n(q,v)=((1+q·v)/2)^n, c_n=(3/2)_n/(3)_n. Exact moments:

\[
H_v(b_n)=c_n,\quad
H_v((1-q·v)b_n)/c_n=3/(n+3).
\]

Choose a positive cubature exact through n+1. Define the polynomial

\[
Q_nf(q)=c_n^{-1}\sum_j w_j f(v_j)b_n(q,v_j).
\]

For |f|<=B and constructive modulus omega_f(delta):

\[
||Q_nf-f||_\infty\le
\omega_f(\delta)+12B/[(n+3)\delta^2].
\]

Take eps_k=2^(-k-3), choose a positive rational delta_k with
omega_f(delta_k)<=eps_k/2, then choose integer n_k with
n_k+3 >=24B/(eps_k delta_k²). This constructs a *direct*
Cauchy estimate for a_k=H(Q_{n_k}f):

\[
|a_j-a_k|\le eps_j+eps_k\le2^{-k-2}\quad(j\ge k).
\]

The actual vendor Sequence.fast-cauchy⇒convergent then supplies the
Bishop-real limit I(f), unique independently of approximation choice.
Positivity, normalization, norm contraction, linearity and setoid
extensionality extend by uniform limits. For L_f-Lipschitz functions
take delta_k=eps_k/(2L_f),
n_k=ceil(96 B L_f²/eps_k³); handle L_f=0 separately.
Executable: scripts/check_ym_effective_cauchy_general_20261117.py.
**Agda gap:** inhabit the modulus/cubature producers and build the
native Sequence._isCauchy term; neither is discharged by SymPy.

## All-degree O(4) and bilateral SU2 invariance

Exact sphere moments have the pairing-tensor formula

\[
H(q_{i_1}\cdots q_{i_{2k}})=
\frac{\sum_{\pi\in Pair(2k)}
      \prod_{\{r,s\}\in\pi}\delta_{i_r i_s}}
     {4\cdot6\cdots(2k+2)}.
\]

It equals the Pochhammer moment by counting equal-index pairings.
Under R in O(4), the delta contractions are invariant because
sum_a R_ia R_ja=delta_ij. Therefore H is O(4)-invariant on ALL
polynomials. Polynomial density/contractivity extend this to I(f).
Left and right unit-quaternion actions are orthogonal maps of R4,
giving actual mathematical two-sided SU2 invariance without
postulating a Haar group-invariance axiom.

scripts/check_ym_su2_o4_invariance_20261117.py:
1,212 exact checks: full monomials through degree 10 plus nontrivial
3/5–4/5 rational orthogonal rotation through degree 6.

## Same-original periodic Wilson polynomial cylinder

scripts/check_ym_original_wilson_polynomial_cylinder_20261117.py
constructs the literal original 4D periodic 4L^4 positive-link
quaternion variables and 6L^4 positive plaquette words

\[
U_{x,\mu\nu}
=U_{x,\mu}U_{x+\hat\mu,\nu}
U^{-1}_{x+\hat\nu,\mu}U^{-1}_{x,\nu},
\quad\mu<\nu.
\]

It expands these ORIGINAL quaternion words in coordinate polynomials,
uses inverse=conjugate on unit S3, and integrates every resulting
monomial by the exact product Pochhammer functional. It has no
preselected first/second Taylor coefficients built into its integral.
Independent source verification:
- L=1 actual commutators: H(D)=9/2, H(D²)=187/8.
- L=2 original six-plane source: H(D)=96.
The existing specialized sparse original L=1 cubic result gives
H(D³)=6445/48; the separate original L>=2 incidence tests certify
the cubic coefficients for L=2,3,4.

With D_L=sum_p(1-ReTr(U_p)/2) in [0,2P_L], P_L=6L^4, and beta>=0,
the polynomial Taylor inequalities are

\[
T_{2m+1}(\beta D_L)\le e^{-\beta D_L}
\le T_{2m}(\beta D_L),\qquad
0\le T_{2m}-T_{2m+1}\le
(2\beta P_L)^{2m+1}/(2m+1)!.
\]

At every m the required original **per-link polynomial** degree
is <=2(2m+1), including the L=1 repeated-link commutator.
Thus positive exact cubature gives rational Taylor endpoints for
rational beta, and a constructive factorial limit for each finite
original cutoff L. The mathematical finite-volume partition obeys

\[
e^{-2\beta P_L}\le Z_L(\beta)\le1,\quad Z_L>0.
\]

The existing original rational periodic plaquette gauge conjugation
and trace class-function owners are joined in
YMClayNativeSixPlaneGaugeSameSourceExact.agda for the side-four
six-plane trace. This source remains uncompiled.

**Important:** different lattice cutoff Gibbs measures are NOT
automatically projectively consistent. An RG/cylinder transfer across
cutoffs is an additional theorem, and is not implied by normalization.

## Honest six-gate accounting

1. Fejer product: mathematical all-degree exact positivity now
   explicit; native Bishop node constructor and Agda acceptance OPEN.
2. All-degree Fourier: exact finite character proof supplied and
   on-demand degree evaluator committed; universally quantified Agda
   Fourier/filter producer OPEN.
3. Effective b_n: constructive all-uniform-modulus bound and dyadic
   schedule supplied; native Bishop inequality/modulus Agda proof OPEN.
4. Bishop Haar: mathematical Cauchy and two-sided invariant extension
   complete on bounded uniformly continuous S3 functions; actual
   Agda producer of native _isCauchy witness OPEN.
5. SU2 matrix: original rational-to-Bishop trace/determinant/unitarity
   candidate source and exact symbolic matrix/O4 verification;
   pinned Agda acceptance and full original SUN carrier weld OPEN.
6. Original Wilson/Haar/cylinder: exact original link/plaquette
   polynomial-cylinder compiler and Taylor endpoint algorithm;
   original typed full product Haar/legacy carrier and RG
   cross-cutoff cylinder consistency OPEN.

None of the above claims an Agda kernel receipt, transitive
postulate-freedom, continuum interacting 4D YM or Clay mass gap.


## Final independent local receipts, 17 November 2026

All checks below were actually executed in the working container, rather
than inferred from the source text. The scripts are also committed.

- Arbitrary-degree rational Pochhammer/Fejer/Chebyshev/circle evaluator
  through degree 11: **4,510/4,510** exact checks.
- Primitive character cancellation in exact cyclotomic quotients,
  Q[z]/(z^N+1), all dyadic orders through degree 11: **496/496**
  checks. The checker computes quotient coefficients explicitly.
- O4 pairing-tensor exact sphere moments and nontrivial rational
  orthogonal rotation: **1,212/1,212** checks.
- Finite Fourier/Cauchy rational and symbolic schedule: **1,510/1,510**
  checks.
- Literal original L=1 cylinder: 4 links and 6 positive plaquettes,
  115 monomials in the deficit, 4,028 in its square,
  H[D]=9/2 and H[D²]=187/8.
- Literal original L=2 cylinder: 64 links and 96 positive plaquettes,
  6,145 deficit monomials, H[D]=96.

Executable repository paths:
scripts/check_ym_universal_cubature_producer_20261117.py;
scripts/check_ym_su2_o4_invariance_20261117.py;
scripts/check_ym_effective_cauchy_general_20261117.py;
scripts/check_ym_original_wilson_polynomial_cylinder_20261117.py.

All are wired to scripts/check_ym_p0_real_carrier_local.sh.
The all-degree mathematical proof uses finite geometric character
identities; sampled symbolic runs do not establish Agda kernel
acceptance. No pinned Agda/Nix toolchain was available. The original
typed YM.REAL/Bishop/SUN/Haar/Wilson source gates remain OPEN.


## 17 November later max-cut: dyadic pairing, all-L partition, cylinder discriminator

The new proof cut is documented in
Docs/physics/YMClayDyadicPairingAllCutoffCylinderMaxCut20261117.md.

The all-d primitive Fourier cancellation can avoid trigonometric
angles and polynomial inversion entirely: for N=2^s, nontrivial k=2^t u
with u odd, pair j and j+2^(s-t-1). Their phases are negatives in
Q[z]/(z^(N/2)+1). The new safe-source finite list theorem proves
opposite-phase block cancellation structurally; the companion
exact checker verified 698027 terms through N=1024.
The remaining source gap is the canonical Fin N reindexing and actual
ordered Bishop dyadic root/weight producer.

The original periodic positive-six-plane Wilson action has mathematically
proved cubic moments at EVERY cutoff:
- L=1: (9/2, 187/8, 6445/48), with commutator geometry.
- L>=2: (P, P^2+P/4, P^3+3P^2/4), P=6L^4, from the
  universal no-three-plaquette mod-2 cycle argument. At L=2 the
  only two-edge overlap graph is C4 and triangle-free.

For every positive integer L and rational beta>=0, an exact
strict-positive partition enclosure is executable:
max(4^(-ceil(12 beta L^4)),T3-integral)
<= Z_L(beta) <= min(1,T2-integral).
This is a finite mathematical Wilson model theorem, not yet the
original Agda/Bishop SUN integral.

**Important correction:** A naive original-link selection L2 -> L1
at fixed beta is NOT a valid consistency theorem. For the selected
origin-link commutator trace f, the first normalized Gibbs derivative
is 25/48 in the one-site model and 0 in the selected two-site
projection; the exact negative-control regression checks all 96
two-site plaquettes. The positive original cylinder research target
must specify a gauge-covariant RG/blocking map and its induced
effective action (plus measure/disintegration laws), not demand
fixed-beta equality for arbitrary link deletion.

All five formal/kernel gates remain open where they need the genuine
primitive Bishop dyadic cubature, its quantitative Cauchy witness,
the full original SUN matrix carrier and an actual RG transfer.
Do NOT label mathematical checked identities as Agda acceptance.
