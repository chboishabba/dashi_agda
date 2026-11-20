# Paper 9 — Exact CM derivative certificates from modular polynomial slices

**Subtitle:** A constructive derivation and verification of Chudnovsky-type series  
**Status:** Living working manuscript, 20 November 2026. Independent computational mathematics candidate; not submitted, peer reviewed, or kernel certified.  
**Primary classification:** math.NT; secondary math.NA, cs.SC.  
**Source branch:** PR #1529, baseline 060970700e72e79bc13dfa3829c1e17e61fb036d.

## Abstract

We investigate exact local derivative extraction from symmetric prime-level modular correspondences using a diagonal and one specialized univariate polynomial. Logarithmic differentiation and cyclic root-of-unity filtering reconstruct these slices using integer series arithmetic without materializing a global bivariate coefficient array. At the degree-41 cyclic self-isogeny of the discriminant -163 CM lattice, the construction supplies a route to the singular modulus and almost-holomorphic correction in the Chudnovsky series. Rational root isolation and alternating-series enclosures connect the resulting modular identity to arbitrary-precision evaluation of the original Machin constant. We separate classical analytic inputs, exact executable certificates, representation size, bit complexity and physical execution costs. The novelty of the combined method relative to existing specialized modular-polynomial and nonholomorphic CM algorithms remains under review.

## 1. Introduction and contribution boundary

The proposed contribution is not the discovery of the Chudnovsky formula, binary splitting, cyclic norms, or a general CM theorem. The candidate contribution is an economical joint reconstruction of two slices sufficient for the local cubic jet, followed by exact root isolation, derivative extraction, and constructive certification. This manuscript requires no physical or unification claims and no result from the Clay-facing papers. The Moonshine/369 representation programme is separate.

## 2. Constructive constant

Select the original Machin constant
\[
\pi_M=16\arctan(1/5)-4\arctan(1/239).
\]
The alternating arctangent series supplies rational intervals of width 1/((2N+1)b^(2N+1)). Gaussian multiplication gives
\[
(5+i)^4(239-i)=i(5-i)^4(239+i).
\]
Together with the elementary angle bounds this identifies the selected classical phase. The native Bishop completion and setoid proof is a separate formal supplement; the computational manuscript uses explicit rational enclosures and their classical limit semantics. No inference of real equality from finitely many matching digits is made.

## 3. Classical modular inputs

Use the standard normalized modular forms
\[
E_4=1+240\sum_{n\ge1}\sigma_3(n)q^n,\quad
E_6=1-504\sum_{n\ge1}\sigma_5(n)q^n,
\qquad
\Delta=(E_4^3-E_6^2)/1728=\eta^{24}.
\]
Here q=exp(2 pi i tau), j=E4^3/Delta, and J=qj (not j-744 or j/1728). Inputs are classical modular invariance, holomorphy/nonvanishing of Delta on the upper half-plane, the Fourier expansions, and compactness of X(1). The existing canonical Bishop/Mathlib route in Lean PR #13 and native Agda series/reciprocal modules are source donors, not fresh kernel receipts.

## 4. Direct cyclic norm

For odd prime p, write t^p=q. For an integer series H(t) with H(0)=1, set
\[
N(q)=\prod_{k=0}^{p-1}H(\zeta_p^kt),\quad L(t)=tH'(t)/H(t).
\]
Formal logarithmic differentiation and the root-of-unity sum imply
\[
qN'(q)/N(q)=\sum_{n\ge1}L_{pn}q^n.
\]
The exact integer recurrences are
\[
L_m=mH_m-\sum_{i=1}^{m-1}H_iL_{m-i},\quad
nN_n=\sum_{i=1}^nL_{pi}N_{n-i}.
\]
Integrality follows from the symmetric cyclotomic product and Galois invariance; the implementation checks each division. Truncation and all-degree identities must be distinguished. For J, the inverse eta product coefficients satisfy nB_n=24 sum_{i=1}^n sigma1(i)B_(n-i).

## 5. Modular polynomial slices

Let Phi_p be the standard symmetric modular polynomial. For p odd,
\[
P_p(X)=\Phi_p(X,X),\qquad S_p(X)=\Phi_p(X,K).
\]
The invariant correspondence product for P has pole order 2p at the cusp. Its normalized series equals
\[
q^{2p}P_p(j(q))=(q^{p-1}J(q)-J(q^p))\operatorname{Norm}(J(t^p)-t^{p-1}J(t)).
\]
The fixed specialization satisfies
\[
q^{p+1}S_p(j(q))=(J(q^p)-Kq^p)\operatorname{Norm}(J(t)-Kt).
\]
Subtract consecutive leading powers of j through the constant term. Compactness of X(1) proves the residual with no pole and zero cusp value vanishes. This establishes the polynomial identity on the stated classical inputs, not merely a finite Laurent fit.

## 6. Two-slice cubic jet lemma

For any symmetric polynomial Phi with vanishing constant and linear terms at (K,K), write
\[
\Phi(K+x,K+y)=c_{20}(x^2+y^2)+c_{11}xy+c_{30}(x^3+y^3)+c_{21}(x^2y+xy^2)+O(4).
\]
If P_m=[x^m]P(K+x), S_m=[x^m]S(K+x), then
\[
c_{20}=S_2,\quad c_{30}=S_3,\quad c_{11}=P_2-2S_2,\quad c_{21}=P_3/2-S_3.
\]
Proof: restrict the symmetric Taylor polynomial to y=x and y=0 and compare like powers. For a smooth parametrized branch y=alpha x+beta x^2+O(x^3), the quadratic and cubic coefficients imply
\[
c_{20}(1+\alpha^2)+c_{11}\alpha=0,\quad
(c_{11}+2c_{20}\alpha)\beta=-c_{30}(1+\alpha^3)-c_{21}(\alpha+\alpha^2).
\]
If c11+2c20 alpha is nonzero the latter determines beta. The double-point assumption and simple tangent root must be checked, not inferred from CM alone. This lemma makes no claim that two slices recover arbitrary higher jets.

## 7. CM163 worked example

Take tau=(-1+i sqrt(163))/2, tau^2+tau+41=0. The multiplication matrix on (1,tau) is [[0,-41],[1,-1]], determinant 41. S-invariance gives j(tau)=j((tau+1)/41); hence P41(j(tau))=0.

The tracked diagonal checker reports K=-640320^3, multiplicity two and factor S80 such that P41(X)=(X-K)^2 S80(X). If a_i are coefficients of S80(K+z), integer dominance
2^80 |a_0| > sum_{i=1}^80 2^(80-i)|a_i|
excludes other roots in |z|<=1/2. Combine with the dyadic series enclosure, without a general CM class-degree or integrality premise. These are reported repository receipts pending independent reproduction for publication.

The branch h(t)=-41/(t+1) fixes tau. Its slope alpha satisfies 41 alpha^2+81 alpha+41=0. In the quadratic field, derive beta from the cubic jet, then kappa=2 beta/(alpha^2-alpha). The chain rule yields kappa=j''/(j')^2+2/((2tau+1)j'). Ramanujan differentiation gives
\[
s_2=4+3K/(K-1728)-6K\kappa,\qquad
s_2=(E_4/E_6)(E_2-3/(\pi\Im\tau)).
\]
The tracked slice checker reports s2=77265280/90856689. Reproduce and review all analytic branch and nonzero premises prior to submission.

## 8. Hypergeometric transport

The Ramanujan identities follow from D log Delta=E2, the Serre derivative, and classical dimensions of M4, M6, M8 (D=q d/dq). Set z=1728/j, F=sqrt(E4) with cusp branch F(0)=1, theta=z d/dz. Then Dz=z E6/E4 and
\[
[\theta^3-z(\theta+1/6)(\theta+1/2)(\theta+5/6)]F=0.
\]
Normalized analytic uniqueness gives the factorial series; continuation to the selected negative real q segment requires E4,E6 positive and no singularity. The period identity is
\[
\theta F+(1-s_2)F/6=1/(2\pi\Im\tau\sqrt{1-z}).
\]
With C=640320, B=545140134, A=13591409, verify 144 B^2=163(C^3+1728), (1-s2)/6=A/B. These yield the classical Chudnovsky identity on the stated analytic inputs.

## 9. Certified evaluation

Use the existing integer P/Q/B/T merge and alternating tail enclosure for the weighted hypergeometric sum, plus outward dyadic sqrt10005. The absolute consecutive-term ratio is bounded by 42*1728/C^3<1. The two arbitrary-precision algorithms terminate and, conditional on the classical identity argument, enclose the same constant. Previous reported 100, 1000, 3000 and 10000 decimal-place comparisons are regression targets, not independently reproduced performance results for this draft. Distinguish exact acceptance from approximate timings.

## 10. Complexity and memory: reuse the existing computational programme

### 10.1 Cost model and inputs

Use the existing FibreProgramComplexityExact path-indexed sum/peak consumers, and EfficientRecoverableQuotientExact separation of quotient construction, receipt storage, and reopening. The Karp-21 physical F3/F4 contract requires actual bit widths, signed arithmetic costs, scratch and copying costs, and explicit tape/head movement for a TM implementation. We use a conventional bit-operation model here, not unit-cost unbounded integer arithmetic. No SAT hardness, P=NP or P!=NP inference follows. QuantumExecutionFibreAdapterExact and ShorClassicalQuantumFibreComparisonExact distinguish gate/depth/register/measurement costs from classical transitions; no quantum algorithm or advantage is asserted.

Parameters: p odd prime; b=max(1,bitlength(|K|)); d requested decimal precision (output size Theta(d) bits); M=max series cutoff (<=2p^2 for diagonal, p(p+1) for slice); B_max maximum live integer magnitude bitlength including accumulators, not just final coefficients. Charge addition O(B_max), multiplication M_int(B_max), exact division D_int(B_max), and pointer/index/serialization separately. When p is binary encoded, a bound polynomial in numeric p is not automatically polynomial in log p.

### 10.2 Output size versus construction cost

Dense bivariate slots (p+2)^2; diagonal + specialization slots (2p+1)+(p+2)=3p+3. For p=41, 1849 versus 126, ratio 14.6746. This is only potential coefficient slots; integer heights differ, especially at K, so it does not establish a bit-storage or peak-memory ratio. A coefficient vector costs sum_i(1+bitlength(|a_i|)) plus index/representation overhead.

The current integer implementation has O(M^2) scalar convolution/recurrence operations for J and logarithmic derivative, O(p^2) for norm recurrence, and O(p^3) for the stored power table used in triangular polynomial recovery. Thus a conservative arithmetic count is O(p^4), with a bit-time upper bound conditional on measured/proved B_max of O(p^4(M_int(B_max)+B_max)+p^2 D_int(B_max)); include polynomial translation/isolation and quadratic-field extraction separately (not silently free). This is not yet a complete asymptotic bit bound. Stored series arrays and power tables require O(p^2) simultaneously live coefficient slots, and O(p^2 B_max) payload bits under a common bound; temporary bigint allocation, interpreter structures, provenance, recursion and output serialization must be charged separately. Stream powers or use a triangular composition algorithm as an optimization candidate, not a claimed implemented improvement.

### 10.3 Precision cost

For fixed Chudnovsky constants the number of terms is O(d); unreduced binary-split leaf products have O(d log d) bits by factorial bounds, while the required output itself has Theta(d) bits. Under standard regular multiplication cost assumptions, a balanced split has O(M_int(d log d) log d) multiplication work plus exact final rational conversion/square-root costs. This is a conservative bound; reducing common factors, truncation or alternate arithmetic may improve it. Prove the whole live heap/stack bound, including temporary multiplication and rational normalization, before making a peak-space theorem. Machin comparison must use optimized schedules, matched width, repeat timings and peak RSS, not raw iteration counts. Neither wall time nor number of coefficients is a complexity-class proof.

### 10.4 Planned empirical ledger

For each p,K,d record arithmetic operation counts by type, max and aggregate integer bitlengths, live payload peak, process peak RSS, wall time distributions, certificate serialized bytes and independent verification time. Report construction versus verification and any FRACDASH encoding/decoding time separately. Use local SymPy/Python first, pinned source hashes, fixed versions and no CI dependence. Compare against established direct specialization algorithms and full reconstruction where feasible. Quantum costs are out of scope unless a concrete reversible arithmetic algorithm, ancilla budget and output/recovery cost are actually provided.

## 11. Reproduction, extensions and prior art

Primary tracked scripts (under scripts/):
- check_cm163_modular_diagonal.py
- check_cm163_derivative_slice.py
- check_cm163_dyadic_j_integer_certificate.py
- check_cm163_delta_apartness.py
- check_chudnovsky_differential_weld.py
- check_chudnovsky_exact.py
- check_chudnovsky_bishop_semantics.py

Run from a common checkout so imports resolve. Reproduce all receipts from exact pinned bytes, resolve any failures, save receipts and report versions/CPU. No fresh execution is claimed for this manuscript creation.

Extend to D=-7,-11,-19,-43,-67 using appropriate prime cyclic self-isogenies and verify the Taylor hypotheses individually (special elliptic points and exceptional multiplicities require separate treatment). Audit general bit-height bound in p,b, not merely the output slot count. Add explicit standard bit-machine replay only if needed for the chosen complexity claim. Formal Agda supplement optional for computational submission, mandatory before claiming formal verification.

Prior-art leads (bibliographic and novelty verification pending): Chudnovsky brothers, Ramanujan, Serre, classical modular correspondences and valence formula; Lorenz Milla arXiv:1809.00533; Andrew Sutherland arXiv:1202.3985; Bruinier/Ono/Sutherland arXiv:1301.5672; Computer-assisted construction of Ramanujan–Sato series for 1/pi (2026), DOI 10.1007/s11139-026-01352-2; Arora and Barak, Computational Complexity: A Modern Approach (2009). Cite original authors for their theorems and algorithms; compare actual methods before asserting originality.

## 12. Submission gates

Working draft only. Required: independent local reproduction (including previous reported wall times treated as historical), general lemma exposition and validation, additional CM examples, explicit bit-height/time/peak-memory analysis, baseline comparisons, external literature audit and independent mathematical review. Preserve native Bishop/kernel gaps in formal supplement. No Clay or unification promotion. Paper 8 may cite the completed computational example but is not a prerequisite.
