# Paper 9 — Exact CM derivative certificates from modular polynomial slices

**Subtitle:** A constructive derivation and verification of Chudnovsky-type series  
**Status:** Living working manuscript, revised 25 November 2026. Independent computational mathematics candidate; not submitted, peer reviewed, or kernel certified.  
**Primary classification:** math.NT; secondary math.NA, cs.SC.  
**Source branch:** [PR #1546](https://github.com/chboishabba/dashi_agda/pull/1546), master-native consolidation of historical PR #1529. Audited parent `1f53737635811b6aee827ada5f36612cc9126b11`; Lean derivative companion `094b4f6cc9c9a653783d7ff42621dc91e06c4d89`. Current status below supersedes historical progress entries.

## Abstract

We investigate exact local derivative extraction from symmetric prime-level modular correspondences using a diagonal and one specialized univariate polynomial. Logarithmic differentiation and cyclic root-of-unity filtering reconstruct these slices using integer series arithmetic without materializing a global bivariate coefficient array. At the degree-41 cyclic self-isogeny of the discriminant -163 CM lattice, the construction supplies a route to the singular modulus and almost-holomorphic correction in the Chudnovsky series. A real-slice root isolation and a reciprocal scalar cross identity eliminate the common Hecke residual before differentiation, avoiding inverse j and quadratic-field inversion in the scalar correction. The earlier cubic identity is retained as an independent verification route. Two ramified elliptic CM cases provide additional exact coefficient tests. Signed alternating brackets and an exact integer width bound reduce constructive certification to a universal rational overlap with the original Machin stages. We separate classical analytic inputs, exact executable certificates, representation size, bit complexity and physical execution costs. Historical source-equivalent native evaluations match decimal hash receipts through ten million digits; exact-head replay and external matched comparisons remain outstanding. The analytic argument uses named classical premises; intended native proof terms are uncompiled and the universal same-real theorem is not yet established. Novelty relative to existing specialized modular-polynomial and nonholomorphic CM algorithms remains under review.

## 1. Introduction and contribution boundary

The proposed contribution is not the discovery of the Chudnovsky formula, binary splitting, cyclic norms, or a general CM theorem. The candidate contribution is an economical joint reconstruction of two slices sufficient for the reciprocal scalar jet (with the cubic jet retained as an independent route), followed by exact root isolation, derivative extraction, and constructive certification. This manuscript requires no physical or unification claims and no result from the Clay-facing papers. The Moonshine/369 representation programme is separate. The Masser invariant and the higher-level derivative method are credited to Masser and Bruinier–Ono–Sutherland (arXiv:1301.5672); the lower-level cubic two-slice consumer is a candidate specialization, not a claim of a new invariant. See the attribution ledger below.

## 2. Constructive constant

Select the original Machin constant
\[
\pi_M=16\arctan(1/5)-4\arctan(1/239).
\]
The alternating arctangent series supplies rational intervals of width 1/((2N+1)b^(2N+1)). Gaussian multiplication gives
\[
(5+i)^4(239-i)=i(5-i)^4(239+i).
\]
Together with the elementary angle bounds this identifies the selected classical phase. The native Bishop completion and setoid proof is a required formal supplement for the P0 independent-certification objective. The original rational Machin stages m_k, their convergence and all-index error 4/25^k are existing source owners; the pinned Bishop order reflection works in both directions. At k=0 use the sharper original 22/7 bound. The companion Lean Machin semantic theorem is an existing donor, not automatic Agda proof import. No inference of real equality from finitely many matching digits is made.

## 3. Classical modular inputs

Use the standard normalized modular forms
\[
E_4=1+240\sum_{n\ge1}\sigma_3(n)q^n,\quad
E_6=1-504\sum_{n\ge1}\sigma_5(n)q^n,
\qquad
\Delta=(E_4^3-E_6^2)/1728=\eta^{24}.
\]
Here q=exp(2 pi i tau), j=E4^3/Delta, and J=qj (not j-744 or j/1728). Inputs are classical modular invariance, holomorphy/nonvanishing of Delta on the upper half-plane, the Fourier expansions, and weight-zero rigidity (equivalently compactness of X(1)). The pinned Mathlib v4.28.0 companion already has original E4/E6 cusp functions, normalized Delta = eta^24, nonvanishing, weight-12 cusp rigidity and nonpositive-weight constancy. Actual Agda divisor-series completion and real-slice/weighted Euler jet proof terms are source owners; source-semantic reflection and new kernel acceptance remain open. Raw lattice G_(2k) is normalized by 2*zeta(2k), not silently equated to E_(2k).

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
The p+1 determinant-p row-lattice charts consist of diag(p,1) and [[1,a],[0,p]] for 0<=a<p. Right multiplication by S,T permutes them up to left SL2Z correction; the adjugate reverses the correspondence. For an r-fold coefficient product the integer pole order is at most p for 1<=r<=p, and p+1 for r=p+1, since the infinity chart has pole p and the others pole 1/p; translation removes fractional exponents. Subtract powers of j through degree zero and apply weight-zero rigidity. Near the cusp the p+1 roots are distinct by leading coefficients and both reversed polynomials are monic, yielding symmetry by equality on infinitely many j-values. This derives the actual correspondence on the named analytic premises. The invariant correspondence product for P has pole order 2p at the cusp. Its normalized series equals
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

The branch h(t)=-41/(t+1) fixes tau. Its slope alpha satisfies 41 alpha^2+81 alpha+41=0. Rather than invert j, put a=j'(tau), b=j''(tau), gamma=h''(tau). Expand both actual branches in epsilon=t-tau. Their quadratic relation is 41 P2=163 S2; their cubic equation, after the quadratic cancellation, gives the denominator-cleared identity
\[
163S_2[(\alpha^2-\alpha)b+a\gamma]
 =a^2(\alpha^2-\alpha)(41P_3-326S_3).
\]
Here a≠0 from the original derivative identity and the selected small-q positivity; S2≠0 from the finite certificate, and alpha is not 0,1,-1. The signed discriminant 82 alpha+81 is ±i sqrt(163); the actual derivative chooses the sign. Thus kappa=(41P3-326S3)/(163S2)=P3/P2-2S3/S2. The chain rule yields kappa=j''/(j')^2+2/((2tau+1)j'). Retain the branch to reopen b; the scalar does not recover it alone. The original q is real negative, and real Fourier coefficients and apartness give real j; complementary-factor dominance on the real half-unit interval suffices. The new forward Laurent/shift replay is source-written and unexecuted, not a new certificate acceptance. Ramanujan differentiation gives
\[
s_2=4+3K/(K-1728)-6K\kappa,\qquad
s_2=(E_4/E_6)(E_2-3/(\pi\Im\tau)).
\]
The tracked slice checker reports s2=77265280/90856689. Reproduce and review all analytic branch and nonzero premises prior to submission.

## 8. Hypergeometric transport

The Ramanujan identities can be derived using two specialized rigidity applications, without general dimension formulas (D=q d/dq). Define E2=DDelta/Delta on the actual normalized discriminant. The weight-12 Rankin–Cohen bracket 3E6 DE4-2E4 DE6 has cancelled derivative anomaly, zero constant and first coefficient 1728, hence equals 1728 Delta by existing weight-12 rigidity. Let x=E4,y=E6,u=3Dx,v=2Dy,d=x^3-y^2,e=E2. Then x^2u-yv=ed and yu-xv=d; determinant -d is nonzero on H, giving u=ex-y and v=ey-x^2. The cusp d=0 is treated separately. The remaining corrected form 12DE2-E2^2+E4 is weight 4 with zero constant. Divide by Delta and apply negative-weight rigidity at -8 to force zero. These are ordinary derivations on the actual derivative transformation and cusp premises. The companion source writes the bracket cusp packaging and first-coefficient transport from actual cusp functions, then the original Euler Möbius chain rules on the open upper half-plane. Its intended unconditional `originalRamanujan46` consumes these terms; the same weight-12 transport gives the intended actual E2 logarithmic anomaly. The subsequent `Paper9E2CorrectedClosure.lean` uses the original analytic eta-product unit U=Delta/q to regularize E2=1+q U'/U, writes the differentiated anomaly, corrected weight-four cusp quotient and negative-weight vanishing. The intended unconditional `originalRamanujanSystem` now covers all three identities. All new source terms are uncompiled, not accepted theorems. Set z=1728/j, F=sqrt(E4) with cusp branch F(0)=1, theta=z d/dz. Then Dz=z E6/E4 and
\[
[\theta^3-z(\theta+1/6)(\theta+1/2)(\theta+5/6)]F=0.
\]
Use the original q-coordinate operator L=(E4/E6)D. For x=E4,y=E6,e=E2 define a=(e x/y-1)/6 and h=x^3/y^2-1. The actual differential system reduces to
\[
La=-a^2/2+h(a/2+5/72),\qquad Lh=h(h+1),\qquad Lz=z.
\]
With F^2=x on the actual binomial branch, LF=aF. Put b=a^2/2+h(a/2+5/72). Then L^2F=bF, and the exact polynomial identity
\[
(a+h/2)La+(a/2+5/72)Lh+ab=h(3b/2+23a/36+5/72)
\]
gives L^3F=h(3b/2+23a/36+5/72)F. Because (1-z)h=z, the displayed hypergeometric ODE follows without an inverse coordinate. The Lean companion now source-writes the normalized branch exp(log(E4)/2), its first derivative, and the cusp-order leading multiplier. The subsequent source-written Lean modules now assemble actual iterated product rules, normalized germ uniqueness, and the literal factorial solution using Mathlib scalar multilinear series: J_d=sum n^d c_n z^n, d=0..3, with common radius at least 1/2, actual derivative-series diagonal gives z J_d'=J_(d+1), and the exact all-index recurrence yields the third-order equation. The intended unconditional local germ identity extends on any connected selected GoodZ domain via analytic uniqueness. The actual small-disk norm bounds now have intended source terms in `Paper9SelectedCMDomain.lean`, reusing the original shifted Eisenstein limits and their equality to the pinned Mathlib forms. For every nonzero q in the disk, the pinned q-parameter lift supplies the original upper-half-plane source; the cusp q=0 is handled separately. The bound on each signed tail is 504/(2^30−1)<1/16. The same original x,y satisfy Re x>0, |x|,|y|≥15/16 and |z|≤1345/3375=269/675<1/2. The connected-disk identity and first Euler jet are now source-written on that domain. Actual CM q membership, real-positive branch and all elaboration/kernel replay remain unpaid. For a nonzero difference germ q^n g with n>0 and g(0)≠0, the actual Euler operator preserves order with leading coefficient n*g(0), while z raises order. The third-order residual therefore has nonzero leading coefficient n^3*g(0). This is the analytic ultrametric filtration, not identification with a finite ternary carrier. The factorial successor ratio is now source-written for every index in Lean, with original CM leaf ratio; native prefix semantics still open. No division at q=0; its constant mode is retained. On |q|<=2^-36 the original divisor bounds give |E4-1|,|E6-1|<1/16 and |z|<=1345/3375<1. The binomial square root and convergent hypergeometric composition both have constant 1. Since U=E4/E6 has U0=1 and z0=0, the coefficient of q^n in L^3 of a difference agreeing through n-1 is n^3 times its nth coefficient, whereas the z-multiplied right side depends only on earlier coefficients. Induction gives equality on the original small disk, without inverse z or analytic continuation. The convergent interpretation and universal factorial recurrence now have intended Lean source terms; original Agda prefix reflection and kernel acceptance remain open. The period identity is
\[
\theta F+(1-s_2)F/6=1/(2\pi\Im\tau\sqrt{1-z}).
\]
With C=640320, B=545140134, A=13591409, verify 144 B^2=163(C^3+1728), (1-s2)/6=A/B. These yield the classical Chudnovsky identity on the stated analytic inputs.

The original degree-82 diagonal and degree-42 fixed slice, their signed cubic correction, the independent forward Laurent substitution, strict complementary-factor dominance, and the original dyadic half-unit enclosure have now been replayed locally from four Git-blob-matched committed Python sources. This is finite certificate acceptance, not analytic or kernel reflection. The actual upper-half-plane fixed-point chart has source-written derivative and orientation lemmas, with signed residual 82 alpha+81=-i sqrt(163), and intended selected-disk specialization. See `Docs/proofs/Paper9LiteralPrefixCMReplay20261125.md` for exact outputs, hashes and reproduction.

The normalized original discriminant supplies a shorter coefficient route. With (U=\Delta/q), (U_0=1), and (a_n=[q^n]E_4^3,b_n=[q^n]E_6^2), the original cusp unit (J=qj) is uniquely forced by (UJ=E_4^3). Thus (u_n=(a_{n+1}-b_{n+1})/1728) and (J_n=a_n-\sum_{i=1}^{n}u_iJ_{n-i}). The new discriminant-based exact integer recurrence matches the original eta-based coefficient producer at all 3363 indices through degree 3362. This eliminates an unnecessary eta logarithmic derivative reflection in the coefficient path, but does not substitute finite agreement for actual analytic coefficient soundness. The Lean companion writes actual SL2 invariance, Hecke chart transport and adjugate reverse root, formal normalized Laurent triangular uniqueness, actual discriminant shift and unit inverse, and actual first/second j jet. The signed correction uses (p=\pi\operatorname{Im}\tau=\pi\sqrt{163}/2). Actual positive period and literal prefix limit are source-written on precisely the original CM root and transverse signed jet premises; all new proof terms remain uncompiled. See `Docs/proofs/Paper9ReverseSolvedActualHeckeDiscriminantPeriod20261125.md` for the all-gate dependency register.

The original variable-degree Hecke correspondence and prime-regular/positive neighbour owners were recovered verbatim from PR #580. The degree-41 instance uses the original Fin(42) fold on ordered lattice rows, retaining the correction and common scale 41 in reverse reconstruction. The pinned SL2Z generation theorem and existing weight-zero rigidity now give intended source proofs of direct diagonal and fixed-slice pole removal: for the actual ramified parameter t, an analytic residual of order at least 3363 (diagonal) or 1723 (slice), before cancellation of the respective t^3362 or t^1722 normalizer, yields a vanishing cusp residual. The actual CM diagonal root therefore need not wait for the full bivariate symmetry theorem. The exact coefficient replay-to-analytic order and dyadic source soundness remain unpaid, and the symmetric Taylor theorem remains on the transverse-jet path. See `Docs/proofs/Paper9RecoveredHeckeOwnersPoleRemoval20261125.md`. All new proof terms are uncompiled.

## 9. Certified evaluation

Use the existing integer P/Q/B/T merge and alternating tail enclosure for the weighted hypergeometric sum, plus outward dyadic sqrt10005. The absolute consecutive-term ratio is bounded by 42*1728/C^3<1. For the actual adjacent source sums S_n=T_n/Q_n, delta_n=P_n p_n(A+Bn) alternates and |delta_(n+1)|*2^41<=q_(n+1)|delta_n|; the original paired slack gives 2T_n>A Q_n for n>=1. Let n=1+floor((k+4)/41), s=2^(k+2), R=floor(s sqrt10005), J=Q_n|delta_n|. With ordered positive prefix pairs (t_l,d_l),(t_h,d_h), K_r=426880, the exact reciprocal-corner width is
\[
u_k-l_k=\frac{K_r(d_l t_h+RJ)}{s t_l t_h}\le 3/s<2^{-k}.
\]
This follows from R<=101s, 8s<=2^(41n), the scaled defect bound and positive lower planes. It is independent of the analytic Chudnovsky identity; intended native totality/width terms are uncompiled. For c_k=(l_k+u_k)/2 and m_k the literal Machin stage, retain both rational crosses l_k<=m_k+e_k and m_k<=u_k+e_k, where e_0=22/7 and e_k=4/25^k for k>=1. The exact combined-radius bound is |c_k-m_k|<=width/2+e_k<=4/(k+1). Universal crossed endpoints, not finite hashes, are the outstanding F5 theorem. Interval production totality differs from decimal-floor termination: exact boundary apartness (e.g. irrationality of pi) and fair refinement are required. Historical exact decimal comparisons and source-equivalent native runs are recorded below, not exact-head replay. Distinguish exact acceptance from approximate timings.

For the original signed raw binary-split prefix, B_split=1, U_n=P_n/Q_n and S_n=T_n/Q_n satisfy U_(n+1)=U_n p_n/q_n and S_(n+1)=S_n+(A+Bn)U_(n+1). The new native rational semantics source retains the literal positiveView, while the Lean target consumes the all-index factorial recurrence and convergent weighted hypergeometric jet. Agda factorial/source reflection and kernel acceptance remain unpaid; no finite prefix test proves the infinite same-real claim.

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

Extend to D=-7,-11,-19,-43,-67 using appropriate prime cyclic self-isogenies and verify the Taylor hypotheses individually (special elliptic points and exceptional multiplicities require separate treatment). Audit general bit-height bound in p,b, not merely the output slot count. Add explicit standard bit-machine replay only if needed for the chosen complexity claim. Formal Agda supplement may be separated for a narrower computational submission; it is mandatory for the stated P0 original-Bishop independent-certification objective.

Prior-art leads (bibliographic and novelty verification pending): Chudnovsky brothers, Ramanujan, Serre, classical modular correspondences and valence formula; Lorenz Milla arXiv:1809.00533; Andrew Sutherland arXiv:1202.3985; Bruinier/Ono/Sutherland arXiv:1301.5672; Computer-assisted construction of Ramanujan–Sato series for 1/pi (2026), DOI 10.1007/s11139-026-01352-2; Arora and Barak, Computational Complexity: A Modern Approach (2009). Cite original authors for their theorems and algorithms; compare actual methods before asserting originality.

## 12. Submission gates

Working draft only. Current integrated gates: A2 intended original Ramanujan system source-written, with all elaboration and kernel replay still open; A3–A5 actual degree-41 Laurent/CM certificates and signed Taylor binding; A6–A7 convergent original-q identity and positive period normalization; F1 actual factorial series and F2–F4 source-written positivity/width/totality; F5 universal rational overlap with the original Bishop real; F6–F8 exact native correspondence, digit termination and kernel acceptance; F9 calibrated external comparison. Historical source-equivalent native hashes through 10M digits and COMP5j's 148,669,512 managed-live peak bytes (166,072 KiB VmHWM, single run) are evidence, not an external record. COMP6 candidates remain unexecuted. Required for publication: independent exact-source reproduction, additional CM examples and literature/novelty audit, whole bit-height/time/peak-memory accounting and mathematical review. No Clay or unification promotion. Paper 8 may cite the completed computational example but is not a prerequisite.

### 12.1 Scope of the secondary 369 donor

The existing signed Tate/eta coefficient 66-12=54 and integer v3 cancellation are distinct from the original word 66 (6→6, two neutral coordinates). The original 13-stage source uses slot3/6/9 = negative/neutral/positive and word/pants/cylinder round trips; fixing 66 leaves an eleven-coordinate suffix, not global zero. No semantic Tate-to-word map or equivariant identification follows from the numeral. The classical level-three Hauptmodul chart and this typed fibre geometry are secondary donors, not new pi proof prerequisites.

**Current controlling register:** `Docs/proofs/Paper9IntegratedFrontier66Cusp20261125.md` and `Docs/proofs/Paper9GeometryFirstEndpointClosure20261125.md`. The following chronological sections are historical evidence, not independent current status declarations.


## 20 November — independent replay and preliminary uniform bit-height lemma

Local Python 3.13.5, SymPy 1.14.0. Exact Git blob readback at
7d5be142d881f810740b5f8de4cf858e7cffc905 matches five mounted scripts.
The local check_chudnovsky_exact.py initially lacked the committed
positive precision assertion; restored it and verified blob
eb58d9dd1d0a2e0d62e9ef16a0ad1ee9703e0e6b before rerunning.
Exact-source results: CM163 delta apartness PASS (0.02539 s),
hypergeometric differential weld and 24 ratios PASS (0.19618 s),
degree-82 diagonal root isolation PASS (9.0771 s internal,
10.41 s process elapsed, max RSS 130884 KiB via GNU time).
Root K multiplicity 2, dominance floor 6593105375567751.
Gaussian phase, 771 Ramanujan coefficients, 4 matched intervals
PASS after dependency correction. Single-run Machin/CH milliseconds:
100: 0.229/0.174; 1000: 2.255/1.068; 3000: 16.281/5.027;
10000: 119.085/48.259. CH standalone seven-run medians in ms:
0.051575, 0.744255, 5.472865, 33.064358.
Full derivative slice replay timed out (120 s limit) after diagonal
stage printed 9.2683 s; prior 31.910 s receipt NOT independently
reproduced. Dyadic enclosure not rerun in this packet. No CI/kernel.

### Uniform bit-height bound for the integer construction (proof candidate)

Let b=max(1,bitlength(|K|)), M<=2p^2. J=q*j has nonnegative integer
coefficients. On q=1/2, E4<=1+240 sum n^4/2^n=36001<2^16.
The inverse eta product has logarithm <=24 sum 2^-n/(1-2^-n)
<=48; exp(48)<2^96. Hence J(1/2)<2^144, and J_m<=2^(144+m).
All positive inverse-eta recurrence partial sums are bounded by
their final numerator; nonnegative convolutions likewise. For either
H construction, |H_m|<=A^m for m>=1 with A=2^(b+150).
The formal inverse coefficients obey |[t^m]1/H|<=2^(m-1) A^m
for m>=1 by ordered compositions (constant coefficient 1).
Absolute sums of the products in the logarithmic derivative recurrence
are bounded by O(m (2A)^m) using that same inverse majorant.
Consequently all L recurrence terms and partial accumulators have
O(M(b+1)) bits. For N, its p-factor product gives
|N_n|<=A^(pn) binom(pn+p-1,p-1)<= A^(pn) 2^(pn+p).
The recurrence intermediates L_(pi)*N_(n-i), their sums and exact
division numerators retain O(pn(b+1)+p+log(n+1)) bits.
Normalized correspondence products inherit O(p^2(b+1)) bits.

For the triangular extraction, [q^k]J^d <= 2^(144d+k)
binom(k+d-1,d-1) for d>=1, so all power table entries for d,k<=2p
have O(p) bits. At each leading-coefficient elimination the maximum
absolute residual can grow by at most 1+max coefficient of J^d,
i.e. a factor 2^O(p). Across at most 2p+1 eliminations this adds
O(p^2) bits. Thus B_max=O(p^2(b+1)) for the actual integer series
and triangular reconstruction, including scalar accumulators.
This does not yet cover SymPy's general internal shift/exquo/invert
temporaries, allocator overhead or a physical tape simulation.
The existing O(p^4) scalar operation and O(p^2) payload slots
then imply O(p^4(b+1)) live integer payload bits for that stage.
With schoolbook arithmetic, a conservative construction time bound
is O(p^8(b+1)^2), not a bound polynomial in log p.
General proof should be reviewed, and actual operand instrumentation,
full derivative replay, dyadic replay and allocator accounting remain open.


## 20 November — GMP/Newton exact construction and complete CM163 replay

Prior head 3b32bcb374cfd52cc2fe0e824f6b05d04f9f6cce.
Scalar defaults preserved in check_cm163_modular_diagonal.py and
check_cm163_derivative_slice.py, with explicit optional logder_fn hooks
(commits 50d40405b26dbf2620270c7f5b18b8206250f932 and
2f8b5e594e95a4b487d376e701c19fd909445c27).
New check_cm163_fast.py fc51d0f1636bcc2cc7b71f95225304aa2a86ed08
uses native GMP signed Kronecker multiplication via ctypes (Linux GMP
ABI), Newton inversion of H with constant coefficient 1 and exact
checks H*G=1 and H*L=tH' modulo the requested truncation.
For operand coefficient counts m,n and maxima U,V, choose byte-aligned
radix R>2 min(m,n) U V. The signed coefficient of the true product
lies strictly inside (-R/2,R/2). Evaluating at R, multiplying
integers and centered digit extraction with carry recovers each
coefficient inductively. Truncation uses the low bits of the product.
Newton identity 1-HG_new=(1-HG)^2 gives doubling and uniqueness of L
from H*L=tH'. This proves equality to the scalar recurrence for
unit H, not a claim of independent analytic modularity.
The original other construction and derivative consumer are unchanged.
64/64 signed convolution and 64/64 inverse/logder scalar comparisons,
8/8 complete polynomial comparisons at p=3,5,7,11 passed locally.
An initial proof-of-concept run timed out with large Python modulo;
using a bit mask resolved the truncation issue. Final code uses explicit
hooks, no dynamic source substitution. A separate unmodified scalar
replay also completed, 33.01158858 s while concurrently running other
tests; do not use that as a controlled speed benchmark.

Sequential reproduction runner check_cm163_backend_parity.py
9adb75153854c4a8a019c6a05f8e8fb3b6313940 runs independent subprocesses
and checks exact byte equality of both unshifted polynomial arrays
serialized as signed hexadecimal JSON, not just hashes or final s2.
Executed locally with Python 3.13.5, SymPy 1.14.0, GMP 6.3.0,
Linux x86_64 glibc 2.41, Intel Xeon Platinum 8573C.
All exact source blobs matched: diagonal add8e35866aa1e9f379b4a57059c4487e4c7241c,
slice 0c1f7d04618943d6b9941f433ceed8c5cd9fd590,
fast 6c1a051c2832d9afd549680b3a6401383023989e,
runner d737ef34938ee5c1557e08ee322f785c5d2ec7d8.
Both full p=41 runs PASS, s2=77265280/90856689 and
kappa=-77859659565707/19943834790540897829879824384000.
126 output coefficient slots, aggregate signed-magnitude payload
241632 bits (one sign bit per slot), max output coefficient 3371 bits,
61113 serialized bytes; full byte-for-byte coefficient parity PASS.
Measured single sequential run (seconds; imports excluded):

| Backend | Diagonal | Construction total | Complete incl. derivative/serialization | Peak RSS KiB |
| --- | ---: | ---: | ---: | ---: |
| Scalar | 8.899486372 | 31.606400973 | 31.649009698 | 143412 |
| GMP/Newton | 4.252409969 | 16.159672922 | 16.208337047 | 533716 |

Speed ratio 1.95x; RSS ratio 3.72x. 52 packed multiplication calls
on the fast full construction; maximum packed operand 204771028 bits.
This is distinct from maximum individual coefficient width, final
certificate size or live integer payload. Resource receipt:
Artifacts/paper9/cm163_backend_parity_20261120.json (commit 684059f458297ed9dbb7e158d83f895cc4bfec45).
Reproduce: python scripts/check_cm163_fast.py for regressions and
full fast derivative, then python scripts/check_cm163_backend_parity.py
for sequential full exact comparison. No CI/kernel required.
Historical derivative result now independently reproduced. Dyadic
enclosure replay remains open; P9.03 partial for entire suite.
P9.04 partial (packed counts/operand width and output coefficient
heights, not every scalar intermediate); P9.06 measured two backend
RSS and serialized slice size, not a general memory theorem or
full certificate size. No claim of an unconditional speedup, statistical
benchmark, smaller peak memory, or asymptotic improvement for all stages.
Next: block or height-adaptive packing/CRT, charge repacking and all
GMP/Python temporary buffers, preserve exact parity; retain scalar
backend for memory-constrained runs. Generalization and external
baselines remain open. No new formal analytic or kernel closure.


## 20 November — codec-inspired support-window Newton backend

Implemented scripts/check_cm163_window.py at commit
245dd9739108f80b296f304316642355b8026601, exact local Git blob
f5f578445d1ac1bfa4f46a0de62f72cc9320428f verified after connector write.
Reuses original GMP mul and unchanged diagonal/specialized polynomial consumers.
Donor inspiration: TriadicResidualMaskSignCodec, TriadicExplodedTransformCodecFormalism,
BalancedTritBitFibre, DNACarrierFibre, DNAProductionCodec and the actual
run_triadic_flagship_benchmark.py. These are structural analogies, not a claim
of literal ternary entropy coding or DNA execution.

For H(0)=1 and HG=1 mod t^m, define r=-[t^m,...,t^(k-1)]HG,
k=min(2m,N). Then G_new=G+t^m*(G*r mod t^(k-m)); the known
prefix stays unchanged. Partition operands into blocks of 256 coefficients.
Omit all-zero blocks and pairs outside requested output window; choose
forward or reversed truncated multiplication according to the shorter
local output prefix. Reversal is exact since rev_(a+b)(AB)=rev_a(A)rev_b(B).
Accumulate each pair at its exact index offset. Existing GMP mul chooses
a safe local signed radix per pair. If individual coefficient heights
are bounded by B, a packed operand uses O(s(B+log s)) bits for block
size s, rather than O(M(B+log M)) for a uniform full operand; source,
output, copies, allocation and multiplication workspace are separate.
No global peak-memory theorem asserted. The 256 block length is a
selected experimental constant, not an optimized parameter.

Local Python execution: 128 random signed window comparisons against
scalar convolution; 128 logder comparisons against dense fast backend;
8 full small-prime polynomial comparisons against scalar (p=3,5,7,11).
All PASS. Full degree-41 window derivative run PASS with exact H*G=1
and H*L=tH' at full truncation, kappa and s2 unchanged.
Window diagonal 5.738555279 s, cumulative construction 18.666320395 s,
total derivative 18.706544707 s, max RSS 223188 KiB, 579 packed calls,
max operand 22816464 bits. This process included small regressions.
Separate window construction/serialization run 18.577457777 s,
RSS 221560 KiB, saved signed hexadecimal coefficient arrays.
Fresh dense fast runner: diagonal 4.524124461 s, construction
17.555023721 s, total 17.608450256 s, RSS 521212 KiB,
52 calls, max operand 204771028 bits.
Byte comparison of both complete serialized arrays PASS (126 slots).
Fresh scalar comparison attempt exceeded 120 s tool limit (after window
construction); do not claim direct fresh scalar p=41 comparison in this
packet. Transitive scalar parity uses previous recorded dense/scalar
receipt. These single process observations are not a controlled
statistical benchmark. Historical scalar timings retained as historical.

P9.M1-M4 implemented together; no ablation yet. Largest packed operand
8.97x smaller; full-run RSS 57.2% smaller vs fresh dense run, with roughly
6% construction-time overhead. Different process scopes explicitly noted.
Next: geometric predictor as exact factorization or quotient, not merely
subtracting a large leading power; triadic/height-adaptive block sizes,
ablation and repeated sequential memory/runtime measurements, then CRT.
Native ternary coding, FRACDASH execution, dyadic enclosure replay and
additional CM discriminants remain OPEN. No Agda or CI execution.


## 20 November — bounded residue SWAR-inspired execution and deterministic CRT

Source commit ab90beec7eeadb73489bfc5ecad253cd53086b05:
scripts/check_cm163_residue_swar.py, local and committed Git blob
2feac81f52f2b9b941444e2e8b3e260004a0e4f2. Dependencies checked locally:
fast 6c1a051c2832d9afd549680b3a6401383023989e,
diagonal add8e35866aa1e9f379b4a57059c4487e4c7241c,
derivative 0c1f7d04618943d6b9941f433ceed8c5cd9fd590.
Python 3.13.5, SymPy 1.14.0, x86_64. No CI/kernel run.

Reuse provenance: TriadicSupportMaskSWARExecutionExact has a receipt for
eight independent byte lanes and 8^8 exhaustive packed words;
TriadicSignCompactionSWARExecutionExact has eight lane factorized encode
and 27^5 core product receipt; TriadicCodecSWARPortableKernelCrossPollinationExact
separates representation from execution; RSA260TriadicSWARExecutionRoadmapCrossPollinationExact
supplies bounded ABI / scalar oracle / exact source / lane execution /
domain parity pattern. This new backend uses GMP Kronecker coefficient
lanes and serial residue rings, NOT fixed-word hardware SWAR or SIMD.
No claim of reusing the actual C byte-popcount kernel for big-integer multiplication.

Reduce every coefficient mod r after each convolution; use carry-isolated
packing via original fast.mul. For operand sizes m,n and residues <r,
the signed radix bound R>2 min(m,n)(r-1)^2 suffices. For b_r=bitlength(r),
packed operand size O(M(b_r+log M)) rather than O(M B_max).
Use Newton active residual update and check HG=1, HL=tH' in every ring.
Norm division by k is modular inversion, legal because moduli are powers
of distinct small primes >82 (trial division establishes primality).
Reconstruct only the two final polynomial vectors by incremental CRT,
not the high-height intermediate inverse series. J generated once using
original exact j_unit; both slices use prefixes of that same series.

Deterministic height proof (not historical output width):
Let n be slice degree, H finite truncated input in t with t^p=q, g the
normalized prefactor in q, J the unit series truncated to degree n.
Define Q=g*Norm(H), whose first n+1 coefficients agree with the original
construction. Norm is invariant under t -> zeta*t, a polynomial in q,
and on |q|=2^-p its magnitude is <= (sum_i |H_i|2^-i)^p.
For formal coordinate w=q/J, residue change of variable gives the recovered
coefficient c_d=[q^(n-d)] Q J^-d (1-qJ'/J), 0<=d<=n:
take the residue of w^(d-1) P(1/w) dw and substitute w=q/J.
Only first n+1 coefficients enter. Exact dyadic inequalities in code prove
|J-1|<=1/4 and |qJ'|<=1/4 on the circle; hence |J^-d|<=2^d and
|1-qJ'/J|<=2. If H_abs<=2^h and g_abs<=2^a from exact coefficient
sums, Cauchy gives |c_d|<=2^(p*h+a+1+d+p(n-d))<=2^E,
E=p*h+a+1+pn. For both CM163 inputs computed E=5086.
CRT product strictly >2^(E+1) makes centered reconstruction unique;
no reliance on historical coefficient list or probabilistic stopping.
The optional reference argument only compares after reconstruction.
This is a mathematical bound conditional on the existing slice construction;
no fresh proof of classical modularity is asserted. The dyadic checks
are specific to p=41, not a uniform small-prime theorem.

Observed separate live local runs, including original J generation,
all modular inverse/logder checks, CRT, byte serialization, optional
reference equality and exact derivative consumer:
| Target modulus bits | CRT rings | Final product bits | Time s | RSS KiB | Largest packed operand bits | Packed calls |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 768 | 7 | 5396 | 6.693572904 | 143340 | 5245493 | 1246 |
| 384 | 14 | 5413 | 6.625785951 | 137292 | 2689990 | 2492 |
Both PASS all 126 exact coefficients against the existing local
cm_fast_coeffs.json, and kappa=-77859659565707/19943834790540897829879824384000,
s2=77265280/90856689. First output file also independently cmp-equal to
the reference. J/setup times 3.090534929 and 2.898582786 s.
Reproduce without a reference:
python scripts/check_cm163_residue_swar.py --bits 384 --output coeffs.json
Reference optional: --reference existing signed-hex JSON.
Reported historical scalar 31.649 s /143412 KiB and dense 16.208 s /
533716 KiB are separate prior runs, not controlled fresh comparisons.
384 target is ~134.07 MiB RSS, ~76x smaller largest packed operand than
historical dense; runtime ~6.63 s. Only two single observations; no
statistical, general peak-heap or hardware-throughput claim.
P9.M7 deterministic streamed CRT implemented and full CM163 parity PASS.
P9.M5 geometric compression remains open and is no longer prerequisite.
P9.M10 fixed-width SWAR lane reduction / SIMD implementation OPEN:
derive overflow-safe packed modular add/sub/mul, compile scalar oracle,
exhaustively test feasible domains and compare full same-source residues.
Next optimize shared J construction (~3s), width/block ablations,
native fixed-width lanes and generalization; charge all intermediate
storage/CRT reconstruction, retain original scalar and dense oracles.


## 20 November — fast shared J and native fixed-width SWAR primitive gate

New scripts/check_cm163_fast_j.py commit b808d8f511b0cf1e36a9f3ca4eeecd60ca66ef11
blob b3b0e21af92c80c38e26ccba811514f7b6ab1bef.
Use Euler pentagonal theorem P=prod(1-q^m)=1+sum_{k>=1}(-1)^k
(q^(k(3k-1)/2)+q^(k(3k+1)/2)), exponentiate P^24 by repeated squaring,
invert by active-residual Newton, multiply by E4^3. Attribution Euler and
classical eta normalization; no claim of new series identities.
Exact checks P^24*inv=1 and P^24*J=E4^3 modulo q^(n+1).
All 3323 coefficients at n=3322 agree with original scalar j_unit.
One same-process comparison, fast first: 0.202099954 s vs 2.824831598 s;
34 GMP calls, maximum packed operand 3721676 bits. Six smaller prefixes
(0,1,2,10,31,64) also PASS. No statistical claim.

Earlier experimental injection of j_unit into unchanged CRT consumer
completed in 3.442226512 s, RSS 137748 KiB, 126 exact coefficients equal.
Committed explicit --fast-j option in check_cm163_residue_swar.py at
45b4c6bee64889f152c951d33905ec46c2957450, blob cc611e4540eaa07cda9062425ad42382672ecb76.
Exact committed source replay (verified local blob):
python scripts/check_cm163_residue_swar.py --bits 384 --fast-j --reference cm_residue_coeffs.json --output cm_fast_j_coeffs.json
J/setup 0.212358979 s, total 3.541941401 s, RSS 138372 KiB,
14 CRT rings, modulus 5413 bits, certified E=[5086,5086],
2526 packed calls, max operand 3721676 bits. All 126 coefficient
bytes match previous local residue arrays, same kappa and s2.
Reference optional; not used for stopping or reconstruction.
The fast-j option leaves scalar default unchanged. Historical scalar
31.649 s comparison is cross-run only; latest exact committed replay
~8.94x historical speed, RSS ~135.13 MiB.

Native SWAR primitive source scripts/check_cm163_swar_lanes.c commit
95dedf01e3e0eb23560ec978de89f82d55de47d8, blob
dcfd038bee6d26385a6f0cf71b36aa154de38446.
Four 16-bit lanes in uint64_t, 14-bit residue payload, common modulus
2<=p<=16384, inputs canonical. Addition: s=a+b <2p per lane, guard
bit 15 prevents cross-lane borrow in (s|GUARD)-p; guard predicate
selects s or s-p with a replicated full-lane mask. Subtraction uses
a+(p-b), whose maximum <=2p-1 and hence still below guard.
Multiplication uses 14 bounded double-and-add iterations, bit selection
via disjoint full-lane masks. This proves lane isolation under the
stated preconditions; no hardware SIMD or constant-time claim.
Compiled locally gcc -std=c11 -O3 -Wall -Wextra -pedantic.
Executed 6889 exhaustive scalar pair cases p=83 embedded in four
correlated lanes, plus 100000 pseudorandom four-lane words p=16381;
all 4 lanes x 3 operations checked per case. Not exhaustive over all
independent four-lane words. This C primitive is NOT integrated into
the 384-bit CRT backend; no end-to-end native SWAR speed claim.
P9.M10 primitive PASS, full modular-polynomial SWAR backend OPEN.
P9.M11 shared J generation PASS. Dyadic replay and other CM cases
remain open.

External SOTA/novelty boundary: compare Sutherland, On the Evaluation
of Modular Polynomials (2013), https://mathweb.ucsd.edu/~kedlaya/ants10/sutherland/paper.pdf;
Evaluation of Modular Polynomials from Supersingular Elliptic Curves
(2025), https://portal.fis.tum.de/en/publications/evaluation-of-modular-polynomial-from-supersingular-elliptic-curv/;
Hemmecke, Paule, Radu, Computer-assisted construction of Ramanujan-Sato
series for 1/pi (2026), DOI 10.1007/s11139-026-01352-2;
FLINT polynomial algorithms https://flintlib.org/doc/algorithms/polynomials/overview.html.
Existing efficient evaluation, CRT and automated series derivation
preclude novelty claims for those techniques alone. Our proposed scope
is direct certified CM cubic jet with two slices and exact height bound.
SOTA not established: no matched external execution baseline yet;
PARI/Sage/FLINT not installed in this local environment (gp absent,
no libflint in ldconfig). Need cold/warm matched outputs, exact height
guarantees, identical hardware, repeated time and RSS, general levels
and comparison against direct derivative/jet methods as well as full Phi.
No new Agda/CI run.

## 20 November — attribution-first source ledger and odd-prime family replay

Standing PR #1444 attribution policy: preserve original authors, exact primary
source, earlier DASHI producer and revision; distinguish quotation, theorem
intake, conceptual analogy, independent rediscovery, implementation, extension,
execution, formalization, kernel acceptance and external validation. Cite
external researchers, do not imply collaboration or co-authorship unless
actually evidenced. Missing metadata is an explicit residual. Reuse before
construct. No provenance inferred from a similar formula.

Primary bibliographic records checked 20 November 2026:
- Andrew V. Sutherland, On the evaluation of modular polynomials (2013),
  DOI 10.2140/obs.2013.1.531, arXiv:1202.3985. Direct specialization,
  CRT evaluation; established prior art, not implemented here.
- Maria Corte-Real Santos, Jonathan Komada Eriksen, Antonin Leroux,
  Michael Meyer, Lorenz Panny, Evaluation of Modular Polynomials from
  Supersingular Elliptic Curves, arXiv:2506.15429 (2025), proceedings
  DOI 10.1090/conm/840/16823 (2026). Supersingular evaluation and memory
  complexity under their stated model; no comparative run yet.
- Ralf Hemmecke, Peter Paule, Cristian-Silviu Radu, Computer-assisted
  construction of Ramanujan–Sato series for 1/pi, Ramanujan Journal 69,
  article 73 (2026), DOI 10.1007/s11139-026-01352-2. MultiSamba and
  ModFormDE, with lineage to Radu (2015), Hemmecke (2018), Paule and
  Radu (2021); author supplement
  https://www3.risc.jku.at/people/hemmecke/papers/oneoverpi/.
  No FriCAS execution or reuse of their code claimed.
- Reinier Bröker, Andrew V. Sutherland, An explicit height bound for
  the classical modular polynomial (2010), DOI 10.1007/s11139-010-9231-8,
  arXiv:0909.3442. Prior explicit height bounds; compare our slice bound
  with specialization of their bound before claiming improved theory.
- Reinier Bröker, Kristin Lauter, Andrew V. Sutherland, Modular polynomials
  via isogeny volcanoes (2012), DOI 10.1090/S0025-5718-2011-02508-1,
  arXiv:1001.0402. CRT isogeny-graph construction, established prior art.
- David Masser, Elliptic Functions and Transcendence (1975), original
  CM derivative observation; exact original lemma inspection pending
  (identified through cited Bruinier/Ono/Sutherland paper, not independently
  read from Masser's book). Jan Hendrik Bruinier, Ken Ono, Andrew V.
  Sutherland, Class polynomials for nonholomorphic modular functions,
  arXiv:1301.5672, CRT algorithm building on Masser's observation.
  Our chain-rule derivation is an independently constructed route,
  not discovery of the modular derivative/CM relation. Compare both
  normalization conventions and derivative orders explicitly.
- FLINT: David Harvey, William Hart (founders), Sebastian Pancratz,
  Fredrik Johansson and all relevant contributors; official
  https://flintlib.org/authors.html and https://flintlib.org/citation.html.
  External baseline, not executed or linked in current code.
- Classical Machin, Euler pentagonal theorem, Eisenstein, Dedekind eta,
  Klein j, Ramanujan, Serre derivative, Chudnovsky brothers, Newton
  inversion, Kronecker substitution, CRT and Bishop completion retain
  their historical attribution. Exact original edition/page ledger
  remains pending where not verified. Lorenz Milla arXiv:1809.00533
  remains related derivation lead. Do not claim classical results new.

Evidence boundary: bibliographic records and abstracts inspected; detailed
theorem-by-theorem comparison and benchmark replication still OPEN.
No claim that cited authors collaborated, no co-authorship trailers for
citation alone. Existing Aristotle/Harmonic attribution retained on actual
donor artifacts. Original DASHI codec, SWAR and Karp owners preserved.
Our candidate contribution is the specific two-slice cubic-jet execution,
cyclic-norm reconstruction and explicit slice certificate integration,
subject to prior-art review. SOTA remains OPEN.

New source scripts/check_cm_prime_family.py commit
ef295d0d7390475f1c4cd417be28866b04f5ff0b. Executed locally with SymPy
and original scalar/GMP constructors; classical K supplied, not derived.
For odd prime p, tau=(-1+i sqrt(4p-1))/2, h=-p/(tau+1),
alpha satisfies p alpha^2+(2p-1) alpha+p=0. Same cubic formula
and s2 normalization as CM163. Exact P/S parity at p=3,5,11,17,
double-point conditions, quadratic tangent and invertible denominator,
rational kappa verified. Results (one local run, seconds include both
backends):
D=-11 p=3 K=-32768 s2=32/77 0.030947798;
D=-19 p=5 K=-884736 s2=32/57 0.010402145;
D=-43 p=11 K=-884736000 s2=640/903 0.084691348;
D=-67 p=17 K=-147197952000 s2=33440/43617 0.521738573.
No independent analytic CM value or root isolation for these four cases
yet. p=2 (D=-7) excluded by odd-prime sign convention. P9.M13 partial PASS.
Local gp/sage absent, ldconfig no libpari/libflint, FriCAS absent;
no external runtime benchmark. Next generalize CRT radius for small
p and root enclosure, compare Masser formula and run pinned external
baseline in user environment. No Agda/CI execution.


## 20 November — Masser normalization and rational-only cubic jet

Primary text inspected: Bruinier, Ono, Sutherland, Class polynomials for
nonholomorphic modular functions, arXiv:1301.5672v3 (28 Jan 2015),
pp.2,9–10, eqs. (1.2), (2.6)–(2.9), Lemma 2.3. The authors credit
David Masser, Elliptic Functions and Transcendence, LNM 437 (1975),
p.118 and Lemma A2. Masser's original book not directly inspected.
Their gamma = s2/(6K) -(7K-6912)/(6K(K-1728)) equals -kappa by
our earlier normalization. Prior art owns this invariant, not DASHI.

Their formula at level |D| is gamma=(2 beta02-beta11)/beta01,
with beta01!=0 under their hypotheses D<-4, D != -3d^2.
For translated diagonal P and fixed slice S, symmetry gives beta02=S2,
beta11=P2-2S2, beta01=S1, hence gamma=(4S2-P2)/S1.
This two-slice rewriting is an elementary consequence of their formula,
not an independent discovery of Masser's theorem.

At lower prime level p=(1-D)/4, for the nodal cubic jet set
a=S2, b=S3, c=P2-2a, d=P3/2-b. The nonzero tangent alpha
obeys a(1+alpha^2)+c alpha=0. Assume a!=0, simple nonreal tangent
(alpha!= +/-1), and the established chain-rule relation
kappa=2beta/(alpha^2-alpha).
The cubic equation gives
kappa=-2[b(1+alpha^3)+d(alpha+alpha^2)]/
((c+2a alpha)alpha(alpha-1)).
Using c=-a(alpha+alpha^-1), denominator becomes
a(alpha+1)(alpha-1)^2; numerator is
-2(alpha+1)[b(alpha^2-alpha+1)+d alpha].
Since (alpha-1)^2=-(c/a+2)alpha and alpha^2-alpha+1=-(c/a+1)alpha,
cancel to get kappa=2[d-b(c/a+1)]/(c+2a)
=P3/P2-2S3/S2. Thus gamma=2S3/S2-P3/P2.
All divisions licensed by the stated hypotheses. This rational-only
consumer eliminates quadratic field inversion, not the need to establish
the analytic branch/tangent hypotheses. It is a specific alternative
lower-level computational route; novelty relative to other CM derivative
methods remains open. For D=-163 levels 41 vs 163, degrees in each
variable 42 vs 164; no implied measured speedup.

New executable scripts/check_cm_masser_weld.py at 152d7148f72d7f480ac928326bff402479729922,
locally executed exact Git blob e79b21cbe0e485b2b40502d53359afb8fa852d6b.
Run from repository:
python scripts/check_cm163_residue_swar.py --fast-j --bits 384 --output coeffs.json
python scripts/check_cm_masser_weld.py --coeffs coeffs.json
Local replay used existing cm_fast_j_coeffs.json; no fresh CM163
construction in this packet. Independent lower/higher polynomial
construction using original GMP backend:
D=-11 levels 3/11 gamma=289/8830976, 0.043565546 s;
D=-19 levels 5/19 gamma=275/226934784, 0.377458157 s.
Both exact parity PASS. Stored CM163 slice gamma=
77859659565707/19943834790540897829879824384000 and s2
77265280/90856689 PASS. Single execution observations, not comparative
benchmarks. Classical K supplied for smaller cases. No higher-level
163 reconstruction, original Masser book inspection, external benchmark,
or Agda/CI acceptance. Keep original quadratic field consumer as oracle.
Next: cross-level 43/67 and bounded CRT for 163, compare direct jet
competitors rather than only full polynomial reconstruction, integrate
rational consumer after parity on all supported CM cases.


## 20 November — direct consumer-selected translated jets (P9.M14)

Refactor scripts/check_cm163_residue_swar.py at bc4a24b9513ac57479f4b16d2295b247c9bd1197
(blob 16675c15d6617454e9cb3e5f15bb2a2807f4c70a) exposes raw_inputs and
normalized_product; original full-slice constructor remains an oracle.
New scripts/check_cm_direct_jet.py at 5aa4f5310f1db891ae8b4227e7181c61ce7fc606
(blob 6e1b83d5ff38d1cc42095b31f8a24b3ff17cbf62). Local Git hashes match.
Reuse existing cyclic norm, modular inverse and fast J producers; no
new classical modularity assumption. Preserve Masser attribution through
Bruinier–Ono–Sutherland arXiv:1301.5672 Lemma 2.3; classical formal residue
change of variable is not novel. Candidate contribution is the specific
consumer-selected implementation, its bounds and lower-level jet weld.
No actual co-authorship inferred from citations.

Let F be either polynomial slice of degree n, Q=q^n F(j(q)), V=J-Kq,
w=q/V. Formal residue of w^(m-1) F(K+1/w) dw after substitution is
[q^(n-m)] Q V^-m (1-qV'/V). This gives translated coefficient m
directly over residue rings, without reconstructing any full polynomial
or subsequent translation. V has constant coefficient 1. Substitution
identity holds over integers and hence descends to all residue rings.
Compute Z=Q(1-qV'/V), then multiply successively by V^-1 at decreasing
truncations n-m; select one coefficient at each order. Fixed-slice
V inverse is a prefix of the already computed H inverse, reused after
exact input equality check. Diagonal uses a small unit inverse recurrence.
This is conditional on existing integral slice and normalized product
identity and analytic branch hypotheses; not a fresh modularity proof.

Height proof: choose least integer B>=2 satisfying exact absolute sums
|V-1|<=1/4, |qV'|<=1/4 on |q|=B^-p; monotone exponential search/bisection.
On |t|=B^-1 bound H by 2^h using finite absolute coefficient sum,
bound g on q circle by 2^a. Norm invariant under t->zeta*t gives
|Q|<=2^(ph+a); |V^-m|<=2^m and |1-qV'/V|<=2.
Cauchy implies |translated c_m|<=2^E_m, E_m=ph+a+1+m+
ceil(log2(B^(p(n-m)))). All ceilings via integer arithmetic. Finite
truncation suffices because only coefficients through n enter.
CRT product >2^(max E_m+1) certifies unique signed reconstruction.
For CM163 B=3 for both slices, E arrays [5372,5308,5244,5180] and
[5069,5005,4941,4877], 14 rings, product 5413 bits.
Reconstruct eight integers (four zero witnesses, four nonzero
consumer coefficients); no full-polynomial recovery on normal path.
Optional --ring-oracle invokes full slice reconstruction per ring and
checks translated residue equality; --reference checks existing
signed-hex full coefficient file after reconstruction only.
CRT maintains O(1) reconstructed integer slots at fixed jet order,
not an O(1) total working-memory theorem. Series M=O(p^2) unchanged.
Old full power table O(p^2) residue slots replaced by constant number
of length O(p) arrays in extraction. Norm/series dominate overall memory.

Local final source Python 3.13.5/SymPy 1.14.0, serial subprocess runs
including construction, exact verification, final rational normalization:
- full slices (refactored original --fast-j --bits 384 --reference):
  3.697450925 s; RSS 138272 KiB; 2526 packed calls; 3721676 max operand bits.
- direct (--bits 384 --reference --output):
  3.352723950 s; RSS 138416 KiB; 958 packed calls; same max operand bits.
- direct with --ring-oracle: 6.346344054 s; RSS 138680 KiB;
  3450 packed calls; all 14 rings x 8 translated coefficients PASS.
Earlier prototype 3.123610317 s, RSS 138156 KiB, not used for matched comparison.
Both final normal paths exact s2=77265280/90856689,
gamma=77859659565707/19943834790540897829879824384000.
All eight direct coefficients match stored full slice translation.
Full payload 241632 bits, 61113 JSON bytes vs direct 18425 bits,
4664 JSON bytes (different JSON whitespace conventions, payload counts
independent). Direct nonzero bit lengths [4631,4580,4629,4577].
15.75x fewer reconstructed slots, 62.1% fewer packed calls, 9.3%
less elapsed time in one sequential pair, no observed RSS reduction.
No statistical benchmark or external SOTA claim.

Final --family replay: independently construct low cubic and high
Masser quadratic jets, low ring oracle enabled, different moduli target
widths 128 and 384, so times NOT a matched level speed benchmark.
| D | low/high levels | gamma | low/high seconds |
| --- | --- | --- | --- |
| -11 | 3/11 | 289/8830976 | .003908/.042307 |
| -19 | 5/19 | 275/226934784 | .011166/.228938 |
| -43 | 11/43 | 268427/226492858368000 | .088244/3.211053 |
| -67 | 17/67 | 44248307/6269455245182976000 | .357782/16.550388 |
All PASS same rational gamma and known s2; lower ring comparisons
1+2+6+11 rings. Classical K supplied. Higher cases use direct jets,
not full independently reconstructed polynomials. Both levels share
arithmetic backend, so not independent software implementations.
Level 163 Masser comparison still OPEN; optional --compare-masser
command exists but level 163 has not been run. Independent root
enclosures, external PARI/FLINT/FriCAS comparison, native SWAR full
backend, and proof/kernel acceptance remain OPEN.
Reproduce from repository:
python scripts/check_cm163_residue_swar.py --fast-j --bits 384 --output full.json
python scripts/check_cm_direct_jet.py --bits 384 --reference full.json --output jets.json
python scripts/check_cm_direct_jet.py --bits 384 --reference full.json --ring-oracle
python scripts/check_cm_direct_jet.py --family
Next: exploit sublinear-in-full-output norm consumer / tighter height
bounds, compare equal residue widths at different levels, run level 163
where resources permit. No CI or Agda run in this packet.


## 20 November — cross-PR quadratic norm and complementary parity (CMP102)

Paper 3 / PR #1444 commit 1cf86519fd571b091301c864297a160de1a6d3eb transfers the original BishopFiniteEvenOddSeriesReindexExact from this branch unchanged, with identical exponent-owner blob on both branches. The signed degree-2n row has 2n+1 entries; retain the final even endpoint. The Yang–Mills specialization uses the already-local real factorial binomial producer rather than requiring the complex capstone.

A shared mathematical observation, not a new CM theorem or performance claim: for the rank-two algebra R[t]/(t^2-z), conjugation sends t to -t, and the multiplication matrix of a+bt is [[a,zb],[b,a]]. Its determinant is a^2-zb^2. For the factorial series C(z)=sum z^n/(2n)! and S(z)=sum z^n/(2n+1)!, exp(T_z)=C I+S T_z with T_z=[[0,z],[1,0]], giving determinant C^2-zS^2=1 by complementary signed binomial coefficients. At z=0, T_z is nilpotent. The Monster cyclotomic norm a^2-ab+b^2 is a related rank-two determinant, with different defining polynomial. This illustrates the multiplication-operator norm and complementary fibre viewpoint without identifying the quadratic algebra with Paper 9's general cyclic quotient, or transferring analytic convergence to a modular residue ring.

For CMP102, shift the vanishing positive-degree coefficients before limit evaluation to avoid division by z; actual Bishop convergence, native unit quaternion and physical attachment remain OPEN. No new Paper 9 analytic, CRT, performance or kernel gate is promoted. Keep existing projected-product/inverse verification and M15k obligations unchanged.


## 20 November — scope clarification and valuation-filtered binary repetition

User objective clarified: SOTA specifically means fast certified pi. CM/modular-j
and cyclic norm arithmetic remain active complementary research, not a required
world-record claim. For pi prioritize matched end-to-end comparisons (including
constant generation, precision certificate, and output) against established
fast pi implementations; no new pi benchmark in this packet.

For original diagonal H=A(q)-t^(p-1)J(t), A=J(q), set U=t^(p-1)J(t)/A.
Then val U=p-1 and (1-U)^(-1)=prod_(k>=0)(1+U^(2^k)), truncated when
2^k(p-1)>pn. The projected derivative is p*q*A'/A-Pi_p(tU'/(1-U)).
Compute successive powers with shifted leading support, retain full inverse
verification, and reconstruct norm by the original q-logder recurrence.
Requires units only through n for norm reconstruction, not through
floor(pn/(p-1)) as the earlier valuation-log route did.
Independent local Python/GMP harness /tmp/p9/filtered.py using previously
transcribed original raw-input formulas and modular J generator:
10/10 exact diagonal norm comparisons with Newton logder, 10/10 full
(1-U)*G=1 verification; p=3,5,11,17,41, two split prime-power rings
per p, >=384 bits. Includes previously inadmissible valuation-log p=41
prime base 83. Level 41 single norm-only timing pairs (Newton, filtered):
83 (.08962,.19454) s; 739 (.08852,.19045) s. Shared J setup excluded.
Both routes use same independent nonnegative GMP convolution; no production
byte replay, statistical speedup, external benchmark, or Agda receipt.
Filtered repetition is slower; keep default Newton unchanged. Source
harness not yet persisted to repo in this packet. Sweetgrass retained-strand
motif remains attributed to Robin Wall Kimmerer, not mathematical authority.
Native selected extraction, contour optimization, full CRT and level 163 OPEN.


## 20 November — COMP1/2: projective binary splitting and shared compression programme

Fast certified pi remains the SOTA benchmark target; compression remains a
first-class cross-programme research objective, including CM, Monster/VOA,
FRACTRAN/FRACDASH and TOE. Do not demote wheel/holonomy, connectedness,
primitive repetition or retained-strand consumer sufficiency to discarded
ideas merely because a prototype is slower.

Reuse scripts/check_chudnovsky_exact.py (blob
eb58d9dd1d0a2e0d62e9ef16a0ad1ee9703e0e6b) and the existing
HypergeometricBSplitIntegerMergeExact owner. For Chudnovsky only the generic
extra denominator is 1. Triple (P,Q,T) represents [[P,T],[0,Q]].
Merge (pP,qQ,tQ+pT) is associative. Common nonzero scaling is
compatible with both left and right composition, preserving P/Q,T/Q
over Q with Q nonzero. Canonical primitive integer triple with Q>0
is sufficient for these rational observations, not for absolute
integer scale or arbitrary unrelated consumers. Do not transfer
this quotient into a residue ring where canceled factors are nonunits.
Tail enclosure retains original alternating bound and integer-isqrt
sqrt(10005) bracket, conditional on classical Chudnovsky identity.

Implementation scripts/check_pi_projective.py, commit
1055652c4a91a70aef8a607f3060a69fbfed9846; local git hash-object and
connector readback match blob 19c01fff2ff1326b47119a44c930ce7ed1fa1df2.
Actual local Python/SymPy 1.14.0: symbolic scalar-matrix compatibility,
400/400 interval split comparisons (a=0..19,b=a..a+19), 14/14 independent
factorial prefix sums. All three tested rational pi intervals identical
between modes and width <=10^(-digits). No new Agda proof.
Three-run sequential median interval computation, same specialized
triple constructor, CPython integer/Fraction arithmetic, normalization
at every leaf/internal node versus none:

| digits | terms | plain ms | normalized ms | plain final bits | normalized final bits |
|---:|---:|---:|---:|---:|---:|
| 1000 | 73 | 0.550 | 0.575 | 12222 | 9017 |
| 10000 | 716 | 28.915 | 26.835 | 142231 | 90212 |
| 50000 | 3573 | 616.538 | 539.675 | 784923 | 451516 |

At 50000 digits ~42.5% final carrier size and ~12.5% elapsed reduction.
Final summed bit lengths are NOT peak RSS. Width bound is NOT a proof
that decimal endpoint rounding agrees; add identical floor(10^d*L)
and floor(10^d*U) with adaptive refinement and actual output timing.
No external SOTA comparison; normalization may be costly at other scales.
Classical prior art includes Chudnovsky binary splitting and rational
common-factor removal; no novelty claim before review.

COMP1 algebraic projective composition derived and finite PASS.
COMP2 exact normalized split prototype PASS, production/native GMP OPEN.
COMP3 predictive prime valuation cancellation: seek gcd(P_left,Q_right)
which divides both numerator addends AND both products; cancel before
large products, compare residual post-merge gcd; prime-factor sieve
and factorial valuations as alternative. COMP4 operand-balanced tree
and empirical thresholds OPEN. COMP5 native GMP/MPFR/FLINT and
established fast pi external benchmark, certified output and peak RSS OPEN.
COMP6 Monster/VOA orbit/stabilizer, multiplicity and action compression:
reuse #1250, #1179, #1472 and actual Monster369ZetaSameObjectWeldExact,
JInvariant369Zeta6561MonsterCrosswalkExact, JInvariantLambdaOrbitBase369BridgeExact,
JInvariant369ConsolidatedNextStageExact. Graded trace/character parity
does not certify literal vertex operators, intertwiners or full action.
COMP7 FRACTRAN/FRACDASH shared program and exact reconstruction OPEN.
COMP8 general contextual consumer-preserving quotient/factorization
reuse canonical TOE owner, retain negative controls for projected
carrier non-descent. Sweetgrass/Robin Wall Kimmerer (2013) remains
cultural/methodological attribution, not mathematical proof authority.
All earlier CM gates, including projected GMP, contour, primitive
necklaces and level-163 Masser, remain active and unchanged. No CI initiated.


## 20 November — COMP3a: complementary pre-multiplication cancellation

For triples (p,q,t),(P,Q,T), g=gcd(p,Q)>0, write p=g*p0,Q=g*Q0.
The merge equals g*(p0*P,q*Q0,t*Q0+p0*T). Cancel before materializing
all three outputs. Works over integers with nonzero Q, including signed p.
This is classical rational cross cancellation, not novelty claimed.
Cross-only mode need not return a primitive triple; sufficient rational
consumer is preserved despite residual common scale.

Exact local run of scripts/check_pi_cross_cancel.py, commit
6e3a7236c5b521b53612ff0206e1f493dfb3886f; local git hash-object and
connector readback identical blob 3ccd75ca55528965d4f69ec207305d8ac33b5b8c.
SymPy symbolic matrix identity PASS; 1200/1200 subinterval comparisons
(400 intervals, three modes against plain), including canonical gcd
checks for modes 1/2. Four modes: 0 plain, 1 post-gcd, 2 cross+post-gcd,
3 cross only. Exact common decimal floor of rational endpoints certified
for each mode, all modes match at each precision, conditional on classical
Chudnovsky identity and alternating tail. No refinement needed.
Three-run sequential medians include interval computation, scaled endpoint
floors and decimal string conversion, exclude hash and separate carrier
measurement. CPython standard integers; SymPy only symbolic oracle.

| decimal places | terms | bits | plain ms | post gcd ms | cross+gcd ms | cross only ms |
|---:|---:|---:|---:|---:|---:|---:|
| 1000 | 73 | 4032 | .622 | .708 | .663 | .586 |
| 10000 | 716 | 40032 | 34.370 | 29.647 | 30.068 | 28.475 |
| 50000 | 3573 | 200032 | 675.993 | 590.620 | 602.470 | 553.565 |

Final triple summed bit lengths by mode:
1000 [12222,9017,9017,9030]; 10000 [142231,90212,90212,90233];
50000 [784923,451516,451516,451549]. Not peak RSS.
SHA256 of decimal integer string floor(10^d*pi), no dot:
1000 8a84d58d47f78c42a200ebfbbe7346426d4cdf4f2803d45c3590162865fcc0d2
10000 ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524
50000 c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1
Cross-only ~18.1% faster than plain at 50000 places, ~42.5% final
carrier reduction, only 33 bits more than fully primitive. Choose as
candidate, not production default or external SOTA. COMP3a PASS reference;
COMP3b factor-sieve predictive cancellation, COMP4 balanced tree and
thresholds, COMP5 native library/external matched benchmark all OPEN.
Preserve COMP6-8 and CM gates: minimal canonical form can be more costly
than sufficient noncanonical carrier; test this separately for Monster/VOA
orbit/action and FRACDASH reconstruction, do not infer equivalences.
No CI initiated or Agda kernel receipt.


## 23 November — P0 fast-π master-native consolidation

P0 remains fastest independently certified π, although the external SOTA
comparison has been deferred for execution. Original GMP source blobs
from diverged historical PR #1529 are restored **byte-identically**
on a clean master-based branch, with source-hash-checking compiler and
certified decimal regression harness. A *separately built equivalent*
local C++ implementation completed exact conditional decimal-floor
certificates for 5 million and 10 million decimal places. At 10M,
the observed elapsed time was 11.88 seconds for the in-place
one-division path, with 265,988 KiB peak RSS and matching
SHA-256 `ae9c137083802006c204e6683c28c6727a862103d703b5e0d79a22ddaa201999`.
This is a single local execution, **not** a new external SOTA or a
source-byte-identical GitHub executable replay. Mode differences at 1M
vary substantially across runs; no universal one-floor or in-place
performance winner is promoted. Complete receipts, compile commands,
source identities, stop conditions, and next Pareto gates are maintained
in `Docs/roadmaps/Paper9PiP0MasterNativeGMPConsolidation20261123.md`.
Analytic Chudnovsky premise and same-original-Bishop real identification
remain separate. Preserve source structure, signs, and all future-consumer
obligations; no dependency on unrelated Monster work.


## 23 November — COMP5g consumer-indexed GMP execution-fibre optimization

The prior section 10 execution/bit-cost formalism now has a concrete
native source-relative resource witness, recorded in
\`Docs/roadmaps/Paper9PiP0MasterNativeGMPConsolidation20261123.md\`
and separately committed \`check_pi_p0_fibre_cost_profile.cpp\`,
\`check_pi_p0_endpoint_lifetime.cpp\` and
\`check_pi_p0_cost_fibre_pareto.py\`. The instrumentation charges
four integer products and one addition per ordered P/Q/T merge;
it explicitly distinguishes (a) modeled live P/Q/T limb
capacity, (b) **actual GMP allocator peak** from hooks installed
before GMP initialization, (c) Linux process VmHWM, and (d)
end-to-end measured wall time. This instantiates the
FibreProgramComplexityExact / EfficientRecoverableQuotientExact /
StreamingResidencyComplexityErrorDNABidiExact planning interface
at source/execution-receipt level, **not** an Agda kernel proof.

At 1M digits, an equivalent locally compiled C++ implementation
with early terminal-carrier transfer/destruction reduced actual
peak GMP bytes 23,074,600 -> 20,765,464 (10.0%) and median
process VmHWM 27,800 -> 25,952 KiB (6.6%), with same exact
certified output; five-run rotating-order times 689.851 ms
(retained) vs 697.337 ms (released), not reliable evidence of
a speed change. At 10M digits the new single-run source-equivalent
receipt is 243,421,624 -> 217,661,176 GMP bytes (10.6%),
265,632 -> 238,056 KiB VmHWM (~10.4%), both completing
~11.38 seconds, and matching existing SHA256
\`ae9c137083802006c204e6683c28c6727a862103d703b5e0d79a22ddaa201999\`.
The 5M hash also matches. The committed GitHub source and full
exact-source runner have not been compiled/executed as exact
Git bytes in this environment; locally tested independently
constructed source has equivalent arithmetic/ownership semantics.
Prior Chudnovsky analytic premises, Bishop same-real, external
SOTA and complete formal machine/Agda cost-weld remain OPEN.


## 23 November — COMP5h: exact quotient-consumer liveness and GMP endpoint scheduling

Following the COMP5g tree-carrier lifetime optimization, the actual
terminal certificate is further factored into two nonoverlapping
resource lifetimes. Compute and retain only the integer quotient
\(x=\lfloor N_L/D_L\rfloor\) from the lower endpoint;
release its source numerator/denominator and the lower-series
endpoint before constructing the upper witness
\(N_U < (x+1)D_U\). Positivity and \(L\le U\) make this
a semantics-preserving refactoring of the exact finite
integer-floor certificate; no upper division, truncation or
permutation of the ordered Chudnovsky product is introduced.
The original Chudnovsky analytic identity and alternating
tail remain external premises.

The new instrumented
\`scripts/check_pi_p0_endpoint_scoped.cpp\` and four-way
\`scripts/check_pi_p0_cost_fibre_pareto.py\` instantiate
the existing execution-fibre sum/peak and
EfficientRecoverableQuotientExact consumer/liveness viewpoint
as a native test plan; they are **not kernel-checked Agda
implementations**. An independently compiled equivalent
local C++ experiment shows the GMP managed-allocation
peak at 1M changing **20,765,464 -> 17,111,176 bytes**
relative to COMP5g, and at 10M
**217,661,176 -> 181,920,552 bytes** (~16.4%).
Compared with the earlier tree-retaining baseline,
the 10M reduction is about 25.3%.
Measured process VmHWM at 10M is
**238,100 -> 195,172 KiB** under the same local
execution conditions. The reported 10M
~11.29/11.13-second times are single runs and
do not prove a latency improvement; five paired
1M runs likewise show overlapping times. All outputs
match the pinned prior exact decimal SHA-256 receipts.
The GitHub files have been read back; byte-identical
compilation and execution of the committed C++ remain
an open reproducibility gate. See the canonical
\`Docs/roadmaps/Paper9PiP0MasterNativeGMPConsolidation20261123.md\`
for full receipt tables, computational model boundaries,
source authority and next experimental controls.


## 23 November — COMP5i/j: exact dyadic quotient factorization, measured 10M Pareto improvement

The exact quotient/upper-bound consumer admits two further
semantics-preserving scheduling identities, with all integer
divisors positive and all numerator inputs nonnegative:

```
floor(N/(D*2^k)) = floor(floor(N/2^k)/D)
N < (x+1)*D*2^k  iff  floor(N/2^k) < (x+1)*D.
```

COMP5i moves the dyadic division to the numerator using
`mpz_fdiv_q_2exp`, removes explicit oversized scaled
denominators, and releases the square-root radicand immediately
after computing the exact integer sqrt. COMP5j further uses
`10^d=2^d*5^d`, constructing `5^d` and shifting by
`k-d` (guarded by `k>=d`). Neither changes requested
precision, ordered Chudnovsky P/Q/T algebra, its exact finite
tail enclosure, or the one-quotient strict upper-bound test.

The **independently locally compiled, equivalent** native C++
variants reproduce prior SHA256 decimal strings at 10k,
100k, 500k, 1M, 5M and 10M. At 1M, a five-run
alternating comparison measured COMP5h median 698.071ms,
COMP5i median 624.521ms and 17,111,176 versus
14,124,952 GMP managed-live peak bytes. At 10M a single
COMP5j run measured 148,669,512 GMP live peak bytes
(166,072 KiB VmHWM); the original tree-retaining source
had recorded 243,421,624 bytes: **38.93% less measured
GMP allocation** relative to that historical same-program
comparison, not an all-hardware theorem. COMP5j vs COMP5i
at 1M has overlapping timing distributions and therefore
only a memory-side preference.

Native source-relative implementations are committed as
`scripts/check_pi_p0_dyadic_quotient_shift.cpp` and
`scripts/check_pi_p0_power5_dyadic_certificate.cpp`.
`scripts/check_pi_p0_cost_fibre_pareto.py` now verifies Git
blob identity, compiles six original/candidate modes and checks
the previous decimal-hash receipts; the two new integer
identities have separate exhaustive bounded tests in
`tests/test_pi_p0_dyadic_quotient_certificate.py`.
The mathematical identities hold for all stated integer
inputs; finite tests are negative controls and reproducible
regressions, not the mathematical reason for equivalence.

The commit/file readbacks succeeded, but there was NO
byte-identical execution of the newly committed C++ on this
runtime; only locally compiled source-equivalent prototypes
were run. No Agda kernel verification, independent exact
Chudnovsky analytic premise proof, Bishop same-original-real
weld, or external SOTA benchmark is claimed. The formal
execution-fibre cost-model owner remains Section 10 and
`FibreProgramComplexityExact.agda`; actual GMP allocator and
RSS receipts are empirical cost consumers. Full source/metrics
and the P0 acceptance gate live in
`Docs/roadmaps/Paper9PiP0MasterNativeGMPConsolidation20261123.md`.


## 24 November — P0 geometric acceleration candidates COMP5k/l (not tested)

The original ordered Chudnovsky binary-splitting triple
\((P,Q,T)\) is an upper-triangular matrix carrier
\(M=\left(\begin{smallmatrix}P&T\\0&Q\end{smallmatrix}\right)\).
The original merge is matrix multiplication and its adjacent
series increment is exactly
\(\delta_n/(Q_nq_n)\), where
\(\delta_n=P_np_n(13591409+545140134n)\) has sign
\((-1)^n\) for \(n\ge2\). Thus the rational endpoint
orientation can be selected from the **original signed
source** without multiplying two enormous cross-products
(COMP5k). An even-index section also gives a new
quotient/remainder upper-witness identity (COMP5l).
Let \(B=Tq+\delta\), \(C=Qq\),
\(F=426880\cdot5^d\), \(R=\lfloor
\sqrt{10005\cdot2^{2b}}\rfloor\), \(k=b-d\).
If \(FRC=2^k u+\ell\) and \(u=xB+\rho\)
with canonical nonnegative Euclidean remainders, then
the original strict upper certificate is **equivalent** to
\(x\delta+\rho+\lfloor(\ell+FC)/2^k\rfloor<Tq\).
The retained residual witness replaces the second upper
root-times-decimal numerator but might cost more live
integer memory or quotient/remainder work. It is an
exact alternative certificate, not an established
optimization or SOTA result.

Original attribution, full algebra, source labels, and the
bounded next research plan are in
\`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md\`.
The latest #1550/#1549 work supplies generic
source/consumer adequacy and sharing inspiration only;
it does not prove any Chudnovsky or performance result.
The user requested **deferred testing**: source implementation
and GitHub readback only, no new executable acceptance,
benchmarks, Agda kernel check or independent SOTA comparison.


## 24 November — COMP5m/n: radical-aligned geometric quotient and width-scheduled P/Q/T tree

Two new **UNTESTED** source-preserving candidate implementations
were committed to master-based Paper 9 PR #1546 with testing
explicitly deferred. They are rooted in the original
\(2\times2\) upper-triangular Chudnovsky P/Q/T matrix product
and consumer-indexed complexity formalism (Paper 9 §10).

**COMP5m, output-aligned radical enclosure:** for
\(K_d=426880\,10^d\sqrt{10005}\), \(g\ge0\), set
\(H_{d,g}=\lfloor2^g K_d\rfloor\) by a large
exact integer square-root. The original signed adjacent
series endpoints \(S_\mathrm{lo}=N_\mathrm{lo}/D_\mathrm{lo}\)
and \(S_\mathrm{hi}=N_\mathrm{hi}/D_\mathrm{hi}\)
give the outward interval

\[
\frac{H_{d,g}D_\mathrm{hi}}{2^gN_\mathrm{hi}}
 \le10^d\pi<
\frac{(H_{d,g}+1)D_\mathrm{lo}}{2^gN_\mathrm{lo}}.
\]

Its exact lower decimal-floor quotient and strict upper
comparison use dyadic numerator shifts as in COMP5i; an
inconclusive comparison widens both the series cutoff and
root guard. This eliminates the **separate** 5-power
post-sqrt product but requires a dense huge-integer square
to form the radicand, so performance may get WORSE.
This outward interval is not asserted to equal COMP5j's
finite interval; both refer conditionally to the same
original analytic Chudnovsky π source.

**COMP5n, exact ordered product with changed execution path:**
\(Q[a,b)=\prod_{j=\max(a,1)}^{b-1}640320^3j^3\).
Its log width can be estimated from differences of
\(\log\Gamma\) without computing a large integer.
Execute the child predicted wider **first** and retain
it while computing the other, but compose the original
left/right factors in exactly the same order

\[
M[a,b)=M[a,m)M[m,b),\qquad
M=\begin{pmatrix}P&T\\0&Q\end{pmatrix}.
\]

This is merely a schedule change: no change of leaf
semantics, signs, tail error, radical certificate or
ordered product. Its cost estimator is a heuristic,
not an exact minimizer or hardware-independent
memory theorem. The existing \`FibreProgramComplexityExact\`
sum/peak, streaming residency and quotient-reopen ledgers
remain authoritative.

Source files: \`scripts/check_pi_p0_output_aligned_root.cpp\`
and \`scripts/check_pi_p0_width_scheduled_pqt.cpp\`.
Full derivations, newly indexed deliverables, negative
controls and future acceptance criteria:
\`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md\`.
Neither source has been compiled or benchmarked, nor were
Agda/Lean, CI or independent SOTA checks run; no new
performance numbers or formal analytic closure are claimed.


### COMP5o — exact square-slack verification without a second radical

The candidate-digit production and independent
certification consumers can be separated in the
existing recoverable-quotient/complexity framework.
Given **source-verified** positive consecutive
Chudnovsky bounds \(S_{\rm lo}\le S\le S_{\rm hi}\)
and \(F=426880\,10^d\), a candidate nonnegative
integer x is admitted when

\[
x S_{\rm hi}\le F\sqrt{10005}
 <(x+1)S_{\rm lo}.
\]

Because every term in these inequalities is
nonnegative, both can be checked using exact
integer-square slacks, with nonnegative lower
slack and strictly positive upper slack.
The header \`scripts/pi_p0_signed_square_verifier.hpp\`
constructs those signed slacks using the original
P/Q/T source cone, no \`mpz_sqrt\` in the verifier.
This is a conditional *same-output* certificate,
not a new infinite-series proof; caller source
authentication, original analytic premises,
receipt reopening and full formal kernel
verification remain separate OPEN obligations.
The untested square-based verifier may require
MORE work and memory than the existing GMP
radical certificate. No performance gain is
claimed. Complete equations in the projective
residual roadmap, G6/COMP5o.


### 24 November — COMP5p/q/r: exact projective source content as a terminal resource quotient

The latest P-vs-NP #1548 signed-source
valuation analysis and ramified
Langlands/GCT #1549 relative
reconstruction/carry ledger reinforce a
source-level rule: factor out **known exact
common content before constructing large
representations**, while keeping the
source scale and signed residual needed
for selected future consumers. This
is analogy and methodology, not an
application of either research programme's
separation/correspondence claims.

In the *original* Chudnovsky leaf matrix
\(M_j=\bigl(\begin{smallmatrix}p_j&t_j\\0&q_j\end{smallmatrix}\bigr)\),
every \(j\ge1\) admits the exact
positive scalar 24:
\(M'_j=M_j/24\). Under the
original ordered multiplication, for
\([0,n)\) the normalized triple is
\((P',Q',T')=(P,Q,T)/24^{n-1}\).
The signed adjacent delta and every
original rational \(T/Q\) right-extension
consumer are unchanged by this
common projective gauge; literal
raw P/Q/T is NOT unchanged.
Maximum uniform factor is 24 since
\(\gcd(|p_1|,|p_2|)=
\gcd(120,5544)=24\).

The *additional* per-index exact
gcd \(h_j=\gcd(
(2j-1)(6j-5)(6j-1),
(640320^3/24)j^3)\)
has only support on primes 3,5,23,29
(with the universal 2^3 already removed).
Its prime valuations are computable
from named small source factors and j,
without calling a general GMP gcd.
Normalize the leaf by \(24h_j\);
record the original-source
scale recipe \(\prod_{j=1}^{n-1}24h_j\)
as an indexed provenance witness.
The exact mathematical projective
identity follows by bilinearity of
the upper triangular matrix product,
not by empirical π hash agreement.

New research implementation files
\`check_pi_p0_projective24_leaf.cpp\`
(COMP5p), \`check_pi_p0_projective24_residual_witness.cpp\`
(COMP5q), and
\`check_pi_p0_indexed_prime_content.cpp\`
(COMP5r) are deliberately standalone,
**uncompiled and untested**, with no
new timing or GMP memory measurements.
The first uses direct factor-free
leaf formation; the second also
uses the COMP5l signed remainder
witness; the third computes exact
prime-local extra factor by constant
prime support tests plus two exact
divisions. All three leave the prior
measured COMP5j default unchanged.

Projective source authenticity and
literal original raw-triple reopening
remain distinct consumers and must be
charged separately under Paper 9 §10,
\`FibreProgramComplexityExact\` and
\`EfficientRecoverableQuotientExact\`.
Full equations and exact PNP/Langlands
attribution boundaries live in
\`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md\`.
No Agda/Lean kernel, source-verified
benchmark, new analytic Chudnovsky
identity/Bishop result or external SOTA
claim is made.


## 24 November — COMP5s: projective \(\mathbf{PQT}\) gauge with precision-indexed exact execution

Source producer complexity remains charged: the native
candidate counts its prime-local divisibility probes,
valuation divisions and two exact GMP divisions per positive
leaf, separately from execution-order planning and optional
raw source reopening. No measured speed or total-cost
dominance follows solely from shorter P/Q/T limbs.

An exact source-normalizing gauge and a
precision-sensitive execution scheduler
have been combined in **UNTESTED**
native C++ candidate COMP5s on Paper 9
PR #1546. Original adjacent Chudnovsky
leaves are normalized by the known
positive indexed factors \(g_j=24h_j\)
for \(j\ge1\), with \(j=0\) unscaled.
For any source interval, define
\(G_{a,b}=\prod_{a\le j<b,j\ge1}g_j\).
The exact ordered matrix identity is

\[
M'_{a,b}=G_{a,b}^{-1}M_{a,b}
        =M'_{a,m}M'_{m,b}.
\]

An optional, explicitly costed
`ProjectiveSourceReceipt` opens the
original raw P/Q/T by multiplying the
normalized triple by recomputed \(G\).
This is source-coordinate recovery, NOT
an independent validation of a
possibly forged P/Q/T producer.

For output precision \(d\) with root
bit index \(b\), approximate source
widths from the original P/Q/T leaf
products and compare the two
independent subtree execution schedules

\[
p_{L\to R}=\max(p_L,s_L+p_R,m),\quad
p_{R\to L}=\max(p_R,s_R+p_L,m).
\]

The original final matrix product stays
left-right and noncommutative;
only child *evaluation time/order*
changes. Existing full-precision GMP
integer merges, signed tail, zero mode,
strict upper π admission and output
hash are unmodified. A floating
`lgamma` width estimator is NEVER
used to decide P/Q/T digits or bounds;
it is a memory-cost HEURISTIC and
cannot justify lossy truncation.

The output precision \(b\) controls
which large source subtrees receive
a bounded-depth schedule. Planner object payload is reported separately
from GMP heap; allocation overhead is still
uncounted, as required for honest accounting by
Paper 9 §10 and
`FibreProgramComplexityExact.agda`.
The implementation and source-specific
cost/proof ledger are respectively
`scripts/pi_p0_projective_precision_schedule.hpp`,
`scripts/check_pi_p0_precision_projective_schedule.cpp`,
and
`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md`.
S1 source homogeneity, S2 optional
raw reopening and S3 correct
consumer-specific semantics are
algebraic source constructions;
formal Agda kernel, actual native
C++ compile/output check,
calibrated Pareto and analytic
Bishop same-real completion remain
OPEN. User requested testing be
deferred; no new timings/memory
claims or external SOTA result.


## 24 November — COMP5t: projective affine-edge continuation and independent precision axes

The exact source-normalized Chudnovsky
\((P'_n,Q'_n,T'_n)\) carrier has a second
reversible coordinate system at an authentic
terminal cutoff \(n\ge2\):

\[
E_n=(T'_n,Q'_n,V_n),\quad
V_n=T'_nq_n+P'_np_n(A+Bn),\quad
P'_n=\frac{V_n-T'_nq_n}{p_n(A+Bn)}.
\]

The last quotient is exact, because
\(V_n-T'_nq_n\) is the original
source-derived signed residual.
This is a **source-indexed isomorphism**
for the authentic selected consumer,
and source scale \(G_{0,n}\) must still
be reopened separately for literal raw
P/Q/T coordinates. The terminal
series bounds \(T'_n/Q'_n\) and
\(V_n/(Q'_nq_n)\) are both available
without storing the original P during
guard-bit-only retries.

If a current root-enclosed quotient
\(x\le F\sqrt{10005}/S_{\mathrm{hi}}\)
fails the usual exact strict upper check,
squared comparisons distinguish two
**independent precision axes**. With
\(F=42688010^d\):

\[
D_b=10005(FD_{\rm hi})^2-
  ((x+1)N_{\rm hi})^2,\quad
D_n=((x+1)N_{\rm lo})^2-
 10005(FD_{\rm lo})^2.
\]

For \(D_b\ge0\), increase only the
dyadic radical guard \(b\), retaining
the current affine edge and cutoff;
for \(D_b<0,D_n>0\), admit x using
the exactly equivalent radical-free
strict upper condition; otherwise
refine only the series index n.
For a series refinement \(n\to n'\),
reopen normalized P by the signed
nonzero source divisor, construct
the new true-index suffix
\(M'_{n,n'}\), and multiply
\(M'_{0,n}M'_{n,n'}\) in the
original noncommutative source
order. Source width, zero mode,
sign orientation and indexed scale
are retained. Neither root/series
refinement requires discarding an
already computed unrelated index.

New files:
\`scripts/pi_p0_affine_edge_retry.hpp\`,
\`scripts/check_pi_p0_affine_retry_schedule.cpp\`,
and the \`makePlanInterval\` addition to
\`scripts/pi_p0_projective_precision_schedule.hpp\`.
The original source and consumer algebra,
repair proof and distinct cost accounting
are in the Paper 9 projective residual
roadmap, S7–S12. Extra full-size square
slacks and derived next denominators
may outweigh any avoided recomputation.
**No compile, test, Agda/Lean proof or
new performance measurement** was run;
COMP5j remains the historically
measured source. Original analytic
Chudnovsky identity/tail, Bishop
same-original-real and independent
SOTA remain separate OPEN obligations.


## 24 November — COMP5u: three-sector dyadic consumer and carry-exact projective receipt

As a costed alternative to the exact
square-slack classifier of COMP5t, a
new **UNTESTED** π certificate decision
operator has been expressed entirely
through the Euclidean residuals of
the original dyadic GMP floor path.
This is inspired by the user's
P-vs-NP G83 negative control
(larger separators can still admit
small exact consumer contractions),
not a transport of a theorem over
\(\mathbb F_2\) to the integers.

For positive original series bounds
\(N_l/D_l\le S\le N_h/D_h\),
set \(H=4268805^d\), \(R_b=
\lfloor2^b\sqrt{10005}\rfloor\),
\(k=b-d\), \(x=\lfloor
HR_bD_h/(2^kN_h)\rfloor\). The
existing lower division carries two
remainders
\[
HR_bD_h=2^k(xN_h+\rho)+\ell .
\]
The upper dyadic product has exact
decomposition \(H(R_b+1)D_l=
2^ku+\eta\). Exact admission checks
\(u<(x+1)N_l\); on failure, the
two remainder tests
\[
u+\left\lfloor\frac{\eta-HD_l}{2^k}\right\rfloor
 \ge(x+1)N_l,\qquad
\rho+\left\lfloor\frac{\ell+HD_h}{2^k}\right\rfloor<N_h
\]
together prove a genuine source
interval obstruction and require
only a source-indexed suffix extension.
All other cases safely refine
the radical precision, retaining the
same affine source edge; this policy
can sometimes over-refine and is not
a proved minimal-cost scheduler.
Full integer-square slacks are
avoided by this branch classifier,
but big-integer residue, shift and
operand costs are still charged.

The source normalization has a
nontrivial **dyadic carry** even
though the output floor is invariant.
If raw \(A=GA'\), \(N=GN'\) and
normalized residuals are
\((\rho',\ell')\), then the raw
residuals are
\(\rho=G\rho'+\lfloor
G\ell'/2^k\rfloor\) and
\(\ell=(G\ell')\bmod2^k\).
Thus source-indexed BIDI recovery
does NOT mean naive multiplication
of each Euclidean remainder by
\(G\). The optional reconstruction
helper is `reopenRawDyadicFibre`;
the fast certificate does not call it.

New files:
`scripts/pi_p0_dyadic_sector_contraction.hpp`
and `scripts/check_pi_p0_dyadic_sector_schedule.cpp`.
The original source identity, signed
orientation, Chudnovsky analytic/tail
assumptions, Bishop same-real
and source-authentication obligations
remain distinct. Source derivation and
P0 roadmap S13–S19:
`Docs/roadmaps/Paper9PiP0ProjectiveResidualCone20261124.md`.
No compilation, benchmark, numerical
test, proof-assistant kernel run or
new world-record claim this tranche.


## 24 November — COMP5v: one source-common terminal radical for both adjacent endpoints



The integrated source was also
reviewed for the inherited adjacent
denominator allocation:
`viewEndpoints(edge)` was removed
from COMP5v's fast path so \(Q'q_n\)
is not materialized independently
before computing its shared radical
factors. When \(1\le n<2^{20}\),
the exact source factor
\(q_n=(640320n)^3<2^{120}\);
this finite cutoff bit-width
motivates small-factor multiplication
as opposed to duplicating a large
root multiplication, but is not a
GMP memory/time benchmark.

From the genuine projective Chudnovsky
signed affine edge \(E_n=(T',Q',V)\),
retain the original next leaf \(q=q_n\),
\(H=426880\,5^d\), and dyadic integer
sqrt \(R=\lfloor2^b\sqrt{10005}\rfloor\).
Define \(Z=HQ'\), \(Y=ZR\).
For even series cutoff n the exact
original source endpoints are
\(S_{\rm lo}=T'/Q'\) and
\(S_{\rm hi}=V/(Q'q)\);
the lower/upper terminal
radical numerators are respectively
\(qY\) and \(Y+Z\). For odd n the
endpoints reverse, and these
numerators are \(Y\) and
\(q(Y+Z)\). Thus a **single
common** \(Y=HQ'R\) multiplies
the radical across both
certificate consumers, rather
than two independently
constructed root products.
This factorization is source
algebra, not a new π identity.

The nested lower Euclidean
quotient and remainders
\(A=2^k(xN_h+\rho)+\ell\)
and upper \(W=2^ku+\eta\)
are literally the same values
as COMP5u, with \(k=b-d\).
The first exact upper test
is \(u<(x+1)N_l\). Only on
its failure is \(\eta=W\bmod2^k\)
produced; the signed floor
correction and exact
root-guard-versus-series-suffix
decision stay unchanged.
The authenticated original
prime-local gauge retains
signed residual \(\delta\),
source zero mode and precise
n,d,b indexing. For raw-source
remainder reconstruction, the
indexed scale and **dyadic carry**
remain necessary; output-floor
homogeneity does not imply
remainder homogeneity.

The two new untested files
`pi_p0_shared_radical_sector.hpp`
and `check_pi_p0_shared_radical_schedule.cpp`
preserve the old COMP5u/t
versions. Separate primitive-work
counters charge source
q-products, common radical
multiply, lower division,
failure-only upper remainder
and signed shifts. **No C++
compilation or benchmark,
Agda/Lean kernel, GMP memory
measurement or external SOTA
claim** is made. The full
source algebra, proper
attribution to G83 as
a methodological example,
and exact outstanding gates
S20–S25 are recorded in the
Paper 9 projective residual
roadmap. Measured COMP5j
remains the historical baseline.


## 24 November — COMP5w: source-specific elimination of lower dyadic Euclidean residues

A further terminal consumer contraction is available from
the **same original source** as COMP5v. For authenticated
positive adjacent Chudnovsky series bounds,
\(H=426880\,5^d\), \(k=b-d\),
\(R=\lfloor2^b\sqrt{10005}\rfloor\),
and signed affine edge
\(E_n=(T',Q',V)\), put \(q=q_n\),
\(Z=HQ'\), \(Y=ZR\).
The lower/upper dyadic numerators
remain \(A=qY,W=Y+Z\) for even
cutoff and \(A=Y,W=q(Y+Z)\)
for odd cutoff.

**Two quotient-only operations**
already give the same conservative
integer floor:

\[
x=\left\lfloor
   \frac{\lfloor A/2^k\rfloor}{N_h}
  \right\rfloor.
\]

There is no reason to materialize
the low-endpoint dyadic remainder
\(\ell\) or integer remainder
\(\rho\), even on the rare failed
certificate path. Compute only
the upper dyadic quotient
\(u=\lfloor W/2^k\rfloor\);
accept if \(u<(x+1)N_l\).
On failure, construct the upper
remainder \(\eta=W\bmod2^k\)
and signed correction
\(\lfloor(\eta-HD_l)/2^k\rfloor\).
If fixed-source upper
obstruction is established,
test the potential lower-source
radical crossing using the
*opposite* upper-root numerator:

\[
H(R+1)D_h=
 \begin{cases}
 qW,&n\text{ even},\\
 W/q,&n\text{ odd}.
 \end{cases}
\]

This is an exact identity of
the source adjacent denominators
\(Q',Q'q_n\), not a heuristic
approximation. The odd quotient
is divisible exactly by \(q_n\);
the code rejects an impossible
nondivisible value. Comparing
its dyadic quotient against
\((x+1)N_h\) yields the SAME
three-sector retry decision
as COMP5u/v, without recomputing
the big radical product or
any lower remainders. The
true source suffix, signed
residual, prime-local scale,
zero-mode, requested decimal
precision, root guard and
original P/Q/T producer
remain separately indexed.

Independent new UNTESTED
candidate sources:
`scripts/pi_p0_lazy_lower_sector.hpp`
and
`scripts/check_pi_p0_lazy_lower_schedule.cpp`.
No new analytic Chudnovsky
identity, Bishop same-real
formalization, Agda/Lean
kernel, source-executed GMP
receipt, or empirical timing/
memory improvement is claimed.
The completion and negative
control gates S26–S32 appear
in the Paper 9 projective
residual roadmap; the
historically measured COMP5j
programme and external
performance acceptance
remain independent.


## COMP5x/y — signed four-corner and streamed parity observer (24 November 2026)

COMP5x compares all three original boundary predicates via virtual dyadic shifts, retaining exact equality and the intermediate upper-source test. COMP5y adds a two-limb parity-product observer: independently stream q0*a and q1*a, delay the second by one limb and add with a separate carry. This avoids the potential 129-bit overflow of a combined two-product accumulator. Scan low to high; the last unequal limb determines the exact sign, with terminal carry flush and explicit zero. On nail-free GMP with <=64-bit limbs and unsigned 128-bit support, q of <=2 limbs uses constant auxiliary storage; otherwise exact materialized GMP fallback. The even lower-floor parity multiplication is still present. All source indices, signed residual, positive projective gauge, G14 carry reopening, root-only and suffix-only continuation remain intact.

G28: split carry streams and prove prefix reconstruction; G29: highest disagreement and terminal support/equality; G30: compile all parity boundary comparisons with exact fallback; G31: source-matched sector equivalence and adversarial carry/zero/limb tests; G32: physical cost Pareto including full low-to-high scans versus optimized GMP multiplication and high-to-low early exit. Donor inspiration from latest PR metadata: X369 future-consumer quotient, Langlands unique extension, P vs NP costed coverage, F8 independent residual channels, Monster source-labelled transport; these are patterns, not imported proofs.

Owners: scripts/pi_p0_stream_boundary_sector.hpp and scripts/check_pi_p0_stream_boundary_schedule.cpp; COMP5x/w/j retained. No compilation, executable tests, formal kernel or benchmarks per inherited deferral. Independent analytic identity/Bishop same-real and external SOTA remain open. Next: virtual affine sum Y+Z and liveness-aware choice of scan vs materialization; do not claim speedup from smaller explicit state.

## COMP5z — fused affine boundary observer (untested)

G33: stream Y+Z with a one-bit affine carry into COMP5y's independent q0 and q1 multiply streams, delayed limb and addition carry. G34: for m=max(limbs(Y),limbs(Z)), at most m+3 output limbs suffice for a two-limb factor; flush all carries and preserve exact sign and zero. G35: compile all three original four-corner predicates, using factor 1 or indexed q and retaining the intermediate upper-source test. G36: preserve original source indices, signed tail, positive gauge, G14 raw-coordinate reopening and suffix-only retries. G37: compare allocation and actual scan cost against COMP5x/y; retaining base and Y can offset savings, and factor-one streaming may lose high-to-low early exits. The even lower-floor product remains. Exact materialized fallback for unsupported GMP configuration/wide factor. Owners: scripts/pi_p0_affine_boundary_sector.hpp and scripts/check_pi_p0_affine_boundary_schedule.cpp. No compilation, execution, kernel or benchmark acceptance; prior candidates retained. Next: cost-aware blockwise carry bounds, exact early termination and quotient consumer liveness, not unconditional streaming promotion.

## COMP6a — bounded bidirectional prefix observer (untested)

G38: put P=M^h, decompose Y=P Y_H+Y_L, Z=P Z_H+Z_L, and 2^k B=P B_H+B_L. The literal signed residual is P delta+q(Y_L+Z_L)-B_L, delta=q(Y_H+Z_H)-B_H. With q>0 and h>0, delta>=1 certifies positive, delta<=-t*q certifies negative, where t is the number of globally nonzero affine operands (1 or 2). Otherwise retain unresolved; h=0 gives exact sign including zero. Proof: lower term >=-(P-1) and <=t*q*(P-1). No claim that delta=0 is original equality.

G39: native virtual high-window extraction by public GMP value limbs and bounded mpz_import, including arbitrary dyadic offsets and nail bits. Prefix widths 4,8,16,32 limbs, aligned to maximum of original operand and shifted-boundary supports; the small q can grow the computed prefix by at most two product limbs plus one affine limb. Read only high windows, no full shifted boundary, lower remainder or product. If no strict sign follows, use the exact COMP5z carry observer (or its exact materialized fallback). Keep all three four-corner tests and source index/scale/signed residual/zero-mode/suffix contracts.

G40: cost ledger counts attempts, decisive prefixes, exact complete prefixes, window slots and fallbacks. This is a bounded heuristic schedule, not calibrated. Prefix work is repeated; cap prevents unbounded doubling cost. Critical negative control: near a decimal floor boundary the relative gap can be O(10^-d), so constant-width high prefixes may fail on nearly every large successful admission. A narrow interval is not evidence of speedup; compare bypass, prefix, streaming and materialized GMP with actual source-matched branch frequencies and heap/time. Do not promote until measured Pareto. 

G41 remains open: original lower-floor parity product and quotient liveness. Investigate lower quotient's exact slack/remainder as an optional shared consumer, despite prior remainder-elimination cuts; retain COMP5w/x/y/z and measured COMP5j for independent comparisons. This is geometry-first and not unconditional streaming.

Owners: scripts/pi_p0_adaptive_boundary_sector.hpp and scripts/check_pi_p0_adaptive_boundary_schedule.cpp. No compilation, numerical execution, formal kernel checks, CI or benchmarks per inherited deferral; original analytic identity/Bishop same-real and external SOTA remain open.

## COMP6b — both-parity signed local slack fibre (UNTESTED)

Reuse original COMP5q even-parity residual witness in scripts/check_pi_p0_projective24_residual_witness.cpp, not a new independent arithmetic theorem. For original indexed edge (n,T',Q',V), q=q_n, signed defect V-qT', set e=abs(V-qT') only after parity sign validation. Let (a,b)=(q,1) even or (1,q) odd, (Nh,Nl)=(V,T') even or (T',V) odd. Then ab=q, b Nh-a Nl=e. With Z=HQ', Y=ZR, the upper-minus-lower enclosure width is (Ye+b Z Nh)/(2^k Nh Nl).

G41/G42/G43/G44: obtain aY=2^k(x Nh+rho)+ell by nested divmods, L=Nh-rho>0, J=b L-(x+1)e, C=ell+aZ. Exact original admission residual multiplied by a is b C-2^k J; intermediate upper-source lower-root residual multiplied by a is b ell-2^k J; opposite lower-source upper-root residual is C-2^k L. Strict negative first admits, strict negative second refines root, nonnegative third refines root, else append original suffix. J<=0 makes the first two strict predicates impossible, but J=0 and ell=0 is an inhabited equality, not invalid source. At k=0 ell=0. The signed defect is preserved by the original edge and its index; no loss of source zero mode or scale receipt.

Native owner scripts/pi_p0_slack_sector.hpp reuses signed defect during validation, overwrites the packed lower numerator with dyadic quotient, pays for two actual remainder outputs, releases it before slack/correction work, and reuses base storage for C. No retained Y or materialized absolute (x+1)Nl or (x+1)Nh threshold. Odd parity may still materialize q*C and q*ell; even lower aY product still exists. Uses existing virtual shifted comparator; signed J domain handled before positive comparator. Counters distinguish skipped nonpositive-J predicates, exact zeros (including inferred), executed comparisons, divmods and parity/tail product sites. Raw L and J are not generally homogeneous: G14 carry t=floor(G ell/2^k) gives L_raw=G L-t, J_raw=G J-b t, C_raw=G C-2^k t. Thus b C_raw-2^k J_raw and C_raw-2^k L_raw scale by G; b ell_raw-2^k J_raw does likewise. Preserve original gauge recipe and explicit carry reopening, never silently identify normalized remainders with raw ones.

G45: compare against COMP5q and COMP5w/x/y/z/6a with actual original-source hashes, strict boundaries, all parity and retry sectors, GMP allocation capacities, scratch, tail multiplication x*e, divmod incremental cost, and suffix-only schedules. No claim of lower latency/peak heap: retaining remainders and multiplying x*e costs real work. Next candidate: bound x*e from original next-term magnitude and use a sufficient slack admission, fall back to exact J only when required; keep equality/unknown distinct. No compilation, tests, formal kernel, CI, benchmarks or external SOTA comparisons per inherited deferral. Analytic identity/Bishop same-real still open.

Integrated owner scripts/check_pi_p0_slack_schedule.cpp; prior candidates unchanged.

## COMP6c — integer tail budget and source-indexed sufficient admission (UNTESTED)

G46: reuse COMP6b's original signed defect e=abs(V-qT'), parity factors a,b and L=Nh-rho, C=ell+aZ. Set E=(x+1)e, K1=bL-floor(bC/2^k), K0=bL-floor(b ell/2^k). K1<=K0. Exact policy: E<K1 admits; otherwise E<K0 refines upper radical; otherwise C>=2^k L refines lower radical; otherwise extend the genuine original suffix. This is the same three-boundary decision, not a different analytic stopping rule. A budget tie E=Ki is NOT necessarily an exact original boundary zero: the corresponding dyadic numerator must also be divisible by 2^k.

Original source bound: |p_j|/q_j < 1728/640320^3=1/53360^3<2^-47 for j>=1. For an authenticated ordered P/Q/T producer, e=Q' q_n (A+Bn) product_(j=1)^n |p_j|/q_j, hence e<Q' q_n (A+Bn) 2^(-47n). This is a source-relative mathematical enclosure; projective gauge cancels from the ratio. It does NOT follow from the signed cone alone. Runtime still obtains exact e from original edge; no claim to have eliminated that producer or evaluated the source envelope as a runtime admission predicate.

G47: for positive u=x+1,v=e, K=K1, first test L2(u)+L2(v)<=L2(K)-1, sufficient for u*v<K. If inconclusive, obtain at most 64 high bits of each operand with shifts su,sv, and use strict upper bound (hu+1)(hv+1)2^(su+sv); compare virtually against K without constructing the shifted bound. K<=0 never admits. A failed bound is UNKNOWN, not a sign/equality; exact u*v is constructed once on fallback, then reused for both K1 and K0. No exact tail multiply on sufficient admission; no changed retry sectors. This fixed 64-bit prefix is a heuristic cost choice, not optimality. The radical budget itself requires a dyadic quotient; odd parity still pays q*C.

BIDI: for w=bC or b ell, let eta=w mod 2^k, K=bL-floor(w/2^k). Under authentic G>0 and carry t=floor(G ell/2^k), Lraw=G L-t and wraw=G w-2^k b t, so Kraw=G K-floor(G eta/2^k), Eraw=G E. Since 0<=floor(G eta/2^k)<G, E<K iff Eraw<Kraw. The same holds for K0. Dyadic ties are representation-dependent; original signed residuals and exact zero remain homogeneous by G45. Original source zero, signed tail, n,d,rootBits and indexed scale recipe remain separate.

G48: measure source-matched incremental divmod, budget-shift and parity costs, bounded-prefix decision rate, fallback cost, live GMP allocation and exact output hashes; compare with COMP6b, COMP5q, COMP5w/x/y/z and COMP6a. The original source bound motivates cutoff planning but does not prove typical budget margin or speedup. Next investigate retaining the signed next-term defect at the producer rather than recomputing V-qT', and replacing absolute edge endpoint storage by reversible signed coordinates with fail-closed provenance and measured liveness. No execution, compilation, formal kernel, CI, benchmarks or SOTA comparison per inherited deferral. Classical analytic identity/Bishop same-real remain open.

Owners: scripts/pi_p0_tail_budget_sector.hpp and scripts/check_pi_p0_tail_budget_schedule.cpp. All earlier candidates retained.

## COMP6d — producer-retained signed defect carrier (UNTESTED)

G49: retain (n,T',Q',delta=P'f_n), f_n=p_n(A+Bn)<0, rather than (n,T',Q',V=q_n T'+delta). Exact BIDI V=q_n T'+delta and P'=delta/f_n, with divisibility checked when reopening. Original positive gauge G scales T',Q',delta uniformly; signed source zero remains excluded for active n>=2, and the empty interval identity remains (P,Q,T)=(1,1,0). The original split producer and scale recipe authenticate provenance separately, not merely the parity cone.

G50: private factory retains the signed defect, overwriting moved P storage. Positive adjacent numerator follows immediately for even n; for odd n verify q_n T'>|delta|. With positive factors T',q_n and e=|delta|, L2(T')+L2(q_n)-2>=L2(e) suffices (strict inequality follows from e<2^L2(e)). Otherwise check exact V>0 once at construction. Private coordinates prevent arbitrary caller injection; shape checked by classifier and reopening. Even lower quotient needs V, materialized once per attempt and released after slack L; odd lower quotient uses T' and does not need V unless producer positivity fallback or explicit reopening is requested. Classifier consumes delta directly; even uses reference, odd currently copies magnitude. Same COMP6c budget and fallback helper, same strict/equality semantics. Avoid old scheduler's repeated V-qT' cone reconstruction and classifier's independent defect reconstruction.

G51: for true indexed suffix (P_s,Q_s,T_s) on [n,m), ordered composition is P_m=P'P_s, Q_m=Q'Q_s, T_m=T'Q_s+P'T_s. Hence delta_m=(delta_n/f_n)P_s f_m. Exact divide first by f_n, not by an arbitrary projective factor. Integrated scheduler reopens P' once (checked exact), moves Q',T', drops old delta, then reuses existing ordered split/join and produces new delta_m. This is suffix-only and preserves the index and scale recipe. Direct defect-native join without intermediate P is not implemented; P is also needed by the T cross-term. Root-only retries retain the same carrier.

G52: actual GMP scratch, odd magnitude copy, producer positivity check/fallback, per-attempt even endpoint reconstruction, exact reopening and prefix/suffix work require matched cost measurements. Compare all preceding candidates and independent certified output, not operation-count-only dominance. Earlier COMP6c retains V across root retries, so repeated even materialization may offset gains. No compile, numerical test, formal kernel, CI or benchmark per inherited deferral. Next: source-specific quotient decomposition of the even endpoint or cached/lazy endpoint policy; compare against simply retaining P' with lazy defect construction. Do not promote until physical Pareto and independent analytic identity/Bishop same-real gates are paid.

Owners: scripts/pi_p0_defect_source.hpp, scripts/pi_p0_defect_sector.hpp, scripts/check_pi_p0_defect_schedule.cpp. Existing COMP5t/6c and historical measured COMP5j remain intact.

## COMP6e — integrated direct quotient, signed correction, and literal corner acceptance (UNTESTED)

Donor pattern: the attached Langlands R208 restricted mixed-geometry work constructs the consumer interface from the original source rather than expanding a raw frontier, and charges precision-probe overhead against savings. This is methodological inspiration only, not an imported arithmetic proof or Langlands correspondence. Keep the original index n, source gauge, signed defect, zero, and independent precision d,b,k. All previous candidates are retained as comparisons, except the explicit portability repair below.

G53: for even n write T=T', e=delta_n>0, q=q_n, V=qT+e, D=2^k, Y=ZR. Directly divide the unscaled Y: Y=D(x0 T+rho)+ell with 0<=rho<T, 0<=ell<D. Let F0=q rho-x0 e, F=F0+floor(q ell/D), eta=q ell mod D. Then qY=D(x0 V+F)+eta; F<V and the literal lower floor is x=x0+floor(F/V). No universal single-integer correction assumption. Odd route reuses COMP6d since its lower floor is already the unscaled x0. Never build full qY on either path.

G54: if x0=0 or a strict bit-length product bound proves x0 e<=q rho, x=x0 without constructing either product. Otherwise compute F0 by q*rho and signed submul x0*e. If F0>=0, x=x0 and no parity dyadic carry needed. Only F0<0 consumes q*ell and its exact dyadic divmod. F>=0 gives x=x0; observed F=0 is a valid neutral state, not invalid or empty. F0=0 alone does not establish F=0. If F<0, h=-floor(F/V)>=1. Put dF=-F; h=ceil(dF/V). If dF<=V, h=1 and corrected slack L=dF, no extra division. A sufficient bit-length bound dF<qT proves this without constructing V. Otherwise materialize V once and compare exactly; only dF>V pays signed divmod and h>=2. General corrected slack L=V-r where F=-hV+r and 0<=r<V. This branch can have arbitrarily many corrections on admissible source-shaped synthetic edges; no universal source-specific bound on their frequency is asserted.

G55: if x=x0, the full upper admission reduces to ell+Z<D(T-rho), otherwise refine upper radical (upper-source lower root lies in floor x0). If F<0, x<x0 and both upper strict predicates necessarily fail. The opposite lower-source upper-radical crossing is eta+qZ>=D L, otherwise append genuine [n,m). Exact ties retain the original non-strict/strict semantics. No approximate stopping rule or extra source/root retry. All original source rebuilding, exact reopening, root-only and suffix-only contracts from COMP6d preserved. 

G56 BIDI: for positive original gauge G let t=floor(G ell/D). The common rho_raw=G rho+t and ell_raw=G ell-Dt. Hence F_raw=GF+c where c=floor(G eta/D), 0<=c<G, and eta_raw=G eta-Dc. If F=-hV+r, then F_raw=-h(GV)+(Gr+c), with 0<=Gr+c<GV; correction h and x invariant. The corrected slack reopens as L_raw=GL-c. The original corrected radical residual eta+qZ-DL scales exactly by G, including zero. Common unscaled slack residual ell+Z-D(T-rho) likewise scales by G. Inhabited F=0 is not itself a projectively homogeneous observable; preserve dyadic carries and original source coordinates.

Implementation: scripts/pi_p0_quotient_sector.hpp and scripts/check_pi_p0_quotient_schedule.cpp. The new even path counts common quotients, sufficient bit proofs, exact signed residual products, dyadic carries, no-correction and single/multi-correction sectors, endpoint products, and corrected radical products. No unbounded prefix-probe heuristic; cost of the remaining signed tail multiplication and possibly a second integer division remains charged. No claim of heap or latency dominance; compare with historical COMP5j and all relevant COMP5q/5w/6b/6c/6d alternatives. Retaining signed source defect and an exact pair of remainder outputs still incurs real memory and arithmetic.

Portability blocker found by inspecting the available standard GMP header: mpz_fdiv_qr_2exp is not a supported GMP API. New scripts/pi_p0_gmp_dyadic_divmod.hpp uses the standard separate floor quotient and remainder calls in alias-safe order, with distinct output guard. Replaced calls in the eight inspected candidate files (dyadic_sector_contraction, shared_radical_sector, slack_sector, tail_budget_sector, defect_sector, quotient_sector headers, residual_witness and projective24_residual_witness C++). This changes operation-site accounting: one logical dyadic divmod means two supported calls, not a single native fused GMP operation. The historically restored baseline files remain untouched. Source-level correction, not compilation acceptance.

Consolidated next acceptance owner: scripts/check_pi_p0_quotient_sector_exact.cpp (authentic raw ordered prefix cases, synthetic signed cone, explicit materialized corner oracle, prior COMP6d equivalence, gauge reopening, negative/multi correction, zero root, k=0 and limb-boundary shifts, alias checks against generic mpz_fdiv_qr). Added but NOT compiled or executed. Separate actual source shapes from synthetic controls. Compare whole original source schedules, independent decimal hashes and matched per-stage time, GMP alloc/scratch and RSS, including probe cost and rare retries; do not select production default from algebraic counts. Remaining P0: independent analytic identity/Bishop same-real, native exact-source acceptance, calibrated cost Pareto, external independently certified speed comparison. No more purely representational candidate extension before evaluating the now-integrated routes unless user explicitly directs further mathematics. No compilation, numerical execution, CI, kernel or benchmarks performed in this tranche per inherited deferral.

## 25 November — indexed quotient transport cube and consolidated acceptance frontier (UNEXECUTED)

Live donors inspected: #1291 at 65950c7fe941a817464ea647cbfc49c58f7db6ab (actual scripts/check_ssp_singer_incidence_wheel_20261125.py blob a68708f3fa817f927fa80f0d2f10ebb60fc7a119); #1552 at 4e9049ab899a9beee76b493698cb647cda116c48, #1549 at e8bd35e56c6f0291f5f0d9a4bf1788b79cc14962, #1547 at 8cf8761e5c1da5346d4604dfa81bd25611a8fccb, #1548 at 87c46ab1c0a4ce7910ddcbf16bcce9aa62d37d8a (metadata audit except named wheel source). JMD retains SSP/prime-encoding motivation, Conway FRACTRAN, Griess/Sah and Singer classical geometry; DASHI wheel attachment is a donor pattern, not an imported pi theorem. No 13-wheel, group equivalence or prime-lane speedup is asserted for Chudnovsky. The important donor is signed transport/history, including nonempty neutral fibres; F8 same-index source capture and Langlands charged discovery costs are methodological donors.

Retain original source prefix (P,Q,T), n, decimal d, radical b, D=2^(b-d), R=floor(2^b sqrt(10005)), Z=426880*5^d Q, and common quotient x0 with W=ZR-D x0 T=D rho+ell. W is a homogeneous full residual under positive source gauge even though rho and ell individually have carries. Zero W is an inhabited exact integer boundary, not an empty prefix. No claim to preserve all producer history from x0,W alone.

G57 — original suffix [n,m) with triple (p_s,q_s,t_s) in the SAME chart. Let T_m=T q_s+P t_s, Q_m=Q q_s. Unreduced new residual relative to old x0 is W*=q_s W-D x0 P t_s. Then h=floor(W*/(D T_m)), x_m=x0+h, W_m=W* mod (D T_m). For radical refinement b->b+s, r=R_new-2^s R in [0,2^s), W*=2^s W+Z r, D_new=2^s D; take the same signed divmod. Combined source/root unreduced residual is 2^s q_s W+q_s Z r-2^s D x0 P t_s. Neither correction is universally single-integer or free. A source correction must retain the original P t_s sign and the true suffix index.

G58 — gauge axis is indexed, not a fixed global label: G_n=product_(1<=j<n) gcd(|p_j|,q_j)=product 24*h_j, matching the existing native source recipe. For [n,m), G_m=G_n G_[n,m). Reopening before suffix composition requires the original raw suffix, not the normalized suffix again. Gauge maps W->G_n W, D fixed, x0 invariant. The two normalized source/root operations commute after Euclidean reduction by uniqueness of quotient/remainder of the same original terminal numerator and denominator; gauge commutes with each provided this indexed suffix factor is respected. Thus six faces and six endpoint paths on the explicitly typed three-axis cube; this is not a statement about arbitrary source revisions, physical time, Frobenius or autonomous FRACTRAN computation. Identities at zero source/precision step retain their typed command histories. Literal four-corner residuals scale by G_n and preserve exact signs and zero, including COMP6e parity correction. Separate zero correction h from zero W and zero signed tail (excluded active source).

G59 — added scripts/check_pi_p0_indexed_quotient_cube.py: independent integer oracle using original leaf formula and gcd gauge, explicit suffix/root/gauge transitions and all six faces/endpoint paths, independent full-prefix rebuild comparison at each vertex, BIDI numerator reconstruction, even quotient correction and signed corner gauge checks. Includes identity source and precision steps; no test or compilation executed. It is not linked into the production scheduler: W and x0 P t_s may be large, and reusing a quotient may cost more than recomputing. No promotion from algebraic transport to a performance benefit. Need native trace/fixture comparison, exact original decimal hashes and charged incremental-vs-full cost including source/gauge reopening.

P0 sequencing remains the four major obligations in COMP6e: original analytic Chudnovsky identity/Bishop same-real; exact native source acceptance; measured physical Pareto; external independently certified comparison. This cube is an acceptance/provenance aid, not another unconditional optimization. Inherited execution deferral remains; no CI, tests, compilation, kernel or benchmarks in this tranche.

## Analytic endpoint — 25 November, quantitative same-real cut (UNTESTED)

See `Docs/proofs/Paper9BishopQuantitativeEndpoint20261125.md` for the controlling source-specific proof: uniform negative-real q branch bounds, fixed precision n=max(1,ceil((k+5)/41)), b=k+2, literal Machin partial vs CH midpoint error <=4/(k+1), and native source-written limit consumer. Classical identity premises and prior CM receipts explicitly retained. New `DASHI/Foundations/BishopChudnovskyMachinLimitWeldExact.agda` consumes the actual original Machin partial stream and quantified embedded rational approximation bound; all-index native source producer and sound semantic reflection remain OPEN. `scripts/check_pi_p0_quantitative_same_real.py` fixtures UNEXECUTED. No kernel, compilation, tests, benchmark, CI or SOTA claims. Existing source/precision/gauge cube remains independent and production scheduler unchanged.

## 25 November — literal rational Chudnovsky midpoint and native source-bound limit (UNTESTED)

See `Docs/proofs/Paper9BishopLiteralMidpointReflection20261125.md`. Recovered original qMachinStage convergence and the existing full source-written 4/25^k native Machin remainder; reuse canonical floor-square-root and original split algebra. New `DASHI/Foundations/BishopChudnovskyRationalMidpointExact.agda` computes a fail-closed literal interval/midpoint with original indexed leaves and fixed cutoff/precision. New `DASHI/Foundations/BishopChudnovskySourceBoundLimitExact.agda` binds each certificate to that computed interval and transports its rational error to the original Bishop carrier, using pinned vendor absolute-value/subtraction laws and native reciprocal convergence. The ordinary all-index bound is derived on the previous classical identity premises; the native total-success/finite-sum/analytic reflection producer of StageCertificate remains OPEN. Source-written only, no compiler, test, benchmark, CI or kernel claim. Production GMP scheduler unchanged.

## 25 November — geometry-first endpoint reverse-solve (source-written, untested)

Controlling remaining dependency register: `Docs/proofs/Paper9GeometryFirstEndpointClosure20261125.md`. New `BishopChudnovskyIndexedEdgeAlgebraExact.agda` writes literal prefix and signed adjacent-edge identities. Finite cone: adjacent partial-sum brackets nest because the next signed defect reverses orientation and shrinks relative to the transported denominator by <2^-41; base S2>A/2 yields all-index positive sums in ordinary arithmetic. Native sign/order/totality proof remains open. Analytic A1–A7: phase, normalized q/modular identity, degree-41 cyclic self-isogeny, isolated double root, transverse cubic jet, local hypergeometric uniqueness, positive terminal normalization. Two routes: actual Bishop analytic construction or sound universal rational proof reflection, neither yet native-closed. Decimal-floor apartness/fair retry separate from width totality. No new arithmetic candidate, compilation, execution, CI, kernel or benchmark. Existing status flags unchanged.

Endpoint register section 6 reconciles actual `DASHI/Interop/LeanMoonshineDeltaIdentityPinnedReceiptExact.agda` and companion branch source declarations for eta24_eq_normalizedDelta, levelOne_weight_zero_const and exists_smul_eta24. External proof receipt retained; no new kernel replay. The prior two-slice kappa formula is derived with explicit conjugate-tangent apartness and BIDI beta reopening, avoiding quadratic-field inversion for the scalar; source Taylor binding and universal rational reflection remain open.

## 25 November — signed positive gap, Hecke generator BIDI and direct q uniqueness (UNTESTED)

See `Docs/proofs/Paper9SignedConeHeckeQCoordinate20261125.md`. New `BishopChudnovskyPositiveGapExact.agda` writes universal positive polynomial contraction, literal positive Q product and paired original affine identity. Pair positivity and nested interval totality derived mathematically, native T sign/positivity still open. Explicit 42-chart S/T action with unimodular corrections and inverse reconstruction reduces A3 to analytic j invariance, coefficient reconstruction and symmetry; 84-edge regression source unexecuted. A6 now uses direct original-q triangular coefficient uniqueness with |z|<=1345/3375<1 on the whole small complex disk, removing inverse-coordinate continuation from the critical path. Native Ramanujan/source reflection and same-real certificate remain open. No execution or new kernel claims; no GMP change.

## Native paired positivity/totality source extension (unexecuted)

New `BishopChudnovskyPairedTotalityExact.agda` writes explicit integer equality witnesses for positive, negative and nonnegative original coordinates. `weakGapIdentity` removes the factor 2^41 using the existing positive gap; `pairGapExact` proves the actual signed paired contribution is a positive successor; `evenWPositive`/`oddWNegative` prove the actual indexed product orientation; `evenTNonnegative`, `evenNonemptyTPositive`, `oddTPositive`, `allNonemptyTPositive` give the paired induction from T0=0. `positiveViewTotal` and `intervalAtTotal` rewrite the actual evaluator with these witnesses, not an alternate value. Corrected twoStepSource solver to expose both original next p and a variables so associativity is paid by the ring solver. These are complete intended proof terms, uncompiled; elaboration, pinned library compatibility and kernel closure remain open. No claim that source terms were accepted. Stronger S>A/2, shrinking widths, factorial interpretation and universal analytic overlap still require native proof; totality alone does not certify pi.

## 25 November — original rational overlap / Bishop order owner reconciliation (UNTESTED)

See `Docs/proofs/Paper9RationalOverlapBishopReuse20261125.md`. Recovered pinned bidirectional rational-order reflection, existing Machin rational stages and exact 4/25^k Bishop remainder, strict 3<pi_M<22/7, actual interval/regular-real constructors and finite convolution donors. New `BishopChudnovskyRationalOverlapExact.agda` writes sharp midpoint bound from the two literal crossed endpoints, membership-to-cross reflection and all-index source certificate consumer. At k=0 use 22/7 instead of 4 to preserve the error budget. Native source width/rate budget and analytic crossed inequalities remain OPEN; no proof promotion. Direct original-q triangular coefficient proof refined; no new generic formal-series engine. Lean #104 source theorem recovered, proof replay not observed. No compilation, tests, CI, kernel or benchmark in this cut.

## Rate-budget source proof extension (uncompiled)

`BishopChudnovskyOverlapBudgetExact.agda` writes the universal Nat inductions k+1<=2^k and 4(k+1)<=25^k for k>=1 (the latter uses the exact positive step margin 188+96j). Existing FiniteNatFractionOrderExact reflects the denominator cross-products, with actual source Machin denominator and explicit nonzero witnesses. `budgetFromWidth` derives the entire sharp-radius budget from the literal fixed-schedule width <=2^-k: for k>=1 h+e<=(3/2)/(k+1)<=4/(k+1); k=0 uses the exact rational inequality 1/2+22/7<4. `literalConvergenceFromWidthAndCross` now needs just two all-index source families: literal CH width and literal rational crossed endpoint inequalities. It consumes previous paired totality and overlap modules. No kernel or compilation, no guarantee of elaboration, no analytic overlap proof assumed. This supersedes the earlier remaining separate rate-budget obligation at the source-written level only. Native F3 width, actual common-value A1-A7/F5 cross, and exact-head verification remain open.

## 25 November — integer width residual and pinned Ramanujan rigidity (source-written, untested)

See `Docs/proofs/Paper9IntegerWidthRamanujanRigidity20261125.md`. New `BishopChudnovskyWidthSourceExact.agda` writes actual signed defect magnitude contraction, all-index M^n H_n<=A Q_(n+1), translated lower plane 2T-AQ>0 by paired induction, radical bound, cutoff exponent and final integer width numerator budget. Ordinary full width proof: J=Q_n H_n, K R J<=2 tL tH, K dL<=tL imply width<=3/s<2^-k. Native cross/parity, plane/order, power schedule and fraction reflection joins remain; no literalWidth theorem promoted. Recovered actual Lean levelOne_nonpos_wt_const (stronger than weight-zero); f/Delta eliminates weight 4/6/8 cusp forms, Serre/log-derivative anomaly cancellation proves all three classical Ramanujan identities on the named analytic premises. Formal derivative/quotient/cusp packaging and same-object reflection remain. No new production candidate, tests, CI, compiler, kernel or benchmark.

## 25 November — literal width reflection and Hecke Laurent reconstruction (source-written, unverified)

See `Docs/proofs/Paper9WidthReflectionHeckeLaurent20261125.md`. New `BishopChudnovskyWidthReflectionExact.agda` writes intended `literalWidthBound` on actual O.window, using positiveView source equalities, signed cross magnitude, both ordered branches, source schedule and denominator-cleared corner comparison. No compiler or kernel acceptance; possible elaboration repairs remain. A3 ordinary proof uses actual 42 Hecke charts, pole bounds, existing level-zero rigidity after Laurent cancellation, dual adjugate symmetry and distinct leading Puiseux branches. Original diagonal and fixed slice scripts are linked through exact cyclotomic norm/log-derivative recurrence and sufficient Laurent truncations; no full bivariate table necessary. Analytic source packaging/reflection and universal cross remain open. No tests, CI, benchmarks, new GMP candidate or status promotion.

## 25 November — selected CM real isolation and direct signed tau Taylor (UNTESTED)

See `Docs/proofs/Paper9CM163SourceReplaySignedTaylor20261125.md`. Selected q is real; actual j real slice plus original dyadic half-unit enclosure and complementary coefficient dominance avoid general complex norm machinery. Direct Taylor in original tau coordinate gives denominator-cleared 163 S2*((alpha^2-alpha)*j''+j'*h'')=(j')^2*(alpha^2-alpha)*(41 P3-326 S3), no local inverse j or quadratic-field inversion. `JInvariantCM163SignedTangentPolynomialExact.agda` writes integer polynomial identities and signed discriminant. `scripts/check_cm163_source_bound_jet.py` adds original pinned coefficient forward Laurent replay, original 128-bit dyadic endpoint binding, integer dominance and signed scalar jet receipt; UNEXECUTED. Native analytic source/finite coefficient reflection and universal rational cross remain OPEN. No kernel, tests, CI, benchmark or proof promotion. Existing CM computation owners and attribution retained.

## 25 November — original Eisenstein completion, Euler jets and Rankin–Cohen reduction (UNTESTED)

See `Docs/proofs/Paper9OriginalEisensteinEulerJets20261125.md`. Recovered actual Agda unit-disk completion, Round11 Machin source, lattice same-object compiler, native proof-relevant j, and Lean literal E4/E6 target semantics, normalized Delta cusp and nonvanishing. New `JInvariantBishopEisensteinRealSliceExact.agda` writes realness of literal completed E4/E6/Delta/j from actual real q and negative Delta, via original series limit uniqueness. New `JInvariantBishopEisensteinEulerJetExact.agda` writes all-order literal weighted coefficient absolute convergence, using existing polynomial-geometric majorants; derivative interpretation still open. New `JInvariantEisensteinRankinCohenResidualExact.agda` writes signed residual adjugate identities: weight12 cusp bracket 3E6 DE4-2E4 DE6=1728 Delta follows on named analytic premises from existing weight12 rigidity/first coefficient, giving both DE4/DE6 via determinant Delta, with only weight4 E2 correction remaining. No independent E2 model or new carrier; native derivative/slash/cusp packaging and actual source binding remain. No execution, kernel, CI, benchmark or proof promotion; all new terms uncompiled.

## 25 November — actual cusp derivative target and level-three coefficient bridge (UNTESTED)

See `Docs/proofs/Paper9EisensteinThreeB54Derivative20261125.md`. Reuse pinned Mathlib cuspFunction/qExpansion analytic derivatives on original E4/E6; companion branch `research/paper9-original-eisenstein-derivative-20261125` at 7ffe113edd10d2ba1a28fcea5be00b888bccaf29, source-written actual q-bracket derivative at zero and weight12 rigidity consumer. Slash/cusp packaging, Delta product derivative and native binding remain open. New `JInvariantEisensteinThreeB54CoefficientBridgeExact.agda` ties actual 240,-504 to 744,1728=32*54 and classical level-three t=(eta/eta3)^12, j=(t+27)(t+243)^3/t^3, whose first q coefficient is exactly 54+196830. Independent Leech theta/eta chart yields 196560+6*54. External Maier/Elkies and classical theta attribution preserved; no Monster equivariance or analytic theorem promoted from coefficient arithmetic. No new P0 dependency, execution, CI, kernel or benchmark.

## 25 November — 66/12 original Tate signed ultrametric and Delta derivative (UNTESTED)

See `Docs/proofs/Paper9Tate66UltrametricDeltaDerivative20261125.md`. New `JInvariantThreeBTate66UltrametricExact.agda` reuses actual Tate dimensions and SSP369 prefix carrier, signed VpDepth comparison gives v3(66-12)=3 and gain2 versus unsigned 78 gain0. Y443 actual 66 pairs/12 nodes/78 relations matches signed cardinality only; natural arm swap virtual trace is not Tate trace. Fricke central shell t=27u preserves v3(u+1) and both j-chart valuations on named rational premises. Lean companion c3b77fc94f302d8a2b4bf733c5f1ff4229ae7146 writes literal Delta cusp-function identity, derivative and Ramanujan46 consumer needing actual bracket and disk membership. No new kernel, compiler, tests, CI or benchmark; no analytic localization or F5 proof promotion.

## 25 November — original 66 prefix and actual bracket cusp closure (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9IntegratedFrontier66Cusp20261125.md`. Original 66 means ordered 6->6 neutral prefix, not integer sixty-six radix expansion. New `TernaryThirteenNeutral66PrefixExact.agda` reuses original word/pants/cylinder and split/join owners for prefix, suffix round trips and nonzero/last-coordinate non-descent witnesses. No Tate-to-word semantic map asserted. The earlier signed valuation chart is a distinct arithmetic observable. Lean companion `a541a44dc990cba133d031eabc9c01adf287beeb` adds actual `Paper9BracketCuspClosure.lean`: intended holo/zero cusp, derivative anomaly cancellation, genuine CuspForm packaging, actual q-disk equality and first coefficient. `ramanujan46FromSlash` consumes actual slash covariance, which reduces to the two original derivative chain rules; E2 correction still open. All terms uncompiled; no native/Lean kernel, tests, CI or benchmark. Manuscript main text reconciled, historical ledger preserved. A2-A7/F5 remain critical; 66 is secondary donor, not a P0 dependency.

## 25 November — original Euler Möbius transport (SOURCE, UNVERIFIED)

Lean companion `23602955180fdddd46375c5ce6198f504950a0e6`, then `3063310926b1ab038a85ab0fbedf65ea63d81f91`: `Integration/Paper9EulerMobiusTransport.lean` writes actual qParam derivative, original modular-form cusp extension derivative, determinant-one fractional-linear derivative, local (only on H) transformation equality, derivative equality and signed Euler anomaly. `dxTransport`, `dyTransport`, `originalBracketSlash` and `originalRamanujan46` now have intended unconditional proof terms from the pinned imports, superseding the prior explicit derivative-transport hypotheses at SOURCE level. `originalE2Transform` writes the actual normalized Delta log derivative anomaly via the same weight-12 transport; `e2CorrectedCovarianceAlgebra` writes exact cancellation after its second derivative. Still unpaid: actual derivative of the logarithmic anomaly and corrected weight-four modular form/cusp quotient, all new Lean elaboration and kernel replay, A3-A7/F5 native/source reflection and F1/F6-F9. No new compiler, executable checks, CI replay or benchmark. Do not call A2 kernel-closed or the independent Bishop endpoint proved.

## 25 November — original Ramanujan system and compact q differential transport (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9RamanujanQHypergeometricClosure20261125.md`. Lean companion `dd30fc1016177e08a4f13588e55247e2ad671c5c` then `9ee290cd9343a85aa0e3710651c42672812f1d87` writes intended `originalRamanujanSystem` on actual E2/E4/E6, reusing original eta-product analytic unit, actual local derivative anomaly, weight4 cusp packaging, existing eta24 domination and negative-weight rigidity. All source terms uncompiled; no kernel closure claimed. New `Paper9HypergeometricQTransport.lean` writes actual punctured-q transport and differential coordinates a=(E2 E4/E6-1)/6, h=E4^3/E6^2-1, L a=-a^2/2+h(a/2+5/72), L h=h(h+1), L z=z. Two exact polynomial multiplier identities reduce ODE to actual LF=aF and iterated product law; actual binomial branch and convergent coefficient semantics still open. A3–A5, A1/A7 native binding, F1/F5 and acceptance unchanged. No compilation, executable checks, CI or benchmark; no new production optimization.

## 25 November — selected hypermetric comparison and cusp-order transport (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9HypermetricCuspOrderFactorial20261125.md`. Actual RG two-metric, H3 residual and indexed chart transport donors audited; no 369/analytic metric identification. Fixed-radical reciprocal adjacent widths have exact shared-endpoint distortion S_n/S_(n+2), at most 2 on actual source band; signed sum contraction 2^-41 transfers to <=2^-40, radical refinement separately bounded. Lean companion `e9b8e422c4b8503074dbf45d6bf6632bd711bbae` writes actual normalized log sqrt branch/first derivative, cusp-order leading multiplier n and residual n^3*g0, all-index factorial ratio and actual CM leaf ratio, exact rational metric comparison. Actual H analytic ODE, germ uniqueness assembly and native prefix/rational reflection remain. All new terms uncompiled; no execution, kernel, CI or benchmark; A3–A5/F5 and acceptance remain open.

## 25 November — actual factorial-series ODE and local hypergeometric identity (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9OrderedCuspActualSeriesODE20261125.md`. Latest #1552 ordered ultrametric and #1545 single residual actual donors read; #1549/#1553 reviewed at metadata level. Lean companion `094b4f6cc9c9a653783d7ff42621dc91e06c4d89` writes all-order normalized germ uniqueness, actual sqrt ODE, literal factorial-series radius and Euler jets via pinned derivativeSeries diagonal, actual composed H(z) ODE, intended unconditional `actualHyperIdentityGerm` and connected-disk consumer `actualHyperIdentityBall`, plus signed period algebra. A6 intended local analytic identity now source-written; selected actual E4/E6 small-disk norm bounds and CM q membership, real-positive branch, CM certificates, native F1/F5 reflection and all elaboration/kernel replay remain open. All new source uncompiled; no executable arithmetic, CI, kernel or benchmark. No donor branch modified.

## 25 November — actual selected CM domain and signed certificate consumers (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9SelectedCMDomainCertificateConsumer20261125.md`. Lean companion `85eff0dd4590c0f6c37f9dc26c02ef68dff95dd0`, `979f2ba17ceb7bb701efc79377b6ff6dfdbf6156`: original Eisenstein shifted series, actual selected GoodZ disk and first-jet equality, degree-80 complementary-factor isolation, signed cubic elimination and positive scalar normalization. Local exact arithmetic checked the domain/period constants and SymPy expanded the three tangent linear combinations identically to zero. Actual Hecke/Laurent/CM coefficient and dyadic certificate reflection, Taylor source, CM point and positive branch binding, F1/A1 and original all-index Bishop rational overlap remain open. No actual packet execution, compiler, kernel, CI or performance claim.

## 25 November — literal F1 prefix and original CM163 exact replay (FINITE PASS; SOURCE UNVERIFIED)

See `Docs/proofs/Paper9LiteralPrefixCMReplay20261125.md`. Exact original Python CM polynomial, signed correction, forward Laurent, complement dominance and 128/160/256-bit dyadic replay passed. Native rational prefix source, Lean all-index factorial target and actual CM-point/jet specialization written, uncompiled. Original CM analytic/finite reflection, actual positive branch, original Machin and native factorial source binding and universal rational crossed inequalities remain open. No compiler, kernel, CI or performance promotion.

## 25 November — actual Hecke/discriminant and reverse-solved period (FINITE PASS; SOURCE UNVERIFIED)

See `Docs/proofs/Paper9ReverseSolvedActualHeckeDiscriminantPeriod20261125.md`. Original 42-chart signed S/T/dual geometry (126 exact matrix checks), actual j first/second derivative and positive period source, normalized discriminant coefficient recurrence (3363/3363 exact agreement) and finite Laurent triangular injectivity source-written. Actual analytic Hecke pole removal, symmetric Taylor, dyadic source/packet reflection, original Machin and universal native rational crosses remain open. No proof kernel, CI or benchmark acceptance.

## 25 November — recovered Hecke owners and direct pole removal (FINITE PASS; SOURCE UNVERIFIED)

See `Docs/proofs/Paper9RecoveredHeckeOwnersPoleRemoval20261125.md`. Four original Hecke source owners restored verbatim; degree-41 row-lattice specialization consumes existing finite fold and retains common scale. Local 126/126 exact geometry checks passed. Pinned full SL2Z generation and weight-zero direct diagonal/slice zero-cusp rigidity source-written; actual analytic Laurent coefficient/order reflection, dyadic source and symmetric Taylor remain open. No compiler/kernel/CI/benchmark acceptance.


## 25 November — actual Hecke finite Taylor remainder (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9ActualHeckeFiniteRemainder20261125.md` (e9f31397a71fa24cab190937d3b446188799184a). Lean companion `7d58601790fce7c4965615d305488c679045e9d0`, `Integration/Paper9HeckeFiniteRemainder.lean`, writes finite signed germ remainder transport, monomial ramification, original normalized diagonal/slice/column expressions and consumer of existing zero-cusp rigidity. Actual Taylor(J_a)=J is forced by actual qExpansion(deltaQ)=deltaPS, deltaQ=q U_a and U_a J_a=x^3, or equivalently finite polynomial quotient with analytic remainder; no eta-log coefficient proof needed. Diagonal J truncation 3322 sufficient (shift 40), slice 1722; existing 3363 coefficient receipt retained. Cyclic phase rotation and exact norm/log recurrence prove descent and specify finite packet divisibility through t^3362/t^1722; actual finite packet reflection remains unpaid. Local SymPy 35/35 algebra/exponent checks PASS; not a full replay. Next exact tasks: actual Taylor coefficient/finite quotient bridge, actual chart exp identities, reflect packet and assemble product/order; then independent A4 dyadic root and A5 bivariate symmetry/signed jet. A7 still conditional; F1–F9/A1–A6 existing gates unchanged. All new Lean source uncompiled, no kernel/CI/benchmark. No new Hecke carrier, no GMP change. Preserve original classical and DASHI/JMD/Aristotle/Mathlib source attribution.


## 25 November — actual Taylor-unit reflection and shifted analytic tail (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9ActualTaylorUnitReflection20261125.md` (7360fafad4dc18212c122229d1b8b9fe3193d9c3). Lean companion `b3ca690606097fd4f1e6d13620c6405088a07919`, `Integration/Paper9ActualTaylorUnit.lean`: source-writes germ equality, factorial-normalized Leibniz from pinned Mathlib qExpansion_mul, Taylor(id)=X, Taylor(deltaUnit)=U by cancelling X at coefficient n+1, and Taylor(jUnit)=J by original JUnique. Pinned iterated dslope/fslope supplies exact analytic shifted tail including zero mode, yielding actualJTruncation for every m. Actual q-chart exponential transport and sharp finite-factor remainder (3323+40=3363 diagonal, 1723 slice) source-written. Local SymPy 42/42 polynomial-model algebra/exponent checks PASS, not a full CM replay or proof verification. No Lean/lake available; no kernel/CI/benchmark. Remaining A3b/c: actual normalized product/phase and columns assembly, cyclotomic descent, sound integer packet reflection. A4 actual dyadic root, A5 symmetric Taylor jet, A7 and F gates remain open. Hopf369 P0H #1554 user-supplied donor is methodological (original object/finite observation/retained tail), not a physical or mathematical identification. Attribution preserved; no new Hecke carrier or GMP change.


## 25 November — actual 42-chart assembly and sector packet gate (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9ActualHeckeProductAssembly20261125.md` (02d7c38ba07e2730b5b002aba8016a0688b25f9e). Lean companion `e54be6f4bd0a1ab6c19b86543e9b45bb18d93d1b`, `Integration/Paper9HeckeProductAssembly.lean`, source-writes actual Fin42 product split, phase product, diagonal/fixed-slice normalization, sharp finite product and column remainders, polynomial divisibility via pinned `Polynomial.X_pow_dvd_iff`, and direct original zero-cusp rigidity consumers `diagonalFromCoefficients`/`sliceFromCoefficients`. The remaining coefficient-zero premises are literal, not a hash. Primitive-root sector cancellation and strong-induction norm recurrence uniqueness source-written; actual rotation/phase-filter and concrete J/H/L/N/column integer reflection remain open. Only 83+43 q coefficients need comparison after rotation reflection; prior integer packet retained. Local SymPy 1.14.0 48/48 exact small-polynomial resultant/recurrence, phase and exponent checks PASS (not full CM replay). Lean/lake not on PATH; all proof terms uncompiled, no kernel/CI/benchmark. A4 actual dyadic root isolation, A5 symmetric analytic jet, A7 and F gates remain open. No new Hecke carrier or GMP change; original attribution preserved.


## 25 November — primitive phase descent, literal CM163 packet and integer residual cast (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9CyclotomicIntegerSectorReflection20261125.md` (858d0ef359433449a305f1f13db20de8f5fc075a). Lean `Integration/Paper9CyclotomicPacketReflection.lean` at 4dd52c66eadd36c29582d5b82f83f27f40b87066 source-writes actual primitive phase rotation, pinned Mathlib expand/contract descent, finite character trace, denominator-cleared Euler residual product and original diagonal/slice sector consumers. Literal signed-hex 126 coefficient data committed at db0eb9ac260c49d749e2be42eea4566c15883137; Lean literal arrays and concrete 83/43 gates at 1d18136b84371bded22f305cde294f76db768f76. Integer polynomial residual cast, finite Euler uniqueness, norm cast and column transport source at 128291dddab6e61c0db13f8c934346a43256e698. Local scratch Python/SymPy exact replay exit 0: 3363 J parity, 5086 H/L identities, 126 N/V identities and 126 forward sector coefficient comparisons all PASS, both shifts, half-unit dominance and historical signed kappa/correction pass. Independent connector BigInt reconstruction matched local FNV64/length and committed packet read-back; no kernel or direct cyclotomic product run. Existing full source-bound entrypoint not executed; dyadic analytic enclosure not rerun. Remaining A3c actual integer J binding, executable recurrence/cast soundness and literal residual proof consumption; A4 actual dyadic root, A5 symmetric analytic jet, A7 and F gates open. All Lean terms uncompiled; no CI, benchmark or new backend. Original attribution retained.


## 25 November — canonical integer Fourier binding, concrete sector gates and actual CM root (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9EisensteinIntegerCMRoot20261125.md` (d80db1a4174d81dbe7963ce2d7b6d8ee0236ed5c). Lean canonical all-index E4/E6 coefficient source at 7ee0d13264e20a20d1ff8580d1fe1cfd4ad2bac9 consumes the original Agda-shaped shifted HasSum/limits and pinned qExpansion_coeff_unique; derivative zero/first coefficient consumers updated at 9e3115c3dca2f521d0ba60e20f1056e494ff74c9; integer discriminant/J finite quotient uniqueness at 23e68a154686dcdecb76aa762c9106df3bbe3560. Concrete signed integer residuals to actual diagonal/slice gates source-written at aa0d0cabcab4e403462cd4bfe68602b3606ea04f, using J cutoffs 3322/1722 and zero modes (1,0,1). Local exact Python/SymPy scratch: 6726 divisor comparisons, 6728 majorant bounds, 3363 shifted discriminant and 3363 J residuals PASS, 14 signed first-defect cases in both families PASS. Connector-side exact replay of actual literal packet with sharp cutoffs: 5086 H/L, 126 N/V and 126 literal comparisons PASS; binomial shift, both double roots, tangent relation and half-unit dominance pass. Original exact dyadic checker blob 8581a684cfb6ba6bfbfa45adbf6bfe01e9617258 locally hash-verified and executed at 128/160/256 bits, all PASS, original 128-bit offsets recovered. A4 direct source-written actual point and binomial-shift isolation consumer at 281748617f2350b532ba39da488aada42d3c8f34. A3c remaining executable finite recurrence/residual reflection, not another Hecke generator. A4 remaining literal shift/dominance and actual dyadic analytic reflection. A5 symmetric transverse Taylor, A7 and F gates open. All Lean source uncompiled; no kernel, CI or benchmark; full source-bound jet entrypoint not run. No GMP change or solvedness promotion. Attribution retained.


## 25 November — finite residual reflection, literal shift and direct symmetric tau jet (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9ExecutableResidualSymmetricTauJet20261125.md` (7b33bf069769001403c4ea35a734af644ee0d67a). Lean source `Paper9FiniteResidualCheck` (603fd5e) writes finite convolution/ramification and clipped Horner soundness into the existing analytic gates, `Paper9ExecutableCM163` (bc226bc) supplies candidate U/J/L/N and decidable unitOK/diagOK/sliceOK, and `Paper9CMShiftCheck` (3c41f66) writes literal integer dominance reflection and rootOfChecks. No generator-correctness or hash premise; actual Lean elaboration and boolean execution remain unpaid. Local Python/SymPy scratch passed 6646 divisor comparisons, 3323 each U/J and full diagonal sector, then timed out at 90s in the slice. Separate GMP scratch replay completed both sectors (5086 H/L, 126 N/V, 126 Horner, 52 signed probes PASS); reconstructed compact signed-hex packet SHA256 9f61b1ece8f5539106576071d82abe5b07f909a96c998495c248158446caa9e6 matches the committed literal packet. Both double zeros, tangent ratio and strict half-unit dominance PASS. Prior exact dyadic receipt retained, not rerun. `Paper9SymmetricTauJet` (2315ab9) writes reverse-chart polynomial uniqueness, actualTwoPointSymmetry on explicit universal monic-slice/separated-infinite-image premises, and direct tauJetToSigned, with local SymPy exact algebra PASS. Universal slice existence is triangular with unit pivots; cusp separation follows from distinct primitive phases and the infinity pole in ordinary mathematics, formal attachment remains. No full bivariate coefficient table, inverse j, new Hecke carrier or production GMP changes. A3c actual Lean check/elaboration, A4 analytic dyadic reflection, A5 universal slice/separation and actual symmetric pullback cubic/branch attachment, A7/F gates remain open. No kernel/CI/benchmark; full original source-bound entrypoint not run. Original attribution retained.


## 25 November — prior Machin / Taylor / infinite-j source-owner recut

See `Docs/proofs/Paper9OriginalMachinTaylorInfiniteJOwnerAudit20261125.md` (1035156abd1e507e4edb52fb19ce63802d6e3847). Do not reconstruct existing analytic machinery. Original Bishop Machin arctan interlacing/π rational windows and Lean faithful eval_machinPi_eq_real_pi, Bishop exponential ratio-half/series and faithful eval_exp_eq_real_exp, original E4/E6 degree-4/6 majorants and original scalar seriesTail/actualJSeries already exist. The older literal Agda CM half-integer checker explicitly leaves actual analytic enclosure open. New Lean `Paper9CMOriginalMachinWindow` (7eb0d74) uses original 90/91, 30/31 prefixes, pinned alternating sum bounds, exact source evaluator and original 128-bit pi/sqrt endpoints. Independent exact Fraction floor/ceil and integer-square checks PASS; closed Lean piRoundOK/sqrtRoundOK still unpaid. `Paper9UniversalMonicSlice` (60223aa, 24e775b) constructs generic slices from original normalized unit pivots and consumes sliceSectorConsumer; `Paper9SeparatedCusp` (4d5c3fe) attaches existing q-unit and exact phase asymptotics, proves intended eventualChartSeparation, separatedImageInfinite and actualSymmetry. No prior actual separated-image theorem located; infinite q-series is not itself infinite image. `Paper9OriginalCMChartWeld` (a780e72, 0cd8bf1) instantiates existing Taylor tail at actual centered j, uses exact rational original Mobius remainder, actual branchVanish and correctionFromTransverse into existing period scalar. `Paper9ActualCMRoot` (3569b6d) now consumes existing cmJReal rather than duplicate proof. Local SymPy toy 7 triangular rows, 820 primitive phase differences and exact Mobius residual PASS. All new Lean source remains UNCOMPILED, no kernel claim. Remaining A4 existing exp/Fourier bounds instantiated at original 180-term dyadic interval and actual quotient binding; A5c actual mixed cubic extraction and literal shifted coefficient reflection; A7 existing positive period consumer; A3c actual Lean decision checks and F1/F5 native acceptance separately. No new analytic foundations, no CI, no new production GMP or full literal original checker rerun.


## 25 November — reciprocal cross and ramification-indexed CM tests (current mathematical route)

The primary local extraction is now the reciprocal scalar cross, not a mixed cubic Taylor calculation. Keep the older two-slice cubic derivation as an independent check. On the actual Hecke product put x=j(tau)-K, x_+=j_1(tau)-K, x_-=j_0(tau)-K, Nr=x_+ x_-, Mr=(x-x_+)(x-x_-). Exact polynomial complements p,s satisfy x²s=Nr R and x²p=Mr(R+xT), with T defined by a finite polynomial difference, not division by x. Thus (Nr p-Mr s)x²=Nr Mr xT. The residual R disappears before differentiation. At the CM zero T(0)=S3 follows from the original fixed slice via symmetry. Retain the zero mode using 41 P2=163 S2 for CM163.

For general elliptic ramification e, use the actual disk w=(tau-tau0)/(tau-conjugate(tau0)). Stabilizer invariance implies J(w)=K+A W+B W²+..., W=w^e, where e=2 at i and e=3 at rho=(-1+i sqrt3)/2. The degree-one case e=1 is the old CM163 geometry. The reciprocal self-isogeny multipliers in W are beta=alpha^e and beta^-1, NOT alpha and alpha^-1. Put t=beta+beta^-1 and c=2-t. For a literal two-branch double-point slice, A,S2,c nonzero, exact zero and first coefficients yield P2=c S2 and

    2B/A²=(P3-2c S3)/(c S2).

Indeed N0=A², N1=t AB, M0=c A², M1=c(2+t) AB. Substitution into the normalized cross gives zero mode A^4(P2-c S2) and, after imposing that mode, first coefficient A³[A²(P3-2c S3)-2c B S2]. This is the same conditional algebra as the e=1 case, not a new theorem about arbitrary ramified Hecke singularities. If beta=1 or the slice has higher multiplicity, retain the degeneracy and do not divide.

Concrete additional exact integer cases, independently replayed locally with SymPy and the original coefficient recurrence (independent reconstruction, not exact committed script execution):

| p | K | e | forward primitive matrix | trace t | c | 2B/A² (conditional jet value) |
|---|---:|---:|---|---:|---:|---:|
| 5 | 1728 | 2 | [[2,-1],[1,2]] | -14/25 | 64/25 | 23/46656 |
| 7 | 0 | 3 | [[2,-1],[1,3]] | -286/343 | 972/343 | -23/55296 |

Both diagonal and slice have exact double zero and nonzero quadratic coefficients, and both satisfy P2=c S2. Matrix determinant, primitive entries, fixed-point identity and reciprocal unit phase passed exact checks. The reusable checker scripts/check_paper9_ramified_cm_cross.py imports the existing diagonal and slice producers; this precise committed entrypoint is source-written, not executed as a checkout here. No external numerical calibration or full p=41 residual replay this turn.

Reuse JInvariantEllipticFixedPointCompilerExact, JInvariantEllipticStandardJValuesCompilerExact and JInvariantEllipticProofRelevantKleinWeldExact, with the source proof Docs/proofs/JInvariantEllipticSpecialValuesSourceProof20261118.md. The actual original modular weights and Delta nonvanishing imply E6(i)=0, E4(rho)=0. From the original Ramanujan equations (D=q d/dq) D E6(i)=-E4(i)^2/2 and D E4(rho)=-E6(rho)/3; both nonzero by Delta nonvanishing. Therefore in the unramified tau coordinate, j-1728=E6²/Delta has leading coefficient (2 pi i)^2*432 E4(i) at order 2, and j=E4³/Delta has leading coefficient (2 pi i)^3*64 E6(rho) at order 3. Disk change multiplies these by (tau0-conjugate(tau0))^e. No use of the old j'/E4 formula at E4=0. These are classical derivations from specified inputs, not new native proofs. Actual stabilizer, source Ramanujan attachment, nonvanishing, and exact ramified chart/Taylor semantics remain to be elaborated.

Lean companion: 794c7dcf2178fe2dbb51acc901242e6e09dd2cbe repairs malformed ScalarCross source assembly; ba5e74821b871fb12989506abc99123bb2f8a85b corrects actualRawCross orientation; 6ee19bbcaed48f9f770aab427a17d741efcc41d9 source-writes Paper9DiskGeometry (local upper-half-plane chart, forward/reverse reciprocal maps, generic ramified scalar consumer). Read-back checked repaired declarations. Remaining A5: actual centered normalized analytic germs, derivatives and restSlope continuity, final instantiation with A4 finite checks. Lean/Lake/Agda absent locally; no native verification claimed.

Cross-paper placement: Paper 6 may consume the actual ramified modular geometry without physical alpha/CKM promotion. Paper 10 shares rank-two involution/norm arithmetic, not a field or representation identity. Paper 8 owns the consumer-relative signed annihilator abstraction, and Paper 3 retains the existing signed norm/factorial transfer. Paper 9 remains mathematically independent. Classical modularity, CM theory, Masser, Ramanujan, Chudnovsky, Machin, Bishop and Mathlib retain attribution; the new work is the selected residual-free organization, finite test cases and source-specific formal reconstruction. No novelty, performance or Clay claim promoted.


## 25 November — exact two-slice fibre and higher-jet boundary

See `Docs/proofs/Paper9TwoSliceIndexedResidualFibre20261125.md`. The full symmetric polynomial observation kernel is xy(x-y)^2 Q[x+y,xy], starting in degree four; a canonical section gives exact BIDI with retained residual. The existing cubic certificate is information-complete at that order. A signed quartic perturbation changes the next normalized disk coefficient C/A^3 by -lambda/[S2(t+2)] while preserving both slices. One additional transverse scalar at degree four is necessary/sufficient; floor(n/2)-1 additional distinct slope observations suffice at degree n. A reciprocal-invariant quartic equation is derived and tested, not an actual new q-source coefficient producer. Two local SymPy scripts are byte-matched to committed source; corrected literal raw-cross orientation in Lean ab9df47. The actual A5 analytic germ is still open; no change to pi's two-slice producer or promotion flags.


## 25 November — actual normalized germ and original adjacent-prefix enclosure

See `Docs/proofs/Paper9ActualDiskGermLiteralWindow20261125.md`. Lean Paper9DiskGerm at 37533f04 writes the actual Taylor pullback, three literal reciprocal branches, first derivatives and finite restSlope continuity; literalPrefixFromFiniteChecks composes A4/A5/A7 with eight finite predicates and no free analytic germ premise. Paper9LiteralWindow at 5f405bc4 writes all-index adjacent convex nesting, limit enclosure and rational cross from the period and source root/Machin bounds. Native cross-prover rational source reflection, proof elaboration and actual finite checks remain. Exact local SymPy/Fraction 9 identities, positive gap coefficients, 19 nesting controls, 20 positive prefixes and 513 rational cross/width stages PASS; executed checker byte-matched to commit 40360db. No Lean/Lake/Agda, CI, full CM163 GMP residual replay, or promotion. Higher jets remain independent.


## 26 November — literal signed integer cross and strict floor correspondence

See `Docs/proofs/Paper9LiteralSignedCrossCoordinates20261126.md`. Lean Paper9LiteralCross at fb223368 source-writes actual cutoff/scale/strict Nat.sqrt, original Machin stage/radius (first-omitted-term error and zero-stage exact bracket), raw unreduced stage, positiveView corners and eight-predicate -> forall k, RawCross k. Agda cbce74cc strengthens original floor with strict uniqueness; dba6f148 exposes actual ExpandedCross ↔ SignedCross ↔ Cross and existing native convergence consumer. Source-shaped recurrences and representation order are explicit; no inter-kernel proof transfer or all-index Agda inhabitant yet. Exact local SymPy/Fraction checker 50e009d blob 431b39b6 verified: 129 unreduced stages and 258 expanded inequalities, 1000 signed order/add controls, 1000 strict-floor uniqueness controls, 5 gap coefficients and zero-stage/equality/sign controls PASS. No Lean/Lake/Agda available, no kernel or CI, no full CM163 GMP rerun or performance promotion. Next P0: actual elaboration/finite checks and verified cross-prover proof transport or independent native all-index proof; avoid more observer abstractions or higher-jet scope expansion.


## 26 November — complete finite predicate arithmetic replay

See `Docs/proofs/Paper9EightFinitePredicateReplay20261126.md`. Local exact independent SymPy/Fraction plus GMP Euler recurrence/scatter replay completed in 14.024 s (prior scalar attempt timed out at 90 s during slice). All eight predicate specifications passed: 6646 unit residuals, 3323 independent eta coefficients, 3363+83+83 diagonal and 1723+43+43 slice residuals, strict shift/jet and original Machin/sqrt/180-term exp windows. Full 126 coefficient packet reconstructs original blob 17ed967d; all 126 literal Lean array entries also match. Corrected original expWindowOK and shiftOK namespaces and Machin denominator form. Lean 204c52d2 adds a separate uncompiled native acceptance target with eight `decide` proof terms and `#print axioms universalRawCross`. This is not kernel acceptance; Lean/Lake/Agda absent, direct download DNS unavailable, no CI. Remaining P0 actual elaboration and proof/axiom audit, verified all-index Agda proof transport or independent native proof. No 10M production timing or publication/novelty promotion.


## 26 November — native cofinal cross and exact signed phase/selector donors

See `Docs/proofs/Paper9CofinalCrossGRHPhasePNPSelector20261126.md`. Reopened master, #1529, #1546, #1533, #1548, #1549 and controlling owners. Actual positive-stage Chudnovsky/Machin windows nest by signed convex contraction, strict dyadic floor and increment/radius gap; zero stage explicitly handled. Agda 24443f51 writes actual Cross decider, negative-witness BIDI, crossZero and conditional cofinal restriction; native monotonicity and actual cofinal overlap/common-value proof remain, no all-index inhabitant claimed. SymPy/Fraction 29 edges, 512 root/window, 511 Machin and 513 overlaps, 12 phase layers, 44455 child-count pairs PASS, exact blob 2f426b74. GRH sixth/eighth signed mixed observation kernels and P vs NP strict normalized occupancy contrast equivalent to valid-child selection are scoped donors, not global endpoint solutions. Existing eight finite checks PASS retained; kernels absent. Next P0 verified native analytic common-value or cross-kernel proof, not additional reflection abstractions.


## 26 November — construct the original native Bishop Chudnovsky real

See `Docs/proofs/Paper9NativeBishopRealFactorialNesting20261126.md`. Paper9 lane only. Source-written original strict dyadic floor refinement (f134695f/b11eda74), signed adjacent/two-step nesting (27a1aa23), native factorial P/Q/T normalization (50b55302), literal reciprocal interval ordering/nesting (40ca1e9b/63339925), and actual Bishop `Real.mkℝ` midpoint construction and native doubled-index interval membership (1aa68f16). New direct BIDI: `chudnovskyReal ≃ bishopMachinPi` iff all original `ExpandedCross`; no additional Machin nesting/cofinal premises needed on this route. Actual same-real identity still OPEN; all new source terms uncompiled. Exact local byte-matched checkers 1cb9d08d and 7c78bb66: 2 polynomial identities, 3072 generic floors, 4097 root/windows, 513 factorial identities, 512 signed cross/nesting controls, 4096 window inclusions, 16384 regularity and 16512 paired order controls PASS. Existing 8/8 finite specifications receipt retained. Next P0: actual native analytic common-value attachment or verified proof transport; local kernel acceptance remains separate. No CI, external lane changes, or production performance promotion.


## 26 November — actual native factorial-period product

See `Docs/proofs/Paper9NativeFactorialPeriodProduct20261126.md`. Re-audited master 8d5b3697, #1529 d8956bb9, #1552 6d2260fb, targeted #1478/#1533/#1551/#1250 and actual Lean 204c52d2. Native seriesReal constructed from original signed defect bound and adjacency (9561c014/532fe225); canonical total root wrapper repaired with positive-index correspondence and direct consumer transport (0e99c67e/51b774ff). Synchronized chart k=41n gives actual lower corner times selected high prefix exactly 426880 times canonical floor fraction. Product-limit theorem source-writes `actualProduct : chudnovskyReal * seriesReal ≃ 426880 * sqrtReal` and positive-series cancellation in both directions (5480db8b/d191ca61). Exact remaining native mathematical obligation is `NativePeriod : bishopMachinPi * seriesReal ≃ 426880 * sqrtReal`, equivalent to all-index ExpandedCross. This is NOT proved by actualProduct. Reuse Lean actual signed CM theorem or verified proof transport; native normalized modular/ODE/CM/period reflection remains open. #1552 shell bounds/folds are donors, not a completed period proof. Local byte-matched regression d191927c: 2 symbolic identities, 259 signed defect bounds, 258 inverse budgets, 16384 regularity pairs, 257 synchronized product stages and shifted-product negative controls PASS. No native elaboration, CI, full CM replay or performance promotion. No other research lane edits.


## 26 November — native signed CM terminal and factorial Euler attachment

See the canonical roadmap Paper9PiP0MasterNativeGMPConsolidation20261123.md. Native signed first Euler flow and cleared Hecke correction imply the literal signed period cross pi*S*sqrt(163)*Y=B*F*X; then F²=X and Y²=(C+1728)/C X³ give [163(C+1728)/C](pi*S)²=B². Existing native positive-root and Machin >3 witnesses select the positive branch, with exact scalar normalization to 426880*sqrt(10005). BishopChudnovskySignedPeriodNormalizationExact (e1e8a50b) and BishopChudnovskyNativeFactorialEulerAttachmentExact (99c3f8e0/a8b24fdb/178a80ac/55e7f729) source-write the conditional native terminal and actual weighted factorial prefix split using the original signed u_n and n*u_n. The remaining inputs are native convergence/identification of those streams with the original E4 root and first Euler jet, CM j relation and signed Hecke correction on the actual normalized native forms. The exact local checker f89d0581, blob 84a4016aa854c3c02a3d7537d253c1768e9f5a11, passed 5 symbolic identities, 257 exact stages, 256 signed-prefix controls and 2 square-sign controls. Source-written, uncompiled; no native elaboration, CI, production promotion, foreign proof transport or edits to other lanes.


## 26 November — native Euler convergence and guarded selected CM disk

See canonical roadmap Paper9PiP0MasterNativeGMPConsolidation20261123.md. The original weighted defect bounds every admissible multiplier A*k<=A+B*n by |k*u_n|<=2^(-41n), hence actual H and theta H converge using original native geometric majorant. BishopChudnovskyNativeEulerLimitsExact (b4ba8fe3) source-writes actualWeightedLimit and removes both convergence premises. JInvariantBishopCM163RealSlicePeriodExact (f0cef823) proves the intended BIDI j=-640320³ iff Y²=(640320³+1728)/640320³ X³ on the same native guarded quotient, with negative Delta explicitly witnessed. JInvariantBishopCM163SelectedDiskExact (a8213fe5) constructs selected q=(-exp(-pi*sqrt(163)),0) via the existing canonical root, Machin radius and disk completion; equality to the literal complex q(tau) still needs the original phase source. The remaining native analytic producers are the actual phase/positivity, normalized CM root, H²/Euler flow and signed Hecke correction. Both checkers dad86a18 and 764364f6 were executed locally with exact integer/Fraction/SymPy; Git blob identities match. The rational q sign fixture is not the actual CM value. Source-written, uncompiled, no CI, no kernel receipt, no performance promotion or edits to other lanes.


## 26 November — E4-only native terminal and remaining same-object cut

Re-audit of #1546 and relevant master/PR owners recovered original K05 product and parity, two-point rational Cayley composition, original q carrier weld, and Lean actual hypergeometric identities/selected domain/actual signed CM period consumer. In JInvariantBishopCM163OriginalPhaseExact (a54b8362), selected q is identified with the actual original complex exponential given the two original atan-Cayley evaluations at 1/5,1/239. The classical semantic donors in Lean #104, BishopRound11OriginalArctanCayleyExact (blob 1280e6f8), remain dependent on faithful source binding; no direct Agda kernel import.

In JInvariantBishopCM163E4JetPeriodExact (7e02757e), define U=3 times the actual first E4 Euler coefficient jet, V=B U+6 A Y. Then 6Y J1=H U and pi sqrt(163) V=6 B X imply the signed period cross, reversible given H>0 and Euler flow. With H²=X and the CM cubic, reuse original positive terminal normalization. No independent E2. For the analytic producer, W=2 DY and bracket Y U-X W=X³-Y² give Dz=z Y/X and D²j=j(3X³+3Y²-YU)/(6X²); the actual analytic square identity H(z(q))²=X(q) then yields the first Euler flow by differentiation. On actual negative q=-r, r<=1/1024 already suffices for 0<X<1<Y using first Fourier term and geometric tail; this is separate from the high-precision root isolation. Detailed remaining source cut and exact local SymPy/Fraction checks are recorded in the canonical roadmap. All new Agda source uncompiled, no native kernel or benchmark promotion, no other lanes changed.
