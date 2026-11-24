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
