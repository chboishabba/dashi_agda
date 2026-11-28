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


## 23 November 2026 — COMP3b exact prime-valuation carrier; performance negative control

Continuation of COMP1/COMP2/COMP3a from scripts/check_pi_cross_cancel.py,
with the same original Chudnovsky P_k=-24(2k-1)(6k-5)(6k-1),
Q_k=640320^3 k^3 and the *same* rational interval and decimal-floor
consumer. New scripts/check_pi_prime_valuation.py on this PR,
commit e45255afd9065ad23b3d4fbef28eca2478a164ce;
the locally executed script and connector readback have the identical
Git blob 8ae26be179e4664eb373ec8628136c66b96a250a.

At each leaf build exact prime-exponent Counter maps for |P| and Q.
Represent 640320^3 through triple the exponents of 640320; multiply
leaf factors 24,(2k-1),(6k-5),(6k-1) and k^3. At each internal merge
compute the intersection e_l=min(v_l(P_left),v_l(Q_right)), reconstruct
g=prod_l l^e_l and divide P_left,Q_right *before* constructing
P_left*P_right,Q_left*Q_right,T_left*Q_right+P_left*T_right.
Update the maps by the exact cross cancellation, then sum remaining
P and Q exponents. This is an exact factorization invariant of the
cross-only triple, not of T. No factorization of an arbitrary large
post-merge integer is attempted.

Local CPython execution: 64/64 prefixes (n=1..64) match cross-GCD
**identical P,Q,T integers** and reconstruct |P|,Q exactly from
the tracked prime maps. Three-run sequential medians for certified
decimal floors, with shared integer-isqrt and Fraction output:
| digits | n | cross-GCD ms | valuation-map ms | final sum of P/Q/T bits |
|---:|---:|---:|---:|---:|
| 1000 | 73 | 0.595 | 1.932 | 9030 |
| 10000 | 716 | 26.930 | 41.999 | 90233 |
| 50000 | 3573 | 534.913 | 612.077 | 451549 |

Exactly the same certified decimal strings at all three precisions,
including prior SHA256 for 50000:
c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1.
The SPF sieve construction is outside both timed modes (and adds extra
overhead to the valuation approach in end-to-end use); separate map
reconstruction assertions are also outside the timed inner loop.
Full-map bookkeeping is 14.4% *slower* than cross-GCD at 50000 digits
and produces NO smaller integer carrier. This is a matched local
negative result, not a native GMP/FLINT/MPFR or external SOTA benchmark.
The cross-GCD route remains the fastest of these two modes at 50000.

COMP3b exact predictive factoring PASS finite reference; COMP3b
*performance improvement FAILED at these scales*. Narrow next cut:
selective valuations for known small/smooth primes; compute the
residual cross-GCD or a certified residual-coprimality check to preserve
exactness, and measure the factor-map setup cost. COMP4 tree-shape and
COMP5 native/externally certified pi remain OPEN. Preserve CM M15k-p
wheel/primitive repetition, GMP selective coefficients, contour and
full 163 Masser, and COMP6 Monster/VOA full-operator versus trace
non-descent, COMP7 FRACDASH reconstruction, COMP8 consumer quotients.
No cultural-metaphor-to-mathematical-authority promotion:
Robin Wall Kimmerer / Braiding Sweetgrass is methodological attribution.
No Agda/Lean compiler or CI run; classical Chudnovsky identity is
external and Bishop same-real transport remains OPEN.


## 23 November — COMP3b selective valuations with residual GCD (local negative result)

Starting live #1529 head 8c6dd40630689b0b12f08f9a2d21f6333b89b81c.
Committed scripts/check_pi_selective_valuation.py at
5c718494b8c1e67d4523b753393607d9e519d58e.
Candidate carries exact selected-prime exponents of the Chudnovsky
P,Q leaves for all primes <=B, B in {7,31,127}. At each interior
merge, remove the intersection of P_left and Q_right selected
valuations before materializing products, and then apply residual
gcd(P_left,Q_right) to preserve FULL projective exactness.
For primes outside B, no support is discarded. Exponents of P,Q
are updated through multiplication and tracked cancellation.
This is not a claim that the output triple is more compressed than
the original cross-GCD-only representation.

Local CPython fixture (from the same algorithm source, not a
byte-identical replay of GitHub script): 448/448 exact subinterval
triples and selected-valuation invariants PASS for four prime bounds
2/7/31/127, 16 starting indices, lengths {0,1,2,3,4,8,16}.
All 12 certified decimal outputs for modes {cross-GCD, select <=7,
<=31, <=127} at digits {1000,10000,50000} agree exactly and
retain prior 50000-digit SHA256:
c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1.
Exact triple summed bit lengths remain 9030/90233/451549 at
1000/10000/50000 digits. Three sequential medians (milliseconds,
enclosure, floor certificate, string conversion; prime list
construction excluded but small):

| digits | GCD | selected <=7 | <=31 | <=127 |
|---:|---:|---:|---:|---:|
| 1000 | 0.663 | 1.109 | 1.290 | 1.501 |
| 10000 | 27.055 | 30.984 | 33.650 | 37.833 |
| 50000 | 554.043 | 574.189 | 607.291 | 620.726 |

Selective <=7 is ~3.6% slower than existing cross-GCD at 50000;
higher selected-prime bounds become slower. Approximately half the
selected <=7 merge calls still need a nontrivial residual GCD at
50000 (5325 of 10716 calls across three runs, 49.69%). 127 reduces
residual-nontrivial cases to 450/10716, but adds greater overhead.
No native GMP, memory/RSS, randomized order, external SOTA or Agda
acceptance in this packet. COMP3b exact constructive route retains
PASS, matched runtime improvement FAILED at tested scales.

Research next: quantify per-prime cancellation benefit vs bookkeeping
and fuse leaf/merge valuation operations in native code only if it can
beat GMP gcd; prioritize COMP4 trees and COMP5 production pi output
and independent established comparator. Do NOT close the CM wheel
winding/primitive necklace, projected GMP, contour or level-163 Masser,
or COMP6 Monster/VOA operator-level, COMP7 FRACDASH reconstruction,
COMP8 all-future-consumer non-descent. Robin Wall Kimmerer / Braiding
Sweetgrass is methodological attribution, not a theorem source.


## 23 November — COMP4 ordered multiplication-tree geometry

Implemented scripts/check_pi_tree_geometry.py on #1529 commit
b7f023a8a6e68b996736f123eced00d047660225,
connector readback blob 22ae2bfdf14df1ce226cca3d8c11ebfefb48a2aa.
Reuse original Chudnovsky integer P,Q,T split and exact COMP3a
pre-multiplication cross GCD: (p,q,t)*(P,Q,T) with g=gcd(p,Q)
computed as (p/g*P,q*(Q/g),t*(Q/g)+(p/g)*T).
Compare ordered (noncommutative upper triangular transport) contiguous
interval trees using midpoint, predicted q-bit-weight midpoint,
quarter and three-quarter split. Preserve ORIGINAL series order;
never permute leaves by valuation, since arbitrary reordering changes
the noncommutative split and may change term semantics.
Weight predictor cumulative sum log2(640320^3)+3log2(max(k,1)).
This is heuristic, not rigorous bit-cost optimization.

Independent local CPython harness /mnt/data/check_pi_tree_geometry.py
with same algorithms: 612/612 exact subinterval P/Q and T/Q parity;
12/12 identical certified decimal-floor strings at 1000,10000,50000
digits, same 50000 SHA256
c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1.
Three-run sequential medians (milliseconds; includes interval,
scaled exact floor and decimal string; excludes statistics collection):
| digits | midpoint | weighted | quarter | three-quarter |
|---:|---:|---:|---:|---:|
| 1000 | .634 | .647 | .673 | .615 |
| 10000 | 27.024 | 27.657 | 28.315 | 30.370 |
| 50000 | 541.004 | 564.890 | 553.486 | 537.535 |

All 50000-digit final sum of P/Q/T bit lengths = 451549 (same exact
cross-cancel output at full interval), not peak process RSS.
The initial three-quarter marginal lead is not robust:
subsequent 7-run pseudorandomized interleaved order control at
50000 digits (same exact consumer and source algorithm) medians:
midpoint 544.361 ms, weighted 545.867 ms, quarter 564.761 ms,
three-quarter 548.431 ms. Order control samples included all
floor and string work. Baseline midpoint leads by only 1.506 ms
over weighted and 4.070 ms over three-quarter; no statistically
established speedup or production promotion.
Tree max intermediate operand bits at 50000:
midpoint 112172, weighted 108684, quarter 162012,
three-quarter 154925; tree max depths 11,13,27,24 respectively.
Proxy bit-products are only illustrative, not actual GMP mul cost
or work bounds. Distinct product tree shapes cannot be treated as
independent Monster/VOA/CM equivalence proofs; same rational
consumer does not reconstruct original operator histories.
COMP4 finite arithmetic parity PASS, measured improvement OPEN/negative.
Keep midpoint COMP3a as baseline. Next test thresholded hybrid trees
only with repeated order-controlled medians, native GMP memory/RSS,
and genuine external pi software at matched certified output.
COMP5 fast pi SOTA, CM winding / necklaces / 163 Masser and COMP6-8
Monster-VOA / FRACDASH / observer-fibre remain OPEN.
No Agda or CI. Kimmerer Sweetgrass relation is cultural/methodological
attribution, not theorem authority.


## 23 November — COMP5 native GNU GMP baseline, byte-identical source acceptance

Native source committed as scripts/check_pi_native_gmp.cpp at
2df45bf7be24dda3e9fdf7ae7f8cdd4028af2d45, Git blob
b5d1d9b7555f559aa4a99225dc98c9ee96a7a9ff.
The local compiled C++ source has exactly that git hash-object, and
GitHub connector readback matches byte for byte. Compile locally:
g++ -O3 -std=c++17 scripts/check_pi_native_gmp.cpp -lgmpxx -lgmp -o /tmp/check_pi_native_gmp
Run /tmp/check_pi_native_gmp 50000 plain 5 and
/tmp/check_pi_native_gmp 50000 cross 5.
Compiler GNU g++ 14.2.0, GMP C++/libgmp.so.10 on Linux x86-64.
No GitHub CI used; no Agda proof promoted.

Uses original Chudnovsky P/Q/T midpoint tree with optional pre-product
gcd(P_left,Q_right) and GMP mpz_class/mpq_class, exact integer sqrt of
10005*2^(2*bits), alternating-tail rational endpoints and integer
floor(10^d*L)==floor(10^d*U) before decimal emission. Includes binary
splitting, interval computation, square root, rational floors and
decimal string conversion INSIDE each timed run; excludes compilation,
process startup and hashes. Source retains classical Chudnovsky
pi identity as EXTERNAL premise and original Bishop same-real
transport OPEN. Distinguish certified precision conditional on the
identity from a new standalone analytic derivation.

Exact output parity for d=1000,10000,50000:
hashes respectively
8a84d58d47f78c42a200ebfbbe7346426d4cdf4f2803d45c3590162865fcc0d2,
ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524,
c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1.
Matches prior exact CPython reference and matches native
plain/cross outputs. Native final P/Q/T summed bit sizes at
d=50000 plain 784923 versus cross 451549.

Five-run within-process native medians, milliseconds:
| digits | plain GMP | cross GMP | relative cross improvement |
|---:|---:|---:|---:|
| 1000 | .168645 | .179010 | negative |
| 10000 | 4.869130 | 4.517620 | 7.2% |
| 50000 | 49.345400 | 44.222700 | 10.4% |

Second independent invocation using identical source/toolchain
again matches ALL exact hashes; five-run medians at d=50000:
plain 51.5054 ms, cross 45.8929 ms (10.9% faster).
Single subprocess /usr/bin/time -v for cross d=50000 reported
peak RSS 3076 KiB, NOT matched plain-v-cross peak RSS and NOT
a reliable isolated algorithmic memory comparison.
Relative timings are confined to this specific environment;
do not extrapolate to native GPU or world-record scale.

No installed y-cruncher, PARI/GP or FLINT development headers were
found locally. External SOTA remains OPEN. Public source comparators:
FLINT documentation on fast constants and binary splitting
https://flintlib.org/doc/algorithms/integers/binary-splitting.html ;
FLINT arb_const_pi https://flintlib.org/doc/constants.html ;
y-cruncher official https://www.numberworld.org/y-cruncher/ .
Their published results do NOT constitute matched hardware/precision/
certification benchmarking. Next COMP5: same-environment
FLINT arb_const_pi with explicit uncached work, MPFR/AGM and y-cruncher
if available, verify identical decimal floor plus independently
documented rounding guarantees; compare threads, cold/warm cache,
peak RSS, and complete end-to-end output costs. Consider GMP low-level
mpn in-place multiplication, reduced rational construction overhead,
and streaming output for 100k-1M digits.

COMP3a cross cancellation remains valid and beneficial natively
at d=10000,50000; COMP3b selected-valuation and COMP4 alternative trees
stay negative controls. Preserve the unified COMP6 Monster/VOA
full-action non-descent, COMP7 FRACDASH reconstruction, COMP8
future-consumer sufficiency, CM winding/primitive necklaces and
level-163 Masser. Sweetgrass cultural/methodological attribution
belongs to Robin Wall Kimmerer, not mathematical theorem authority.


## 23 November — COMP5b fused native GMP integer-floor certificate

New executable scripts/check_pi_gmp_fused_certificate.cpp committed on
#1529 at 478cc4a4042910a28296a81e8cfe269adfdf95e8; source
Git blob e356a56f33126059f2b1fa0db3b6668eeb747e80.
GitHub readback and byte-identical locally compiled file verified
with git hash-object. Exact command:
g++ -O3 -std=c++17 scripts/check_pi_gmp_fused_certificate.cpp -lgmpxx -lgmp -o /tmp/check_pi_gmp_fused_certificate
/tmp/check_pi_gmp_fused_certificate 100000 5

Core identity: with Chudnovsky split (P,Q,T), next-leaf
p_n=-24(2n-1)(6n-5)(6n-1), q_n=C*n^3,
v=T/Q, v_next=(T*q_n+P*p_n*(A+B*n))/(Q*q_n).
For n>=1 compare the exact positive endpoints v,v_next to choose
S_low and S_high. With integer z=floor(2^bits sqrt(10005)),
the certified decimal interval floors are
floor(426880*z*10^d*den(S_high)/(2^bits*num(S_high)))
and
floor(426880*(z+1)*10^d*den(S_low)/(2^bits*num(S_low))).
Compute entirely with mpz integer products and floor division.
The equality of these floors is the selected consumer; ordinary
mpq normalization is unnecessary. The analytic Chudnovsky identity
and alternating-series bound remain EXTERNAL premises; this is
arithmetic certification conditional on them, not a new proof of
Bishop same-real analytic transport.

Four modes use identical midpoint tree and tail/precision:
plain-mpq, cross-gcd-mpq, plain-fused, cross-gcd-fused.
Fresh byte-identical compiled-source execution (g++ 14.2.0, GMP),
5 within-process runs per mode, includes binary split, isqrt,
enclosure, floor, decimal conversion; compilation/startup excluded.
Single-run medians in milliseconds (noise; repeat before SOTA claim):
| places | plain mpq | cross mpq | plain fused | cross fused |
|---:|---:|---:|---:|---:|
| 1000 | .179120 | .148534 | .057937 | .066490 |
| 10000 | 5.469310 | 4.533380 | 1.681440 | 1.821290 |
| 50000 | 51.446400 | 44.901200 | 17.133100 | 16.449300 |
| 100000 | 142.032000 | 116.518000 | 42.977700 | 41.341800 |

Additional 5 independent process invocations x 3 samples:
| places | median plain-mpq | cross-mpq | plain-fused | cross-fused |
|---:|---:|---:|---:|---:|
| 10000 | 5.235 | 4.526 | 1.666 | 1.730 |
| 50000 | 50.282 | 44.141 | 16.621 | 16.200 |
| 100000 | 134.599 | 116.239 | 43.679 | 42.684 |
This suggests 63% faster certificate path at 50000, 100000 than
cross-mpq, with the winning fused variant depending on precision.
Cross-cancellation still substantially reduces final triple bits:
50000 plain 784923, cross 451549;
100000 plain 1633834, cross 903197.
Do not require fully normalized (P,Q,T) when selected decimal-floor
consumer accepts a sufficient projective representation.

All four modes yielded exactly equal decimal strings and prefix
hashes for d=1000,10000,50000,100000:
1000 8a84d58d47f78c42a200ebfbbe7346426d4cdf4f2803d45c3590162865fcc0d2
10000 ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524
50000 c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1
100000 79b862cc31ceb97bb3c39d05ae74664c99f0ff7670b3e08a4b21a31ef84d7711
Independent mpmath pi decimal hashes cross-checked for d=1000
and 10000 (not a directed-rounding certified independent pi source).
No FLINT/PARI/y-cruncher installed; python-flint package unavailable
via this environment's offline package index, MPFR runtime is present
but headers unavailable. No world SOTA or external matched comparison
claimed. No Agda, Lean or CI executed.

COMP5b native direct-quotient optimization exact PASS; matched internal
GMP performance promising, not final SOTA. Next COMP5c: isolate
split versus sqrt versus exact floor/string cost and compare to
FLINT/MPFR on same machine if installed. Test 100k+ digit streaming,
RSS, cold start, varied order, GMP version/CPU and robust intervals.
Preserve COMP6 original Monster/VOA actions beyond scalar graded trace;
COMP7 FRACDASH original instruction trace; COMP8 all-future-observer
non-descent; CM winding/primitive necklaces, GMP selected coefficient,
contour, level-163 Masser. Sweetgrass/Kimmerer attribution remains
methodological and distinct from formal mathematical ownership.


## 23 November — COMP5c: stage-level GMP profiling, 1M digits, delayed cross-GCD

Live original #1529 head c0f1081b6aef87368794d7c0f61290cdf5247b3f.
New compiled exact benchmark scripts/check_pi_gmp_stage_profile.cpp, commit
ca0c67c033decbe0c262cba8a4f03e32702f86c9, blob
6a570bdcbd0c28b05aa6894dbf31e353c1908936.
Local g++ -O3 -std=c++17 -lgmpxx -lgmp -lcrypto executable was run on
the byte-identical Git blob (local git hash-object and connector readback
both equal). All modes use Chudnovsky midpoint P/Q/T, original n=d//14+2,
exact alternating next term and integer-isqrt bounds, exact integer
floor(10^d*L)==floor(10^d*U) certificate (conditional on classical identity).
GMP C++ 14.2.0 Linux; SHA-256 through OpenSSL, no CI, Agda or external SOTA.
The policy to defer external SOTA is explicit.

The instrumentation splits total work into original binary split; decimal
power 10^d; square root of 10005*2^(2bits); endpoint product assembly;
both floor divisions; decimal conversion + SHA256; and residual unaccounted
timer overhead. All are timed inside each certified invocation; compiler and
process startup are excluded. Tight bits=ceil(d*log2(10))+64 rather than
previous wide bits=4d+32. Endpoints are exactly bracketed in BOTH precision
modes; if decimal floors differ n and bits are expanded, never silently
rounding. Tight option is an engineering heuristic with 64-bit margin;
no optimality theorem, and the sqrt rational interval remains outward.

Single-process rotated-order three-run medians for wide and tight at d=100000:
| method | wide ms | tight ms | final triple summed bits |
|---|---:|---:|---:|
| plain midpoint | 42.823 | 40.410 | 1633834 |
| full cross-GCD | 41.981 | 40.234 | 903197 |

At d=500000 (three-run medians):
| method | wide ms | tight ms | final triple bits |
|---|---:|---:|---:|
| plain | 315.402 | 302.051 | 8915236 |
| full cross | 341.328 | 335.009 | 4517094 |
At d=1000000 (three-run medians):
| method | wide ms | tight ms | final triple bits |
|---|---:|---:|---:|
| plain | 701.866 | 688.932 | 18472995 |
| full cross | 798.615 | 782.499 | 9034322 |

Important change of recommendation: cross-GCD is not a universal default
with fused certification. Beyond 500k it reduces final triple size
but raises elapsed time because the GCD merge work exceeds savings in
later endpoint arithmetic. With tight 1M, plain component medians:
split 288.738ms, sqrt 39.466ms, power10 4.749ms,
endpoints 194.998ms, floor divisions 90.796ms,
serialization+SHA 71.903ms. Cross component medians:
split 451.491ms, sqrt 40.001ms, power10 4.572ms,
endpoints 138.429ms, divisions 78.962ms,
serialization+SHA 68.981ms.
Component medians should not be summed as they are selected
independently; these are stage attribution, not machine-independent cost.

Follow-up in the *committed* binary tested thresholded GCD only
when merge interval length >= L (L=2 full, 8,32,128,512,2048;
plain no GCD), all using tight bits. At d=1000000, five-run
rotated-order within-process median total milliseconds:
| schedule | ms | triple summed bits |
|---|---:|---:|
| plain | 692.117 | 18472995 |
| full cross L=2 | 761.927 | 9034322 |
| L=8 | 768.782 | 9034478 |
| L=32 | 739.913 | 9035324 |
| L=128 | 738.351 | 9039413 |
| L=512 | 749.063 | 9059579 |
| L=2048 | 754.617 | 9153108 |
None beats plain for 1M in this local 7-configuration sweep.
At d=500000 (3-run): plain 308.603, L=2 324.970, L=8
312.820, L=32 305.467, L=128 308.143, L=512 315.087,
L=2048 317.880 ms. Tiny L=32 advantage is not robustly
established; no production promotion. At d=100000 (3-run),
plain 42.177, full 43.173, L=8 40.633, L=32 40.304,
L=128 39.771, L=512 41.099, L=2048 42.061 ms.

All seven schedules give identical certified decimal output and
only one refinement attempt at 100k, 500k, 1M. Output SHA256s
(complete integer floor string with initial 3, no decimal point):
100k 79b862cc31ceb97bb3c39d05ae74664c99f0ff7670b3e08a4b21a31ef84d7711;
500k fe727f5894e072423c570402dd3948bef1f318ea957498aab06a95351e1018f9;
1M 130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18.
This is exact INTERNAL parity across independent tree representations,
NOT independently proved equality with the original Bishop pi real.
No external pi software, native GPU, matched RSS, hardware portability,
or full kernel proof acceptance.

COMP5c stage profile and 1M exact consumer PASS. 1M cross-GCD
performance gate NEGATIVE; choose plain fused midpoint as currently
best tested 1M mode, retaining earlier cross-GCD advantages at smaller
precision and its usefulness for other selected consumers. Further work:
tune integer endpoint product schedule/abbreviated quotients,
benchmark crossover across hardware, profile RSS and allocation,
precision-adaptive guard bits, and use exact ABI-valid library
comparisons only later as requested. COMP6 Monster/VOA full operator
vs character distinctions, COMP7 FRACDASH exact reconstruction,
COMP8 all-future-observer separation and CM cyclic winding/primitive
necklaces/Masser remain OPEN, not reduced by decimal hash parity.
Sweetgrass inspiration attributed to Robin Wall Kimmerer;
proof authority remains arithmetic and classical Chudnovsky owners.


## 23 November — COMP5d RH dyadic geometry transfer: exact atlas, order no-go, native timing

Source-first RH donor (master as of 23 Nov): Docs/proofs/
RHQuartic163840G2AnalyticDyadicHeisenbergP0MaxCut20261123.md,
DASHI/Analysis/RHQuartic163840DyadicTailHXIntertwinerExact.agda,
scripts/check_rh_163840_signed_dyadic_analytic_closure_20261123.py,
and RH/GRH PR #1533. RH actual signed |q|^-6 reference measure has the
exact chart u=(8/|q|)^5, signed ray s, 15-bit dyadic k=floor(32768u)
and continuous theta=32768u-k, with q=+/-8(32768/(k+theta))^(1/5).
The RH source explicitly proves only a measure-space reindexing;
XOR on dyadic cells is NOT a smooth-test/source-action symmetry and
its continuous residual cannot be discarded. This must NOT be
conflated with the Monster native H6 or actual zeta-zero action.

Concrete *different-source* Pi donor:
For each ordered Chudnovsky leaf j let positive integer cost weight w_j
be bitlength(Q_j) or bitlength(P_j)+bitlength(Q_j), with w_0=1.
Define W=sum_j w_j and cumulative u=(sum_{i<j}w_i+theta*w_j)/W,
theta in [0,1). Dyadic chart K=floor(32768u), residual rho=32768u-K.
Retaining (K,rho) and the original weighted-prefix dictionary recovers
u, original leaf j and theta EXACTLY by rational inversion. This is a
genuine reversible weighted-coordinate geometry, but is NOT the RH
q^-6 measure or its physical Gamma test, and 15bits alone is not
sufficient to reconstruct an ordered 71k-leaf producer.

Exact local Python fixture scripts/check_pi_rh_geometry_contract.py,
commit 1037a53292ab451943c50570fb0c17ed6d5da151,
source blob faab9cbffa40c4e732cce6a15b650b60bf7ae69a,
byte-identical to executed local file:
492/492 original-index and continuous-residual reconstructions PASS.
At 1M decimal places original n=71430 leaves; all 32768 dyadic cell
addresses occur, leaving 38662 duplicate address observations.
Removing residual causes a provable information-loss collision.
Negative control on actual Chudnovsky k=1,2 leaf matrices
[[P,T],[0,Q]]: forward and backward products have DIFFERENT
offdiagonal T/Q; swapping terms is not a lawful RH bit-mask
reindexing. Explicit upper commutator entry
1465872995519475397815282491520 !=0. The correct transport is
ordered concatenation and associativity, not commutativity.

Native tested scripts/check_pi_rh_geometric_split.cpp, commit
0dcc8c24d801a760138d9a8f446a2a0a2f33eb54,
blob 5b06a5ddaf51a720be240024d02cf6ed29c0feb8,
byte-identical local g++ -O3 -std=c++17 -lgmpxx -lgmp -lcrypto.
Three choices: original index midpoint, weighted midpoint of
cumulative Q_j bitlength, or cumulative P_j+Q_j bitlength. Every
split remains contiguous and retains original leaf order, and
uses plain (non-GCD) GMP fused decimal floor. This is the
algorithmic analogue of an RH weighted-uniformization followed by
dyadic subdivision, without assuming physical/source invariance.

Five-run rotating-order within-process medians with integer 10^d,
split, isqrt, integer endpoint products and floor divisions,
decimal string+SHA-256; no compiler/startup:
| decimal digits | index midpoint ms | Q-bit coordinate ms | P+Q-bit coordinate ms |
|---:|---:|---:|---:|
| 100000 | 42.597 | 41.586 | 41.697 |
| 1000000 | 695.815 | 704.073 | 702.267 |

At 1M, index midpoint is 0.9-1.2% faster even though the
geometric coordinates provide an exact invertible atlas. Shape
choice changes timing but NOT selected consumer or final size:
at 1M 18472995 summed final P/Q/T bits for all modes.
All produced prior exact SHA256:
100000 79b862cc31ceb97bb3c39d05ae74664c99f0ff7670b3e08a4b21a31ef84d7711
1000000 130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18.
Measurements include coordinate construction for both weighted
modes but NOT unnecessary weight-array construction for the plain
midpoint baseline. Earlier unadjusted control that built the
weight-array even for midpoint is superseded by this fair timing.
A 1ms difference at 100k is small and not a robust speedup claim;
no new native breakthrough established.

Conclusion: RH geometry helps define a *source-recoverable*
coordinate, a correct dyadic partition, a collision/no-descent
acceptance test and admissible ordered balancing heuristics.
It does NOT grant a beneficial C2^7 action on Chudnovsky terms,
a permutation of noncommutative triangular transport matrices,
or improved end-to-end runtime on tested 1M. Further potential
is geometric scheduling with actual measured multiplication cost
and remainder theta, avoiding repeated coordinate setup via a
streaming weight producer, and optimizing endpoint integer
products, not reusing RH physical masks. COMP5 external SOTA
remains deferred by explicit request. Original Bishop same-real,
RH actual selected W signed inequality, CM winding/necklaces/Masser,
Monster/VOA literal actions, FRACDASH reconstruction and
COMP8 all-future-consumer sufficiency remain separate OPEN.
Source attribution: classical Chudnovsky and ordered product,
RH original selected quartic/Weil source and DASHI #1533;
Robin Wall Kimmerer is cultural/methodological, not proof authority.
No Agda/Lean/CI or RH/GRH theorem claim.


## 23 November — COMP5e RH-style sufficient quotient-residual witness; SOTA pi remains P0

Keep **FASTEST INDEPENDENTLY CERTIFIED PI** the explicit P0 performance/research
objective. Per user direction, postpone FLINT/y-cruncher external comparator
execution for now, but do NOT demote the objective or infer world SOTA from
internal matched GMP. Next practical optimization must cut actual end-to-end
certification cost, retaining source identity, classical Chudnovsky premise,
ordered product and exact decimal-floor acceptance.

Donor: RH/GRH original selected-W source geometry #1533, true signed
q^-6 weighted-tail dyadic atlas with a continuous residual and exact
recovery; no unconditional bit-reindexing action on compact-smooth
tests. The correct transferable principle is **consumer-sufficient
quotient plus exact residual/boundary**, not 15-bit data magic or
leaf rearrangement. COMP5d demonstrated a reversible weighted chart
but no million-digit runtime win, and ruled out commuting term swaps.

NEW COMP5e exact theorem in ordered rational arithmetic:
For 0 <= L=N_L/D_L <= U=N_U/D_U with positive integer D_L,D_U,
let x=floor(N_L/D_L). Then
    floor(U)=x  iff  N_U < (x+1)*D_U.
Because U>=L>=x, no second integer floor division is needed.
The strict inequality preserves the exact integer boundary at U=x+1;
a weak <= would be UNSOUND. If it fails, restore usual adaptive
term-count and sqrt-precision refinement, without asserting digits.
The lower quotient x is the compressed consumer; the upper-endpoint
comparison is the retained boundary witness. This is elementary
rational order algebra, not a new RH analytic theorem.

Implemented on #1529 as
scripts/check_pi_gmp_quotient_residual.cpp at commit
0fae5e6beadec4aae7115564d90aa8d05e0df4ef,
Git blob 28f4657e5bdbfc27ebb7cc3690f6144590ba2d5e,
GitHub source readback exact. It modifies the existing COMP5c
GMP midpoint fused certificate to four order-rotated modes:
plain_two_floors, plain_one_floor, cross_two_floors, cross_one_floor;
all retain same interval endpoints, adaptive refinement, full
decimal serialization/hash and original Chudnovsky term order.
The committed source has NOT been independently fetched to the
local compiler due to connector/runtime transfer limitations.
A separately constructed, mathematically equivalent local native
GMP/openssl source /tmp/pi_residual.cpp WAS compiled with
g++ -O3 -std=c++17 -lgmpxx -lgmp -lcrypto and executed.
Do not call the committed binary byte-identically compiled.

Exact independent Python Fraction control: 10000 random ordered
positive-rational pairs, 6785 floor-crossing negative cases and
exact equality-boundary controls all PASS.
Local native mode 0 two floors, mode 1 one floor+comparison,
mode 2 exploratory explicit remainder plus comparison (slower).
Full output hashes equal for all modes:
10000 ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524
100000 79b862cc31ceb97bb3c39d05ae74664c99f0ff7670b3e08a4b21a31ef84d7711
500000 fe727f5894e072423c570402dd3948bef1f318ea957498aab06a95351e1018f9
1000000 130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18.
All remain CONDITIONAL on classical Chudnovsky identity and tail, not a new
Agda/Bishop same-real proof.

Rotating mode order five-run native medians (milliseconds, full
binary split+sqrt+products+floor(s)+serialization/hash):
| places | two floors | one floor + bound | saving |
|---:|---:|---:|---:|
| 500000 | 297.825 | 283.410 | 4.84% |
| 1000000 | 722.597 | 702.946 | 2.72% |
Independent seven-run 1000000: two 716.143 vs one 698.856 ms
(2.41% improvement). Lower-volume 10000 three-run:
1.648 vs 1.660 ms, noise/no win; 100000 three-run
42.643 vs 40.310 ms (5.47%). Tests are same-machine within-process,
not external SOTA or peak-RSS comparisons. Independent stage-med:
at 1M five-run floor/comparison stage two=94.827ms vs one=75.682ms;
serialization approximately unchanged (~71ms), so speedup is
consistent with saving second large division. A naive extra
remainder extraction costs more than it saves, negative control.

P0 next maximum-cut: combine this one-quotient certificate with
(1) original fastest GMP fused plain midpoint at >=500k, (2)
precision/size crossover selection of cross-GCD only when measured
net positive, (3) direct factor/scale sharing or smaller endpoint
integer products, (4) controlled 1M-10M arithmetic scaling and
RSS/allocations. Preserve complete decimal-floor agreement and
deliberate integer-boundary adversarial controls; never optimize
using raw hash agreement alone. COMP6 Monster/VOA actual action
versus character, COMP7 FRACDASH full source reconstruction and
COMP8 all-future-consumer/observer distinctions remain research
donors, not substitutes for verified pi speed. CM winding/primitive
necklaces/Masser still open. Original RH actual selected W and signed
zero functional admissibility/open terminal remain separate.
No CI, Lean, Agda kernel, independent external pi benchmark or
world-SOTA claim.


## 23 Nov — COMP5f codec transfer: actual compute-vs-peak-memory gate

Source-first owners: `Docs/specs/TriadicResidualMaskSignCodec.md` and
`DASHI/Codec/BalancedTritBitFibre.agda`: exact zero/support plus
conditional sign fibre; `DASHI/Codec/IndexedCubeMaskSignExact.agda`:
prefix and residual must be reconstructible; and
`DASHI/Core/ConsumerDescentMinimalObserverExact.agda`: consumer-specific
fibre-constancy and factorization. These justify retaining actual
zero, sign and original-order residual witnesses, not encoding
signed/zero matrix states as anonymous interchangeable integers.

For Chudnovsky, source semigroup states (P,Q,T) correspond to
upper-triangular [[P,T],[0,Q]]. Ordered composition has
T_new=T_left Q_right+P_left T_right; leaves and concatenation order
are noncommutative. A memory optimization may mutate the left
state only AFTER preserving its old P for addmul. New implementation
`scripts/check_pi_gmp_codec_memory.cpp`, commit
913d03d7cbe9dc7d00ed87ce02676e386893758a, GitHub blob
82027bc7acee4b4711f0ca1a2ed42dce1d60b8c5:
baseline returns expression-composed temporary P/Q/T;
in-place uses alias-safe GMP mpz_mul(T,T,Qr),
mpz_addmul(T,P,Tr), then mpz_mul(P,P,Pr),mpz_mul(Q,Q,Qr).
No loss of sign or physical zero support, no leaf permutation,
no full postmerge GCD. Both routes feed the same one-quotient
exact decimal floor and strict upper-bound consumer from COMP5e.

Local source `/mnt/data/pi_codec_memory.cpp` independently
implemented and g++ -O3 -std=c++17 -lgmpxx -lgmp -lcrypto compiled,
using the same algorithm (not byte-identical committed source
replay). Tests 10k, 100k, 500k and 1M decimal places. All
eight mode-precision combinations match existing exact SHA-256
certified floor strings:
10k ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524,
100k 79b862cc31ceb97bb3c39d05ae74664c99f0ff7670b3e08a4b21a31ef84d7711,
500k fe727f5894e072423c570402dd3948bef1f318ea957498aab06a95351e1018f9,
1M 130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18.

Fresh independent-process alternating 5-pair comparisons
(1 run per process, CPU/system noise remains, cold RSS;
time includes exact sqrt bound, split, floor, full decimal
conversion + SHA256; excludes startup/compilation):
| places | baseline median ms | in-place median ms | baseline median peak RSS KiB | in-place median peak RSS KiB |
|---:|---:|---:|---:|---:|
| 100000 | 47.571 | 45.218 | 6308 | 6356 |
| 500000 | 306.490 | 295.829 | 15684 | 15912 |
| 1000000 | 737.815 | 728.451 | 28380 | 28540 |

Positive within-sample time effects ~4.95%,3.48%,1.27%;
these do not establish a production SOTA optimization.
**NO RSS IMPROVEMENT**: in-place has respectively +48, +228, and +160 KiB higher
peak RSS in these samples (about +0.8%,+1.5%,+0.6%).
The source uses fewer large expression-temporary outputs,
but GMP allocation reuse, heap high-water mark, recursive
destruction, runtime allocator and many wider endpoint products
make peak resident memory a distinct measurement.
A preliminary three-repetition-per-process scan gave
100k baseline/in-place 45.054/42.871ms,
500k 302.905/287.380ms and 1M 724.470/722.563ms,
also all exact hashes; timing variation reinforces the need
for interleaving/order controls rather than a fixed speed claim.

P0 SOTA Pi **remains priority** even as external SOTA
comparator execution is deferred per direction. Next
cut is true live GMP limb allocation peak (not merely RSS),
memory arenas/streamed chunked leaves/partial-product lifetimes
and endpoint product scheduling; require *Pareto* compute +
memory gate and exact source-to-consumer BIDI. Avoid applying
the 3-state trit support/sign codec to arbitrary dense GMP
limbs with an unsupported compression guarantee; instead
codec gives the proper lossless-condition interface.
No GPU native, Agda/Lean or CI acceptance here; original
classical Chudnovsky identity and Bishop same-real open,
RH actual selected W and Monster action unrelated.


## 23 Nov — P0 PQT × ternary-in-binary × SWAR source-owner correction and ablation

The previous generic trit-to-GMP proposal was INCOMPLETE: original
P/Q/T already has a source-native binary-splitting contract in
`Docs/roadmaps/ConstructivePiBinarySplitMaxCut20261118.md` and
`scripts/check_pi_projective.py`; the source-native ternary
binary layout is `DASHI/Codec/TriadicPAdicCodec.agda`,
`DASHI/Codec/BalancedTritBitFibre.agda`, and
`DASHI/ComputerScience/TriadicCodecSWARPortableKernelCrossPollinationExact.agda`.
Furthermore `TriadicSupportMaskSWARExecutionExact.agda` and
`TriadicPrefixSWARExecutionExact.agda` already cite original
COMPILED eight-byte-lane uint64 C11 SWAR active-count and prefix
execution (8^8 exhaustive), while
`TriadicSignCompactionSWARExecutionExact.agda` records the
factorized 27-state dense-code execution. This is NOT equivalent to
full raw-trit encode/decode, SIMD, ROCm, or GMP limb multiplication.
The source also has `scripts/check_cm163_residue_swar.py`,
which is GMP Kronecker modular residue **lanes plus CRT**, explicitly
not fixed-word SWAR arithmetic. And Paper 9 already implements
`scripts/check_cm163_window.py` with a historical single-process
CM degree-41 57.2% RSS reduction, ~6% extra construction time,
and exact coefficient parity (different workload from pi). These
M1-M4 and CM SWAR results are REUSED, not rediscovered or promoted
to fast-pi benchmarks.

NEW specific Chudnovsky bridge:
`scripts/check_pi_pqt_ternary_swar_block.cpp`, commit
4d7a5645e450daaf7273ca76279fefbc1b458d31,
Git blob 5c15064c0cce70a885c196a51776422a93ada9d6
(GitHub readback matches committed UTF-8 source). Uses eight
byte lanes in uint64 to encode balanced trits 0/positive/negative
as 00/01/10, rejects 11; retains k as the original leaf residual.
For actual Chudnovsky leaves, k=0 has zero support, and k>=1 has
negative P (there is no positive-P leaf). Decode the signed trit
before producing exact GMP P,Q,T, then combine contiguous leaf
blocks B in {1,4,8,16} with the original noncommutative
T=T_left*Q_right+P_left*T_right. Remainder not forgotten;
output consumer is exact one-quotient-plus-strict-bound decimal floor
of the unaltered Chudnovsky rational enclosure.

Source-coded acceptance: exhaustive 3^8=6561 ternary-byte
roundtrips, explicit invalid digit-3 rejection, 32 prefix P/Q/T
identity comparisons against B=1, and full native π hashes.
A separately constructed local C++ equivalent source was
compiled with g++ -O3 -std=c++17 -lgmpxx -lgmp -lcrypto.
Local full-run PASS: for each B=1/4/8/16, d=100k,500k,1M,
all 12 hashes exactly match existing original GMP certificates:
100k 79b862cc31ceb97bb3c39d05ae74664c99f0ff7670b3e08a4b21a31ef84d7711,
500k fe727f5894e072423c570402dd3948bef1f318ea957498aab06a95351e1018f9,
1M 130203eb055a962b8441af76c22b75627ec18c672a485904e567f59251e8ee18.
The committed C++ text has NOT been compiled byte-for-byte
(only readback); do not claim compiler/kernel proof for it.

5-process rotating-order single-invocation 1M runtime medians
milliseconds, source-equivalent local program:
B=1 729.822; B=4 750.199; B=8 718.826; B=16 724.350.
Run ranges overlap strongly (e.g. B=8 from 691 to 765ms);
no robust native SOTA speedup. At 100k:
B=1 44.103; B=4 45.474; B=8 46.223; B=16 48.345.
Earlier independent shell launches with 3 repetitions/process:
at 1M B=1 733.002, B=4 687.039, B=8 748.209,
B=16 730.296 milliseconds; inconsistent apparent winner,
hence NO promotion. Fresh shell isolated peak RSS at 1M
B=1 29536 KiB, B=4 30248, B=8 30204, B=16 29740
(specific run only). A Python-parent subprocess RSS observation
was contaminated by fork-inherited high water and is NOT admitted
as a comparative peak memory receipt. Nothing proves less memory.

Crucial limitation: this benchmark uses packed byte lanes for
ternary sign/support **decoding**, not lane-parallel arithmetic
on P/Q/T and NOT a measured SWAR multiplication kernel.
At n=71430, largest leaf Q=C*k^3 is already 107 bits,
exceeding a 64-bit scalar lane; GMP multi-limb multiplication
remains essential. The full ternary alphabet includes +1
for codec regression, but actual Chudnovsky P has only
0/negative sign states. The codec cannot manufacture useful
low-entropy structure in dense high-precision limbs.

Prioritize P0 fastest independently certified π:
(1) actual signed P/Q/T projects and quotient-residual consumer;
(2) *genuine* SWAR only on independent small metadata or modular
residue subproblems with exact CRT reconstruction and full
setup/serialization costs, not magical packed GMP multiplication;
(3) identify compute/RSS Pareto on real limb allocation,
endpoint scheduling, and producer-local re-use; (4) independent
cold/hot 1M+ tests. External SOTA comparison execution remains
deferred, its P0 end objective intact.
Do not conflate CM p41 RSS improvement or source SWAR
8^8 acceptance with a π performance gain. Do not claim
RH actual selected W, Monster group action, formal Bishop pi
same-real, Agda/Lean kernel or GPU acceptance in this packet.
