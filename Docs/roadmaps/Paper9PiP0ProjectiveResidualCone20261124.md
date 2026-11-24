# Paper 9 P0 — COMP5k/l projective signed-residual geometry

24 November 2026. **Research/design and implementation only. Testing and
benchmarking explicitly deferred by user.** Do not treat read-back of a GitHub
source file as compile, exact-source acceptance, formal proof or measured
performance. Original algorithmic authority: Chudnovsky brothers' classical
hypergeometric π series and binary splitting. DASHI source owner: original
Paper 9 / constructive constants PR #1529, master-native GMP PR #1546.
These are exact source-preserving *candidate rearrangements*, not independent
analytic derivations of π or claims of novelty over classical binary-splitting
arithmetic.

## Latest-PR source reconciliation and legitimate donors

Checked the current repository PR listing on 24 November. Relevant newest
owners: [#1550](https://github.com/chboishabba/dashi_agda/pull/1550)
(X369 deterministic input-indexed future-consumer descent, observer and
transition stability); [#1549](https://github.com/chboishabba/dashi_agda/pull/1549)
(costed shared-computation geometric DAGs and source-labelled observer
refinement); [#1548](https://github.com/chboishabba/dashi_agda/pull/1548)
(semantic polynomial coverage versus actual cost); [#1547](https://github.com/chboishabba/dashi_agda/pull/1547)
(geometry-integrated source and positive-energy acceptance); original
[#1529](https://github.com/chboishabba/dashi_agda/pull/1529)
(P/Q/T Chudnovsky baseline, split/cross-GCD and analytic boundary).
Only **the generic source-consumer / exact algebraic sharing principles**
transfer. X369 recurrent payloads, P≠NP/SAT gates, F8 energy geometry and
Langlands ramification are NOT mathematical premises of a π speedup.

Relevant existing master owners (unchanged):
- \`DASHI/ComputerScience/FibreProgramComplexityExact.agda\`: execution-fibre
  sum and peak cost, not a latency oracle.
- \`DASHI/Core/EfficientRecoverableQuotientExact.agda\`: construction,
  compact receipt and reopening cost separation.
- \`DASHI/ComputerScience/StreamingResidencyComplexityErrorDNABidiExact.agda\`:
  same-consumer residency transformations.
- \`DASHI/Core/QueryFactorisationSufficiency.agda\`: appropriate
  consumer-specific sufficiency rather than arbitrary lossy compression.
- Paper 9 §10: original arithmetic bit-cost + GMP/verification ledger.

## G1 — exact 2×2 triangular projective geometry of original P/Q/T

For a binary-split interval use the original integer triple
\((P,Q,T)\) and its upper-triangular matrix

\[
  M(P,Q,T)=\begin{pmatrix}P&T\\0&Q\end{pmatrix}.
\]

The original, ordered binary merge is precisely matrix
multiplication:

\[
  M(P_L,Q_L,T_L)\,M(P_R,Q_R,T_R)
  =
  M(P_L P_R,\;Q_L Q_R,\;T_L Q_R+P_L T_R).
\]

This is an exact associative Borel-monoid carrier, not a different
definition of the Chudnovsky sum. The *present* series observer is
\(S=T/Q\). The \(P\) fibre matters only for subsequent extension;
discarding it before the last leaf would break future-consumer
adequacy. At terminal \(n\), the next leaf is

\[
p_n=-24(2n-1)(6n-5)(6n-1), \quad
q_n=640320^3 n^3,\quad a_n=13591409+545140134n.
\]

Hence for \((P_n,Q_n,T_n)=M(0,n)\) and its next term,

\[
  S_{n+1}=\frac{T_n q_n+P_n p_n a_n}{Q_n q_n},
  \qquad
  S_{n+1}-S_n
    =\frac{\delta_n}{Q_n q_n},
  \qquad
  \delta_n=P_n p_n a_n.
\]

Original leaves \(p_j<0\) for every \(j\ge1\), while \(p_0=1\),
so \(\operatorname{sgn} P_n=(-1)^{n-1}\) for \(n\ge2\).
The remaining factors \(q_n,Q_n,a_n\) are strictly positive.
Therefore \(\operatorname{sgn}\delta_n=(-1)^n\) exactly.
The **source sign fixes the order** of the adjacent endpoints.
A large cross-product comparison
\`num2*den1 < num1*den2\` is unnecessary.

## COMP5k — source-parity endpoint sorting (implementation committed, UNTESTED)

\`scripts/check_pi_p0_signed_tail_cone.cpp\` derives from the exact
original COMP5j source (same lower floor, upper comparison, signed
tail and sqrt enclosure). It snapshots the original \(P_n\) sign
**before moving and releasing P/Q/T**; checks source leaf sign,
positive \(q_n\) and parity. For even \(n\) it retains
\(S_n<S_{n+1}\); for odd \(n\) it swaps the two quotient-endpoint
objects using GMP's allocated-value swapping. There is no
round-up-to-even overhead, no large cross-products, and no change
to the original retry schedule or decimal certificate.

No performance or actual memory saving is asserted: removing two
large products suggests a gain, but memory allocators, caches
and GMP multiplication cost require later measurement.
The signed orientation proof is exact conditional on the
original Chudnovsky P/Q/T leaf/merge semantics and \(n\ge2\).
No entire analytic Chudnovsky sum is proved here.

## G2 — quotient/remainder witness eliminates the second root product

A stronger specialized **even n** terminal section is available.
Write \(P=P_n,Q=Q_n,T=T_n,q=q_n\) and
\(\delta=P p_n a_n>0\). Let \(B=Tq+\delta>0\) and \(C=Qq>0\).
Let \(R=\lfloor\sqrt{10005\cdot2^{2b}}\rfloor\),
\(F=426880\cdot5^d\), and \(k=b-d\ge0\).
The original, exact binary-scaled interval certificate is

\[
x=\left\lfloor\frac{FRC}{2^k B}\right\rfloor,
\qquad
F(R+1)Q<(x+1)\,2^kT.
\]

Perform the exact Euclidean factorizations

\[
  FRC=2^k u+\ell,\quad 0\le\ell<2^k,
  \qquad
  u=xB+\rho,\quad0\le\rho<B .
\]

The first identity computes the **identical** lower decimal
quotient \(x\) as COMP5j, not an approximation.
Multiply the strict upper condition by positive \(q\) and
substitute \(B=Tq+\delta\):

\[
\begin{aligned}
F(R+1)C
 &=FRC+FC\\
 &=2^k\{x(Tq+\delta)+\rho\}+\ell+FC.
\end{aligned}
\]

The strict upper condition therefore holds **if and only if**

\[
\boxed{\,x\delta+\rho+
  \left\lfloor\frac{\ell+FC}{2^k}\right\rfloor
  < Tq\, .}
\]

No \((R+1)FQ\) multiplication is needed by this upper witness.
The surviving consumer reads only \(x,\rho,\ell,\delta,C,Tq,F,k\),
plus original positivity and source/receipt IDs. The
independent signed tail \(\delta\) is a **necessary** extra
refinement: \(x\) alone does not determine every upper-bound
admission decision. This is the concrete
FibreProgramComplexity/QueryFactorisation sufficiency point,
analogous to (but not inferred from) #1550's future-state
observer analysis. Both formulations have the same acceptance
predicate, *not* just the same decimal output on sample inputs.

## COMP5l — quotient/residual upper witness (implementation committed, UNTESTED)

\`scripts/check_pi_p0_residual_witness.cpp\` is a distinct
candidate, not the production default. It:
1. rounds the cutoff **up to even** and requires the exact
   original \(P_n<0,p_n<0,q_n>0,\delta>0\) source cone;
2. retains the same original binary-split \(P,Q,T\), original
   integer sqrt enclosure and \(5^d\) factorization;
3. computes \(u,\ell\) by \`mpz_fdiv_qr_2exp\), then \(x,\rho\)
   by \`mpz_fdiv_qr\), preserving *both* exact Euclidean residuals;
4. releases the large original lower packed integer and
   unused series-carrier observations;
5. computes the upper correction
   \(\lfloor(\ell+FC)/2^k\rfloor\), checks the boxed
   strict inequality, and emits the unchanged integer \(x\).
6. follows the original widen-\(n,b\) retry semantics, keeping
   \(n\) even.

**Important trade-off:** \(\ell\) has up to \(k\) bits and
\(\rho\) up to \(\operatorname{bitlength}B\); retaining them and
\(\delta,C,Tq\) may exceed the memory removed with the second
root multiplication. There is no benchmark or complexity
improvement claim. GMP division with remainder may cost more
than a quotient-only division. This candidate is valuable
because the exact upper witness no longer depends on \(R\)
once the lower quotient/remainders have been produced.

## G3 — next geometric candidates, NOT implemented or promoted

- **Root-output alignment:** compute an outward radical enclosure
  for \(426880\sqrt{10005}\,10^d\) directly rather than
  building \(\sqrt{10005}\,2^b\), multiplying by \(5^d\)
  and shifting. Requires costed dense radicand production and
  precision adaptation; fewer visible algebraic factors
  need not mean faster \`mpz_sqrt\`. Do not assume the
  one-unit integer enclosure will always certify a decimal floor.
- **Blockwise projective normalization:** because the consumer
  reads \(T/Q\) and signed next-term residual, a shared
  nonzero factor can be canceled from \(P,Q,T\) only with a
  source-proved adequate future extension. Prior COMP3/5
  found cross-GCD not reliably faster at 1M, so a global
  \`gcd(P,Q,T)\` pass is not justified as an optimization.
- **Width-informed multiplication schedule:** use actual operand
  widths and shared scratch lifetime to choose a balanced
  product-tree plan. The upper-triangular monoid ensures
  reparenthesization is exact; changing leaf order is NOT
  generally valid and retains sign/residual obligations.
  Schedule admissibility and memory performance are separate.
- **Adaptive proof width:** make square-root guard bits and
  series cutoff depend on the exact inequality slack rather
  than a fixed guessed geometric ratio. Must preserve strict
  endpoints and guarantee eventual success; no speed result
  is inferred.

## Current P0 gate and testing deferral

The original COMP5j and prior COMP5g/h/i candidates, their
output hashes and receipts remain unchanged. COMP5k/5l
are **source-committed research prototypes only**. No
local C++ compilation, no SymPy or Python execution,
no GitHub CI, no new receipt, no Agda/Lean kernel run,
no external SOTA comparator and no new memory/time figure
were requested or performed for this tranche.
GitHub readback verifies file contents only.

Future acceptance is deferred: compile exact branch source,
check signed odd/even endpoint ordering against the original
cross-products; compare each bound and exact floor for small
and large d; distinguish even-cutoff leaf overhead, division
remainder cost, GMP live heap, RSS, upper product widths and
serialization. Only then add candidates to the performance
default/Pareto runner or promote a faster path. The
original Bishop same-real proof and analytic-source authority
remain distinct OPEN obligations.


## 24 November — COMP5m/n: output-aligned radical and width-directed ordered evaluation

User instruction remains **defer testing**. Code, mathematical source
derivations, PR reconciliation and GitHub byte readbacks only.
No new timing, performance, integer oracle, compilation, CI,
formal kernel or numerical acceptance evidence is claimed.

### G4 / COMP5m — directly output-aligned integer radical

New **UNTESTED** source:
\`scripts/check_pi_p0_output_aligned_root.cpp\` (derived from
COMP5k so odd/even signed-tail ordering survives unchanged).

Let \(\alpha_d=426880\,10^d\sqrt{10005}>0\). For a *separate*
adjustable guard-bit index \(g\ge 0\), define

\[
H_{d,g}=\left\lfloor 2^g\alpha_d\right\rfloor,\qquad
H_{d,g}^2\le
10005\,(426880\,10^d)^2\,2^{2g}<(H_{d,g}+1)^2 .
\]

The second strict inequality holds simply from
\(\lfloor\sqrt N\rfloor=H\); it does not require an unverified
numerical sqrt approximation.

After the original signed-tail ordering, write both positive
source-adjacent series endpoints as

\[
0<S_{\mathrm{lo}}=\frac{N_\mathrm{lo}}{D_\mathrm{lo}}
\le S=\sum_{j=0}^{\infty}(-1)^j
\frac{(6j)!\,(13591409+545140134j)}
{(3j)!\,(j!)^3\,640320^{3j}}
\le S_{\mathrm{hi}}=\frac{N_\mathrm{hi}}{D_\mathrm{hi}} .
\]

The middle \(S\) is the original infinite Chudnovsky
series, with its alternating sign and original positive
normalization. The infinite-series identity and valid analytic
tail enclosure are still EXTERNAL mathematical premises.
The exact output-scaled π interval is

\[
\frac{H_{d,g}D_\mathrm{hi}}{2^g N_\mathrm{hi}}
\le 10^d\pi <
\frac{(H_{d,g}+1)D_\mathrm{lo}}{2^g N_\mathrm{lo}}.
\]

Compute \(x=\lfloor H_{d,g}D_\mathrm{hi}/
(2^g N_\mathrm{hi})\rfloor\). The exact admission condition is

\[
(H_{d,g}+1)D_\mathrm{lo}
<(x+1)\,2^g N_\mathrm{lo},
\]
equivalently (for nonnegative integers),
\[
\left\lfloor
 \frac{(H_{d,g}+1)D_\mathrm{lo}}{2^g}
\right\rfloor
<(x+1)N_\mathrm{lo}.
\]

No multiplication of separately approximated \(\sqrt{10005}\)
with the \(5^d\) decimal factor is needed *after* the square
root. The radical producer instead computes the large
integer radicand by a \(d\)-digit prefactor square
and a constant multiplication, with a GMP in-place
multiplication sequence and immediate scope release.
This **may be slower or use more peak memory** than a cheap
bit-shifted radicand followed by \(5^d\) multiplication.
The root guard \(g\) starts at 64 and increases if the
strict certificate is inconclusive; the series cutoff
\(n\) also increases. Two monotone positive enclosures are
refined rather than relying on a one-unit output interval.

**Important source equivalence boundary:** the COMP5m
finite interval is a *different outward enclosure* of the
same \(10^d\pi\) target than COMP5j's dyadically scaled
\(\sqrt{10005}\) interval; the two finite endpoints need
NOT be equal. A successful certificate proves the SAME
integer output consumer, conditional on the original
Chudnovsky identity and alternating-series tail. No
stronger equality of the full observation fibres is claimed.
If the π floor is ambiguous, the algorithm must NOT
accept, and it must refine guard/series indices.
The code has explicit unsigned-index and mp_bitcnt_t
overflow fail-closed checks, but all runtime and general
termination/resource properties require later acceptance.

### G5 / COMP5n — width-informed evaluation of *the same* matrix product

New **UNTESTED** source:
\`scripts/check_pi_p0_width_scheduled_pqt.cpp\` (derived from
the COMP5j production-performance candidate, with the same
finite sqrt and same signed/unsigned boundary as that owner).

For any original interval \([a,b)\), \(q_0=1\) and for
\(j\ge1\), \(q_j=640320^3j^3\). Therefore for
\(u=\max(a,1)\), \(b>u\), the exact logarithmic Q-width is

\[
\log_2 Q(a,b)
=3(b-u)\log_2 640320
+3\log_2\left(\frac{(b-1)!}{(u-1)!}\right).
\]

The C++ schedule estimates this using
\(\lgamma(b)-\lgamma(u)\), including finite floating
approximation; **only the choice of subtree evaluation order**
depends on it. It evaluates the child with the larger
estimated Q-width first, then retains that child while
computing the smaller child. At the merge it ALWAYS
computes the source-ordered

\[
  M(a,m)\,M(m,b),\quad
  (P,Q,T)=(P_LP_R,\;Q_LQ_R,\;
             T_LQ_R+P_LT_R).
\]

So no leaf permutations, parenthesized algebra changes,
reversed matrix multiplication, source-provenance loss or
change to the consumer are proposed. Only the *execution
path* through the source carrier is altered.
The upper-triangular matrix product is generally
noncommutative: \(M_RM_L\neq M_LM_R\).
This candidate uses a simple Q-width proxy, NOT a
proven optimal Sethi–Ullman schedule. Predicted Q-width
alone does not model actual scratch, live GMP heap,
source T-growth, CPU overhead or hardware cache.
It could increase latency or memory.

For a genuine peak-memory optimality claim one would
need an exact cost model for subtree output storage and
unretained execution peaks. If child A has output
residency \(s_A\), intrinsic execution peak \(p_A\), and
B has \(s_B,p_B\), then ignoring shared merge scratch:

\[
\begin{aligned}
\operatorname{peak}(A\!\to\!B)
 &=\max(p_A,\;s_A+p_B),\\
\operatorname{peak}(B\!\to\!A)
 &=\max(p_B,\;s_B+p_A).
\end{aligned}
\]

The full merge adds a peak common to either child
evaluation order. The current width-only scheduling
does not certify that \(s_i,p_i\) are accurately bounded
or that its choice minimizes these expressions.
This gives a more principled *future* DP/Pareto gate
than deciding from precision alone.

### Producer–consumer boundaries, status and next maximum cut

- G4 uses original exact \(\operatorname{isqrt}\) on a
  new output-aligned radicand; G5 only changes the
  original ordered product's execution path.
- Both retain P, Q, T leaf signs, zero/residual and
  original marked analytic-source conditions. The
  indexed guard \(g\) and split indices \([a,m),[m,b)\)
  remain distinct: changing an output precision guard
  is NOT the same as changing series terms or
  reparenthesizing P/Q/T.
- The current six-variant GMP Pareto runner is unchanged;
  COMP5k/l/m/n are independent research files and
  have no new verified output/performance receipts.
- Original owners: Paper 9 §10, original #1529,
  source-preserving GMP #1546, consumer-indexed
  FibreProgramComplexityExact, recoverable quotients and
  residency constraints. Newer #1550 provides a
  useful reminder of all-future consumer adequacy but
  does NOT prove any π theorem.
- When testing deferral is lifted: compare output
  enclosures **against the same π target**, not require
  equal finite source intervals; verify both source
  parities, strict lower/upper inequalities and guards;
  profile radicand multiplication, sqrt width, retained
  limbs and peak RSS separately; distinguish
  width-prediction cost from any memory reduction; run
  genuine exact-source acceptance and independently
  certified external SOTA comparison only on request.
- Current mathematical endpoints still open:
  the Bishop same-real analytic source certificate
  and a formal kernel-level execution/cost theorem.


### G6 / COMP5o — root-free exact signed-square verifier

New **UNTESTED** verifier interface:
\`scripts/pi_p0_signed_square_verifier.hpp\`.

This is a *consumer-side* geometric alternative, not an
unjustified faster π producer. It accepts a candidate
nonnegative output integer \(x\) and an
**independently source-authenticated** original P/Q/T
triple at cutoff \(n\ge2\), derives the source signed
next-term residual, and orders both positive partial
sums as in COMP5k. Let

\[
0 < S_{\rm lo}=N_{\rm lo}/D_{\rm lo}
\le S \le S_{\rm hi}=N_{\rm hi}/D_{\rm hi},
\quad F=426880\,10^d.
\]

To prove the same integer output consumer
\(x=\lfloor 10^d\pi\rfloor\), it is enough to establish

\[
x S_{\rm hi}\le F\sqrt{10005}
\quad\hbox{and}\quad
F\sqrt{10005}<(x+1)S_{\rm lo}.
\]

All quantities are nonnegative, so the inequalities
are EXACTLY equivalent to two entirely integer
*square-slack receipts*:

\[
\boxed{
L=10005(FD_{\rm hi})^2-(xN_{\rm hi})^2\ge0,}
\qquad
\boxed{
U=((x+1)N_{\rm lo})^2-10005(FD_{\rm lo})^2>0 .}
\]

The new C++ header constructs those integer residuals
and declares acceptance iff the original signed source
cone and both slack signs hold. **No integer square-root
or floating evaluation occurs in the verifier.** The
original alternating tail and Chudnovsky π identity
remain external analytic premises, so the signed
bound alone does not prove the infinite-series source.
Further, arbitrary caller-supplied P/Q/T integers can
be forged while still passing sign checks: a verifier
must separately recompute the exact ordered producer
or verify an original source-identified P/Q/T receipt.
The header explicitly documents this trust boundary.

This is a promising **independent verifier separation**
of candidate construction versus exact receipt checking,
reusing \`EfficientRecoverableQuotientExact.agda\`.
It may be SLOWER and use MORE memory than the
production radical/division certificate, since it
forms up to four large squares. Do not infer a π SOTA
speedup from root elimination at the verifier only.

Acceptance continues to be deferred: establish
caller-source authenticity, compute signed full-size
slacks, prove equivalence against the original
\(x\le10^d\pi<x+1\) consumer, measure receipt
construction and reopening costs independently, and
only then decide whether this belongs in a fast
production or independent-certification path.
No compilation, tests, CI or kernel claims.


## 24 November — COMP5p/q/r: source valuation, projective leaf gauge and exact local content (testing deferred)

### Live cross-PR inspiration, mathematically scoped

Inspect original current work, not PR title alone:

- [P vs NP #1548](https://github.com/chboishabba/dashi_agda/pull/1548),
  G60–G64 actual source-supported multilinear producer, signed
  coefficient valuations and sparse support matching (inspected
  24 Nov at head `7dcee418032a9a6fc7ca32eafe40033253ac925e`).
  G61 stresses **content removal before expansion** and warns
  that apparent bit savings can cost more total generation.
- [Ramified Langlands/GCT #1549](https://github.com/chboishabba/dashi_agda/pull/1549),
  R85–R91 weighted source consumer and zero-mode separation,
  R92–R96 valuation/creation-precision/carry reconciliation
  (inspected 24 Nov at head `73bf0b2a23a3a1918807448ddf8f1a3b6bfb5412`).
  Its **relative, indexed source** requirement is especially relevant
  to an exact projective P/Q/T gauge that is mathematically
  equivalent but not the *literal raw* original integers.
- Existing #1546 formal owners, signed COMP5k and residual
  COMP5l remain the actual π owners; no Langlands conjecture,
  hard SAT instance, Fourier rank, mixed-characteristic ring
  or P-vs-NP separation is imported as a π theorem.

This is exact **integer common-content** arithmetic, not
finite-coefficient-precision truncation. There is therefore no
canonical section/carry defect in these three constructions.
If any future approximate/modular version is introduced, R96
requires separately charging its lift defect and signed residual.

### G7 — the original P/Q/T leaf admits a maximal uniform projective 24 gauge

Original source at nonzero index j:

\[
p_j=-24f_j,\quad
f_j=(2j-1)(6j-5)(6j-1),\quad
q_j=640320^3j^3,\quad
t_j=(A+Bj)p_j .
\]

Since \(640320=24\cdot26680\), 24 divides
\(p_j,q_j,t_j\) at every \(j\ge1\). The first source
leaf \(j=0\) is never scaled:
\(p_0=q_0=1,t_0=A\).
Define the normalized positive-index leaf matrix
\(M'_j=M_j/24\), explicitly by

\[
p'_j=-f_j,\quad
q'_j=(640320^3/24)j^3,\quad
t'_j=(A+Bj)p'_j.
\]

Let
\(e(a,b)=\#([a,b)\cap\{1,2,\ldots\})\).
For any original ordered interval, by bilinearity of
upper-triangular matrix multiplication,

\[
\boxed{M'(a,b)=24^{-e(a,b)}M(a,b)}
\]

with the **same left-right product order** and exact signs.
For the original terminal \([0,n)\), \(e=n-1\).
Consequently both present and any future original
right-multiplied rational observations \(T/Q\),
and the signed next-term increment
\(Pp_n(A+Bn)/(Qq_n)\), are scale invariant.
The output-aligned COMP5m and COMP5j certificate
quotients and both exact strict inequalities are
homogeneous in the P/Q/T source triple.

It is the **maximal guaranteed uniform integer
source-leaf factor** because
\(|p_1|=120, |p_2|=5544\) and
\(\gcd(120,5544)=24\). This does *not*
mean each individual leaf has no further common
content, or that this normalization minimizes
actual runtime/total storage.

A source-authenticated raw triple cannot be
replaced with the normalized triple while
pretending its P,Q,T values are bytewise equal.
The source witness must record the scale recipe
or leaf-gauge index; original raw values may
be reconstructed by multiplying by \(24^{e(a,b)}\).
For a homogeneous floor/signed inequality
consumer, this expensive reopening is
**not mathematically necessary**. For an
independent verifier that requires original
raw P/Q/T coordinates, identity replay/reopening
remains a separately costed obligation.

### COMP5p — direct 24-normalized leaves, not post-hoc GCD (UNTESTED)

New C++ `scripts/check_pi_p0_projective24_leaf.cpp`:
for each nonzero source leaf constructs \(-f_j\)
and \((640320^3/24)j^3\) **directly**,
with the original terminal signed-tail parity,
dyadic root, one-division upper-bound certificate,
and original n-retry schedule of COMP5k.
Its FIBRE receipt declares
`source_gauge=projective_leaf_24` and
`source_scale_24_exponent=n-1`.
For interval \([0,n)\), the original nonzero terminal P/Q/T
entries are exactly \(24^{n-1}\) times their normalized
counterparts;
the exact logarithmic reduction is
\((n-1)\log_2 24\) in each nonzero terminal
component's positive bit-height, up to integer
bit-length rounding. This **does not**
measure memory or GMP multiplication speed.
No generic GCD is computed; source term factors
are reduced before multiplication.

### G8 — fixed-prime support gives exact per-leaf local content without GMP GCD

The original scale 24 is uniform but leaves more
common factors on selected indices.
The exact prime factorization is

\[
640320=2^6\cdot3\cdot5\cdot23\cdot29.
\]

Write \(p'_j=-f_j\),
\(q'_j=(640320^3/24)j^3\).
For every prime \(\ell\) outside the fixed set
\(S=\{2,3,5,23,29\}\), if
\(\ell\mid q'_j\) then
\(\ell\mid j\), whereas

\[
\gcd(j,2j-1)=1,\quad
\gcd(j,6j-1)=1,\quad
\gcd(j,6j-5)=\gcd(j,5).
\]

Therefore \(\ell\nmid f_j\).
As \(f_j\) is always odd, it also has
no factor of 2. Thus

\[
h_j=\gcd(|p'_j|,q'_j)
=\prod_{\ell\in\{3,5,23,29\}}
 \ell^{\min(\nu_\ell(f_j),\nu_\ell(q'_j))}.
\]

The exact exponent is computed from original
source linear-factor valuations:

\[
\nu_\ell(f_j)
=\nu_\ell(2j-1)+\nu_\ell(6j-5)+\nu_\ell(6j-1),
\quad
\nu_\ell(q'_j)
=c_\ell+3\nu_\ell(j),
\]
where \(c_3=2\) and
\(c_5=c_{23}=c_{29}=3\).
This is exact finite-prime source arithmetic;
there are no missing large-prime divisors
of the local \(\gcd\). No generic GMP
`mpz_gcd` need be invoked.

The resulting primitive positive-index leaf is
\((p'_j/h_j,q'_j/h_j,t'_j/h_j)\), and its
original-source scale is
\(g_j=24h_j\).
Define \(G(a,b)=\prod_{j\in[a,b),j>0}g_j\).
Then exactly

\[
\boxed{
M^{\rm local}(a,b)=G(a,b)^{-1}M(a,b).
}
\]

Unlike the uniform 24 gauge, \(G(a,b)\)
is index-dependent; a source receipt must
store its deterministic **recipe and original
index interval**, not merely the exponent n-1.
No expanded \(G(a,b)\) is necessary for
the original homogeneous series/π consumer.
The signed tail residual is scaled by the
same nonzero positive G, so no sign information
is lost. Genuine zero or orientation sign
remains distinct from a zero observed after
modular reduction.

### COMP5q/r — two independent consumers of this geometry

- **COMP5q**, `scripts/check_pi_p0_projective24_residual_witness.cpp`:
  use guaranteed projective 24 source leaves but
  terminal COMP5l exact quotient/remainder
  signed residual witness, instead of the COMP5k
  upper radical multiplication. Even cutoff and
  both remainder fibres are preserved.
- **COMP5r**, `scripts/check_pi_p0_indexed_prime_content.cpp`:
  use the fixed S-supported exact local \(h_j\)
  valuation recipe to divide the *already
  24-normalized* source leaf by \(h_j\).
  Index arithmetic is computed over widened
  64-bit small linear factors, with two
  source-justified exact GMP divisions by
  \(h_j\). No general GMP GCD call is present.
  The original entire-tree scale recipe
  \(\prod 24h_j\) is metadata for source
  reopening and never falsely asserted to
  equal \(24^{n-1}\).

Potential performance trade-offs are substantial:
per-leaf \(\nu_\ell\) divisions, extra
`mpz_divexact` work and scale-metadata
processing must be charged. Source-normalized
leaves reduce downstream big-integer operand
widths, but neither overall operation count
nor speed or peak RSS is proved to improve.
The fixed-prime formula does NOT imply that a
universal SAT problem or a Langlands local
correspondence can be evaluated with this method.

### Cost ledger, future proof obligations and exact boundaries

The relevant three costs are distinct:
(1) leaf normalization/preprocessing;
(2) ordered tree multiplication with smaller
P/Q/T operand bit heights;
(3) source receipt storage and, only if a
consumer demands raw coordinates, exact reopening.
The normalized projective source is sufficient
for present and all future *homogeneous*
right-extension observers, but NOT for a
consumer of literal unscaled integer P/Q/T
without the stored scalar recipe. Source
provenance remains an explicit independent
authenticity obligation.

A future source-typed proof should express
homogeneity of the actual original
\(M_LM_R\) monoid and the exact reconstruction
\(M=G M'\), then factor every
selected π certificate consumer and
parity/signed residual through the normalized
carrier. It should charge lookup/valuation
preprocessing and optional reopening in the
existing `FibreProgramComplexityExact` and
`EfficientRecoverableQuotientExact` terms.
Use `QueryFactorisationSufficiency` for
the consumer-relative positive theorem;
do not make a global all-consumers claim.

**User-directed deferral upheld:** no C++
compilation, Python or SymPy execution,
benchmark, CI, Agda/Lean kernel run or
external SOTA comparison for COMP5p/q/r.
Only live connected GitHub source read,
derivation, source writes and readbacks.
No new empirical timing/RSS claim. Exact
finite-source algebra is distinguished
from analytic Chudnovsky–Bishop same-real
proof, which remains open.


## 24 November — COMP5s: output-precision-indexed projective source execution DP (testing deferred)

Additional **source producer work** is explicitly counted in the new
C++ FIBRE receipt: `leaf_prime_content_calls`,
`leaf_small_mod_checks`, `leaf_small_div_steps` and
`leaf_exact_gmp_division_calls`. These are native
operation counts, not measured time or formal bit complexity.
Optional reverse opening is *not* invoked on the fast π
path, and its independent multiplication/work bill remains
an OPEN consumer-specific cost. The model's reported plan
object payload excludes malloc overhead; GMP hooks do not
measure ordinary C++ planner allocations.

**User goal:** combine actual COMP5r source-local
projective normalization with consumer-specific
evaluation scheduling, and retain signed residual,
zero mode, full source provenance and exact BIDI
reconstruction. This is **a new, separate UNTESTED
candidate**, not a replacement for the historical
measured COMP5j or the six-way acceptance runner.

### Owner and actual source files

- `scripts/pi_p0_projective_precision_schedule.hpp`
  implements a bounded-depth, source-width-based
  binary-tree execution planner. Its precision index
  comes from the current output demand \(d\) and
  the original dyadic square-root working bit index
  \(b\), not from a made-up model clock.
- `scripts/check_pi_p0_precision_projective_schedule.cpp`
  derives directly from the original COMP5r C++ leaf
  producer and GMP certificate. Every original
  positive-index leaf is divided by the **exact**
  source factor \(24h_j\) from the prime support
  \(\{3,5,23,29\}\), and no generic GMP gcd is
  required. A separately callable receipt
  `ProjectiveSourceReceipt{begin,end}` and
  `reopenOriginalRawSource` construct \(G(a,b)\)
  only when a consumer actually requests raw P/Q/T.

### Source-complete, homogeneous geometry

Let \(M_{a,b}=\left(
\begin{smallmatrix}P&T\\0&Q\end{smallmatrix}\right)\)
be the ORIGINAL Chudnovsky ordered matrix product,
\(M'_{a,b}\) its locally content-normalized image,
and \(G_{a,b}=\prod_{a\le j<b,j\ge1}(24h_j)>0\).
For all original intervals:

\[
M'_{a,b}=G_{a,b}^{-1}M_{a,b},\qquad
G_{a,b}=G_{a,m}G_{m,b},\qquad
M'_{a,b}=M'_{a,m}M'_{m,b}.
\]

The source matrix product is in general
NONCOMMUTATIVE. Choosing a right child before
the left child **for execution only** does not
change the merge order: always compute
\(M'_L M'_R\). The zero mode
\([a,a)\mapsto(1,1,0)\) remains the identity;
the original \(j=0\) leaf is not normalized.
The normalized next-term signed residual is
\(\delta'_n=P'_n p_n(A+Bn)\);
with original \(q_n>0,Q'_n>0\), its sign
\((-1)^n\) and the exact adjacent interval
are unchanged. The raw residual is
\(\delta_n=G_{0,n}\delta'_n\).
Thus all presently chosen homogeneous
\(T/Q\), signed adjacent interval and
integer floor certificate consumers factor
through \((M',G_{\rm recipe})\). Consumers
asking for literal original P/Q/T require
the separate exact reopening, including
its actual \(O(n)\) factor recipe and large
integer multiplication costs. Merely
recording the SCALE is not authenticity
of original leaf multiplication: signed
source provenance and/or an independent
source replay remains required.

### Source-derived bit-width forecast, not a floating proof of a bound

For \(u=\max(1,a)\), \(r=\max(0,b-u)\),
write \(L=\log_2((b-1)!/(u-1)!)\) if \(b>u\),
else \(L=0\). The *algebraic* inequalities
from the normalized original leaves give

\[
\begin{aligned}
\log_2 |P'_{a,b}|
 &\le r\log_2 72+3L,\\
\log_2 Q'_{a,b}
 &\le r\log_2 (640320^3/24)+3L,\\
|T'_{a,b}/Q'_{a,b}|
 &\le(b-a)\,(13591409+545140134(b-1)).
\end{aligned}
\]

The last inequality follows by expanding
the ordered upper-triangular product into
one term per original leaf: every normalized
nonzero source \(|p_j/q_j|\) equals the
raw ratio and is strictly below one,
and the \(j=0\) prefix is one.
Therefore absolute sums of terms are
bounded by the count times the largest
source \(A+Bj\). If \([a,a)\) is empty
then \(T=0\) exactly, rather than an
arbitrary small nonzero positive value.

The implementation evaluates these
formulae with `std::lgamma` in floating
arithmetic and adds slack to estimate
\((w_P,w_Q,w_T)\) and the P/Q/T carrier
bytes \(s\). The floating forecasts are
NOT certified integer upper bounds;
they are **execution-order heuristics**
only, and cannot be used to truncate a
source integer, weaken a sign gate or
deduce correctness of the output.

### Precision-adaptive peak-memory DP, no silent loss

Let \(d\) be decimal digits and \(b\)
the current dyadic root precision.
The *output demand* enters the planner
as a scheduling threshold
\(\max(4096,b/16)\) bits: only
projected large source subtrees within
the top ten recursion depths receive
a two-child schedule; the rest retain
the original ordered left-first execution.
Thus requested precision changes the
**planning effort**, not the integer
computation or its analytic stopping gate.

For children L/R with estimated retained
carrier sizes \(s_L,s_R\),
unretained execution peaks \(p_L,p_R\),
and a common merge scratch estimate
\(m\), the two execution choices have

\[
p_{L\to R}
=\max(p_L,s_L+p_R,m),\qquad
p_{R\to L}
=\max(p_R,s_R+p_L,m).
\]

The planner uses this simple recursion
to select the cheaper predicted order
at each scheduled internal node while
retaining \(P_LP_R,Q_LQ_R,
T_LQ_R+P_LT_R\). An unscheduled
subtree is modeled with the coarse
heuristic \(p=4s\); its merge scratch
is estimated from projected operand
width. These prices are **not measured
GMP scratch or proved bounds**.
They deliberately omit cache,
OpenSSL output hashing, actual
malloc fragmentation and CPU time.
No proof of globally optimal memory
scheduling or speed improvement follows.

The source's `FIBRE` receipt separates
`schedule_precision_bits`,
`schedule_plan_nodes`,
`schedule_merges`,
`schedule_right_first`,
`schedule_predicted_peak_bytes`
and `schedule_cpp_plan_object_payload_bytes`
from actual `gmp_peak_live_bytes` and
Linux VmHWM. The C++ plan object's payload-byte estimate is
`planNodes*sizeof(Plan)`: it excludes allocator overhead and
is **not** total measured C++ heap allocation. Neither
ordinary C++ planner allocation nor OpenSSL allocation is
covered by the GMP allocation hooks.
The normal `FC` measured source
operand-width and explicit carrier
observations remain separate from
the heuristic peak forecast.

### Exact indexed producer/consumer ledger and next named obligations

The original coordinates are
\((\text{source version},[a,b),n,d,b,
\text{normalization recipe},P',Q',T',
\operatorname{sgn}\delta,
\text{certificate output},
\text{cost model version})\).
Here \(n\) is the series cutoff, \(d\)
requested digits, and \(b\) the dyadic
root precision. These three indexes
are NOT interchangeable with H05's
history, physical event time, Frobenius
or geometric chart-depth coordinates.
The scale recipe is deterministic
from original source leaf indices.
Original raw and normalized zero modes
and signed residuals are retained,
and source-reconstruction loss is
never hidden in a coarse observed
π SHA256.

- **S1 source-to-projective:** original
  \(M\to (M',G_{\rm recipe})\),
  with exact scalar homogeneity and
  \(j=0\) exception (mathematical
  construction supplied; original Agda
  proof instantiation still OPEN).
- **S2 projective-to-source:** callable
  `reopenOriginalRawSource` reconstructs
  the literal triple with charged
  factor recomputation. This preserves
  algebraic reversibility, not
  independent original producer
  authentication (OPEN).
- **S3 consumer descent:** exact
  \(T/Q\), signed tail, adjacent bounds,
  strict upper dyadic floor and
  existing analytic-premise boundary
  preserved (source algebra supplied,
  code UNTESTED and formal kernel OPEN).
- **S4 peak-path planner:** same ordered
  matrix product with altered child
  evaluation order and separately
  recorded working-precision/plan
  overhead (implementation UNTESTED;
  calibrated GMP cost model OPEN).
- **S5 forbidden precision shortcut:**
  dropping low/high source limbs from
  P/Q/T using only \(d\) or \(b\)
  **is not certified**, because an
  altered residual can change the
  strict floor-admission decision.
  An actual certified truncation would
  require outward signed error
  enclosures, carry accounting and
  proof that BOTH inequalities survive.
  None is implemented or claimed.
- **S6 acceptance and SOTA:** local
  C++ compilation and exact-source
  output parity, sign order for both
  cutoffs, true GMP allocation/latency,
  independent certified verifier,
  Bishop same-original-real transport,
  and external SOTA remain OPEN per
  user's testing deferral.

This reuse is owned by the existing
`FibreProgramComplexityExact.agda`
sum/peak path formalism,
`EfficientRecoverableQuotientExact.agda`
construction/reopen separation,
`StreamingResidencyComplexityErrorDNABidiExact.agda`
memory semantics, and
`QueryFactorisationSufficiency.agda`
consumer-specific descent.
The full indexed hyperfabric identity
is \emph{not} assumed for an unrelated
physics/TOE source. No CPU/GPU
benchmark, Python, SymPy, CI, Agda,
Lean or external pi SOTA execution
was performed.


## 24 November — COMP5t: exact affine edge, radical/series separation and suffix-only continuation (testing deferred)

**Scope:** The Paper 9 P0 objective remains the fastest independently
certified decimal floor of π, conditional on the original Chudnovsky
analytic identity, alternating-series enclosure and source authenticity.
This tranche adds **source-exact architectural candidates only**.
No compilation, test execution, benchmarks, CI, Agda/Lean kernel check
or external SOTA check was authorized or performed.

### G9 — three-coordinate affine edge is bidirectional, not a lossy quotient

Continue the original locally normalized, ordered
\(2\times2\) upper-triangular source matrix
\(M'_n=\left(\begin{smallmatrix}P'_n&T'_n\\0&Q'_n
\end{smallmatrix}\right)\), together with cutoff index \(n\ge2\).
Let the ORIGINAL unnormalized next leaf factors be

\[
p_n=-24(2n-1)(6n-5)(6n-1),\quad
q_n=640320^3n^3,\quad a_n=13591409+545140134n .
\]

The genuinely new edge coordinate (a known next-source
consumer, not an arbitrary derived number) is

\[
V_n=T'_nq_n+P'_np_na_n.
\]

The **affine edge** is
\(E_n=(n,T'_n,Q'_n,V_n)\). It provides the exact pair

\[
S_n=\frac{T'_n}{Q'_n},\qquad
S_{n+1}=\frac{V_n}{Q'_nq_n}.
\]

Crucially, the source-to-edge map has an exact inverse,

\[
\boxed{
P'_n=\frac{V_n-T'_nq_n}{p_na_n},
\quad Q'_n=Q'_n,\quad T'_n=T'_n .
}
\]

The numerator is the ORIGINAL signed next-term residual
\(\delta'_n\) and is divisible by the nonzero source factor
\(p_na_n\) for an authentic ordered Chudnovsky product.
No precision truncation or numerical approximation is involved.
For even \(n\), \(\delta'_n>0\); for odd \(n\),
\(\delta'_n<0\). The empty interval remains the source
identity \(M'[a,a)=I\), not a fabricated edge; the edge is
used only for the terminal authentic prefix \(n\ge2\).
The projective original-to-normalized gauge scale
\(G_{0,n}=\prod_{j=1}^{n-1}(24h_j)\) is a **distinct
source-indexed receipt**; from an edge one first recovers
normalized P/Q/T, and to recover the literal original
raw P/Q/T one additionally multiplies by \(G_{0,n}\).

The precise identity is **source-relative**:
without a producer witness that the original ordered
leaf composition generated \((P',Q',T')\), divisibility
and sign tests alone cannot authenticate a forged edge.
No all-consumer observability theorem is claimed:
consumers that demand original raw coordinates must
pay the source-scale reopening cost. The selected
series and certification consumers are sufficient
on this affine edge and its indexed recipe.

### G10 — root versus series refinement has an exact square-slack discriminator

Let \(S_{\rm lo}=N_{\rm lo}/D_{\rm lo}\),
\(S_{\rm hi}=N_{\rm hi}/D_{\rm hi}\) be the
original positive *source-consecutive* rational
series bounds, ordered using the signed residual.
Let

\[
F=426880\,10^d,\quad
K=F\sqrt{10005},\quad
L=K/S_{\rm hi},\quad
U=K/S_{\rm lo}.
\]

The target is \(L\le10^d\pi\le U\), conditional
on the original analytic source. The current
dyadic lower-root enclosure gives \(x=\lfloor
F R_bD_{\rm hi}/(2^bN_{\rm hi})\rfloor\),
where \(R_b=\lfloor2^b\sqrt{10005}\rfloor\).
Thus **always** \(x\le L\).

On ordinary exact integer upper-witness failure,
evaluate the following source-identified squared
slacks (all denominators and terms positive):

\[
D_b=10005(FD_{\rm hi})^2-
        ((x+1)N_{\rm hi})^2,
\qquad
D_n=((x+1)N_{\rm lo})^2-
        10005(FD_{\rm lo})^2 .
\]

This yields an **exact three-way discriminator**:

1. \(D_b\ge0\): then \(x+1\le L\).
   The dyadic root guard has not yet recovered
   the actual source-lower integer floor.
   Increase **only** the radical precision \(b\),
   keeping the same edge and original cutoff \(n\).
2. \(D_b<0,\ D_n>0\): then
   \(x\le L<x+1\) and \(U<x+1\);
   the original decimal floor \(x\) is already
   certified by the integer-square upper witness.
   Admit without increasing either index.
3. \(D_b<0,\ D_n\le0\): then
   \(x=\lfloor L\rfloor\) is *already*
   the exact lower-source floor, while the
   source upper bound is insufficient.
   Increasing the radical guard cannot improve
   the fixed-source floor: extend **only** \(n\).

The irrationality of \(\sqrt{10005}\) means
the boundary \(L=x+1\) is not an equality
for positive rational endpoints, but the
implementation still handles equality
conservatively. This is a **mathematical
resource decision**, not an empirical
prediction: it separates which source/precision
coordinate still blocks a strict certificate.
It is not a proof that the expensive exact
square comparisons are cheaper than an
extra standard split or a finer root.

The two possible refinements are separately
monotone with their original mathematical meaning:
larger \(b\) improves the outward root interval,
and larger \(n\) narrows the alternating series
enclosure (regardless of n parity, with the source
sign controlling orientation). A successful
witness always retains the original signed
admission gate and its precise integer \(x\).

### G11 — suffix-only ordered extension of the authenticated projective source

Suppose the certificate needs more series
terms, from \(n\) to \(n'>n\). From the current
affine edge, exactly reconstruct normalized
\((P'_n,Q'_n,T'_n)\) by the single
source-factor \`mpz_divexact\` above.
Compute only the NEW original-indexed
suffix \([n,n')\) using the COMP5s
precision-aware planner and exact prime-local
leaf normalization. Then compose

\[
\boxed{
M'_{0,n'}=M'_{0,n}\,M'_{n,n'}
}
\]

in original left-to-right order; never
multiply \(M'_{n,n'}M'_{0,n}\).
Because the scale recipe composes as
\(G_{0,n'}=G_{0,n}G_{n,n'}\),
the result is the same normalized
full Chudnovsky matrix as a fresh
\([0,n')\) binary split, **up to
different associative parenthesization**,
which is exact for the original
upper-triangular monoid. Compute the
new signed affine edge for cutoff \(n'\)
and release the old next-term observation.

A precision-only retry keeps \(E_n\)
**unchanged** and recomputes only the
radical root at larger bit index \(b\),
with source-normalized P completely dead.
A series-only retry can retain the
existing cached radical root at the same
\(b\). The initial full prefix is built
once; no full-prefix rebuild is needed
on later retries. This is not a
worst-case latency theorem: suffix
splits, signed P reopening, new
endpoints and conditional big squares
all incur real costs.

### New source owners and cost-fibre counters

- \`scripts/pi_p0_affine_edge_retry.hpp\` —
  reversible three-coordinate source edge,
  original signed residual, authentic-source
  inverse and exact root/series square-slack
  repair classifier.
- \`scripts/check_pi_p0_affine_retry_schedule.cpp\` —
  source-normalized GMP leaf producer and
  original ordered merge from COMP5s;
  stores only \(E_n\) between certificate
  attempts, uses \`makePlanInterval\` for
  truly indexed suffixes, guards the
  unsigned \(n,b\) refinements, uses an
  optional \(F\) product only if the
  ordinary certificate fails, and
  retains the original SHA output
  consumer on either admission route.
- \`scripts/pi_p0_projective_precision_schedule.hpp\` —
  extended with \`makePlanInterval(begin,end)\`
  so a suffix is scheduled using its
  actual original leaf indices rather
  than silently replacing \([n,n')\)
  with \([0,n'-n)\).

The added \`FIBRE\` fields count
\`retry_initial_tree_builds\`,
\`retry_suffix_tree_builds\`,
\`retry_signed_P_reopening_divisions\`,
\`retry_guard_only_refinements\`,
\`retry_series_only_refinements\`,
\`retry_exact_square_classifications\`,
\`retry_square_slack_admissions\`,
\`retry_root_builds\`,
\`retry_certificate_attempts\` and
aggregate scheduled plan nodes.
These are structural operation counts,
not a certified total-cost bound or a
new runtime receipt. Original source
prime-valuation, GMP exact leaf division,
allocator peak and output hash counters
remain separate. Beware: the derived
next denominator \(Q'_nq_n\) can be
large and must be re-materialized per
attempt; reduced *resident P* alone
does not establish lower actual RSS.

### S7–S12: precise remaining bridge obligations

| Gate | Exact obligation | Status |
|---|---|---|
| S7 | Original \(M'\leftrightarrow E_n\) inverse, including nonzero signed divisor, source \(j=0\) and zero-mode distinction | Source-level algebra written; Agda/Lean kernel OPEN |
| S8 | \((x+1)S_{\rm hi}\le K\) square-slack test and upper signed square-slack equivalence, with full positivity | Algebraic derivation written; kernel OPEN |
| S9 | Genuine indexed suffix composition and scale recipe \(G_{0,n'}=G_{0,n}G_{n,n'}\) under noncommutative ordered merge | Implementation candidate, kernel OPEN |
| S10 | Separate \(n\)-refinement and \(b\)-refinement termination under original analytic tail and non-integral target | Conditional mathematical argument; formal analytic/Bishop source OPEN |
| S11 | Consumer-relative exact performance model charging signed P reopening, classified square work, regenerated denominator and compiler/allocator peak | Structural counters committed; cost calibration OPEN |
| S12 | Exact GitHub-source build and independent output/bound/negative acceptance, source authenticity, memory/time Pareto and SOTA | Testing explicitly DEFERRED |

No “cost saved” or fastest π claim
follows until a real source-matched
execution and controlled comparison
exists. The original measured COMP5j
remains the performance baseline.


## 24 November — COMP5u: PNP G79–G83 inspired consumer-sector contraction and exact dyadic carry (NO TESTING)

### Source attribution and strict transfer boundary

User-provided 24 Nov P-vs-NP G79–G83 note studies **affine shared
separators** over \(\mathbb F_2\) and, in G83, gives a nonlinear
four-sector running contraction that avoids materializing exponentially
many separator assignments. That is a *methodological donor only*.
Paper 9's Chudnovsky P/Q/T matrices and dyadic Euclidean remainders
are over the ordered integers, **not** \(\mathbb F_2\); its G79
least-shared-subspace theorem and G80 contraction formula do NOT
prove any π identity or runtime bound. The actual lesson from
G83 is to cost the final source-adequate **consumer decision**, not
the size of an expanded geometric observer. The existing
P-vs-NP nonlinear composition lower-bound targets remain separate.

COMP5t's original exact square-slack retry classifier is a valid
research construction but on every inconclusive admission can
construct several huge integer squares and the entire decimal
factor \(F=426880\,10^d\). We can decide safe refinement using
the much smaller **dyadic division-remainder sectors** already
present in the actual floor certificate. This is a mathematical
alternative with different possible work, not a measured speedup.

### G12 — joint dyadic quotient-remainder decomposition

For original signed and source-authenticated adjacent series endpoints
\(0<S_{\rm lo}=N_l/D_l\le S\le S_{\rm hi}=N_h/D_h\),
take positive \(d\) decimal places, current original radical index
\(b\ge d\), \(R_b=\lfloor2^b\sqrt{10005}\rfloor\),
\(k=b-d\), \(H=426880\,5^d>0\). The original π source gives

\[
10^d\pi=426880\,10^d\sqrt{10005}/S,\qquad
H R_b/2^k\le426880\,10^d\sqrt{10005}
          <H(R_b+1)/2^k.
\]

The correct conservative lower endpoint is exactly
\(x=\lfloor H R_bD_h/(2^k N_h)\rfloor\).
Retain *both* Euclidean remainders without truncation:

\[
A=H R_bD_h=2^k(xN_h+\rho)+\ell,\quad
0\le\rho<N_h,\quad0\le\ell<2^k.
\]

The source-lower quotient's upper-radical floor crosses the
next decimal integer iff

\[
\boxed{\rho+
 \left\lfloor\frac{\ell+HD_h}{2^k}\right\rfloor
 \ge N_h.}
\tag{G12-left}
\]

Separately the ordinary upper-bound witness uses
\(W=H(R_b+1)D_l=2^k u+\eta\),
\(0\le\eta<2^k\).
Its strict upper admission is simply

\[
\boxed{u<(x+1)N_l.}
\tag{G12-admit}
\]

Rather than form an independent \(H R_bD_l\) product, reuse
this **same** upper-radical numerator:
\(H R_bD_l=W-HD_l\). The lower-radical floor of the
upper source endpoint is therefore exactly

\[
\boxed{
\left\lfloor\frac{H R_bD_l}{2^k}\right\rfloor
  =u+\left\lfloor\frac{\eta-HD_l}{2^k}\right\rfloor .
}
\tag{G12-right}
\]

The inner signed floor is essential: \(\eta-HD_l\) can be
negative, so the implementation uses GMP
`mpz_fdiv_q_2exp` (Euclidean floor) rather than C++
signed truncation toward zero. The two formulas avoid
computing \(\sqrt{10005}\) or a **full radicand square**
during sector selection; the exact integer square-root
\(R_b\) for the ordinary certificate remains required.

### G13 — exact three-sector consumer and what it does NOT establish

Let \(v=(x+1)N_l\).
The three genuine decision sectors are:

1. **Admit** when \(u<v\). Both original positive
   outward π endpoints prove \(\lfloor10^d\pi\rfloor=x\).
2. **ExtendSeries** when the admission fails,
   \(u+\lfloor(\eta-HD_l)/2^k\rfloor\ge v\), and
   \(\rho+\lfloor(\ell+HD_h)/2^k\rfloor<N_h\).
   The actual source upper π endpoint is at least
   \(x+1\), while its lower endpoint lies below
   \(x+1\). Therefore further radical bits **cannot**
   make the current source pair certify x; compute an
   original-indexed Chudnovsky suffix \([n,n')\) and
   recompose the original ordered matrix.
3. **RefineRadical** in all remaining authentic cases.
   Root precision is the safe refinement direction;
   it may over-refine b even if a full exact-square
   classifier would already show a source obstruction.
   Do NOT claim this is the least-cost choice or that
   series source is definitely sufficient.

An **invalid source/zero-sign** state is rejected by the
authenticated affine edge and positive endpoint checks
*before* this classifier; it is NOT silently counted
as another positive numerical sector. This mirrors
G83's retained zero/excluded residual, without
identifying finite-field guard states with these
integer inequalities.

With a fixed positive rational source pair, each
radical enclosure tightens as \(b\) increases;
the two endpoint values \(K/S_{\rm lo}\) and
\(K/S_{\rm hi}\) are irrational because
\(\sqrt{10005}\) is irrational and all
other factors are nonzero rationals.
Consequently both upper/lower dyadic ambiguity
bands eventually separate from any fixed
integer boundary. Such a statement does NOT
replace the original series-tail certificate
or establish a uniform practical runtime bound.
The series cutoff index \(n\), radical guard
\(b\), digit demand \(d\), source prime-local
scale recipe and sign must remain independent.

### COMP5u — original-source, suffix-only implementation (UNTESTED)

- `scripts/pi_p0_dyadic_sector_contraction.hpp`:
  pure GMP integer sector classifier with two
  dyadic quotient/remainder operations, the
  exact lower integer quotient/remainder,
  lazy upper-root and lower-root ambiguity
  corrections, and structural operation
  counters. It keeps no global SAT separator
  or F2 matrix. Signed right-side correction
  is explicitly floor-divided.
- `scripts/check_pi_p0_dyadic_sector_schedule.cpp`:
  derives from COMP5t's exact projective
  indexed-prime source, affine edge, single
  authenticated prefix and right-ordered
  suffix-only extension. It replaces only
  the *retry classifier*, leaves the original
  dyadic root and strict upper arithmetic
  consumer intact, preserves the original
  `[n,n')` source indices and positive
  scale recipe, and emits separate
  `retry_sector_*` cost counts.
  Unlike COMP5t it does **not** build
  \(10005(FD)^2\) slacks on failed
  ordinary admission. The old COMP5t
  implementation remains available and
  unmodified for later comparison.

**Important memory/cost negative control:** the
residue representation retains \(\rho,\ell,\eta\)
and performs additional signed dyadic shifts and
\(H D_l,H D_h\) multiplications, potentially
increasing GMP memory and runtime. Avoiding
four large squares does NOT prove this path
dominates COMP5t or COMP5j; a larger auxiliary
state may be cheaper to *consume* yet more
expensive to *construct*. The GMP allocator
and full source-work/receipt ledgers are
authoritative only after deferred execution.

### G14 — projective raw-remainder reopening requires a dyadic carry

The final rational/decimal floor consumer is
homogeneous under the original prime-local
source scale \(G=G_{0,n}>0\):
\(A_{\rm raw}=GA_{\rm norm}\) and
\(N_{\rm raw}=GN_{\rm norm}\). But the normalized
nested Euclidean quotient-remainder pairs are
**not** individually scalar homogeneous.
If

\[
 A'=2^k(xN'+\rho')+\ell',
 \quad0\le\rho'<N',\quad0\le\ell'<2^k,
\]

then define the *indexed dyadic carry*

\[
c=\left\lfloor\frac{G\ell'}{2^k}\right\rfloor.
\]

The exact reconstructed raw-source remainder
coordinates are

\[
\boxed{
N=GN',\quad \rho=G\rho'+c,\quad
\ell=(G\ell')\bmod2^k.}
\]

In particular \(0\le \rho<N\). The **quotient x is
unchanged**, while the low/high remainders can
change discontinuously with the source gauge.
This is the actual carry/reopening phenomenon
analogous to, but not dependent on, Langlands
R96's relative-index caution.

The optional source-reconstruction function
`reopenRawDyadicFibre` in the new header
implements the exact positive-scale carry,
checking the canonical remainder bounds.
It is NOT invoked in fast π production,
where the normalized gauge is sufficient.
Raw source authentication still requires
an independently authenticated ordered
leaf producer and the original \(G\) recipe.
The signed residual simultaneously reopens
as \(\delta=G\delta'\), preserving zero mode
and orientation. The raw and normalized
Euclidean receipts must never be silently
identified.

### S13–S19 next exact obligations

| Gate | Obligation | Status |
|---|---|---|
| S13 | G12 nested Euclidean identities and negative signed-floor correction | Source algebra derived; formal Agda/Lean proof OPEN |
| S14 | G13 safe three-sector refinement for authenticated positive endpoints, incl. odd/even source sign | Derived; source code UNTESTED |
| S15 | Full source-scaled/remainder carry BIDI G14 and original signed delta | Reopening helper committed; source authenticity/kernel OPEN |
| S16 | Correct terminal floor and series suffix after guard-only vs source-only retry | Candidate committed, exact-source replay DEFERRED |
| S17 | Costed comparison against COMP5t: lower quotient divmod, upper dyadic divmod, scaled endpoint products, extra residency vs four radical squares | Structural work counters, no empirical or proved dominance |
| S18 | Negative controls: modular-zero vs true source zero; near-boundary \(x+1\), wrong sign of \(\eta-HD_l\), odd cutoff, source-scale carry and source observer collisions | Contracts stated, tests DEFERRED |
| S19 | P0 analytic Chudnovsky/Bishop same-original-real and external speed/verification frontier | OPEN, no change to independent SOTA |

**Testing remains deferred by user request.**
No C++ compilation, runtime checks, Python/SymPy
execution, GMP timing/RSS, GitHub CI, Agda/Lean
kernel proof or world-record claim was made.
The historical COMP5j measured baseline is
unchanged and COMP5u is not inserted into the
six-way benchmark default.


## 24 November — COMP5v: one shared radical product for both adjacent Chudnovsky consumers (NO EXECUTION)



**Integrated source audit correction:** the first
COMP5v wrapper inherited a COMP5u
`viewEndpoints(edge)` call, which
eagerly produced \(Q'q\) even though
the classifier did not consume it.
The integrated source was corrected
to invoke the signed cone directly
and pass only the indexed edge.
Consequently the new fast candidate
does not construct the full
adjacent denominator as a separate
terminal GMP integer; it obtains the
necessary \(q\) factor from the
literal original source index.

A source-specific operand-width
bound supports the motivation while
remaining distinct from any measured
speed claim. If \(1\le n<2^{20}\),
then \(640320<2^{20}\), and hence

\[
q_n=(640320\,n)^3<2^{120}.
\]

Thus in this cutoff region the
parity multiplication uses at most
a 120-bit positive operand in
place of one independently
constructed large root product.
This alone does **not** prove a
particular GMP throughput, peak
memory or latency improvement:
intermediate shared-product
liveness and memory scratch must
still be measured.

**Motivation and donor boundary.** The user's P-vs-NP G83
negative control reminds us that the cost of an expanded
source observation is not the cost of its actual consuming
arithmetic. The current original π source is NOT a SAT or
\(\mathbb F_2\) problem. COMP5v is a separate exact
INTEGER source factorization of COMP5u's same original
Chudnovsky edge and three-sector certificate. No
finite-field contraction, unproved compression, or
P-vs-NP hardness statement is imported.

### G15 — exact common-radical factorization from the signed affine edge

Use the genuinely normalized source edge
\(E_n=(n,T',Q',V)\) from COMP5t and the literal
source next-denominator \(q=q_n>0\).
Let \(H=426880\,5^d>0\), \(R=\lfloor
2^b\sqrt{10005}\rfloor\), \(k=b-d\ge0\).
Compute exactly

\[
Z=HQ',\qquad Y=ZR.
\]

No extra precision assumption or source-coordinate
truncation is needed. The original positive source
series bounds are ordered by the **signed residual**
\(\delta'=V-T'q\), whose sign is
\((-1)^n\). The source-defined adjacent endpoint
denominators are \(Q'\) and \(Q'q\), but the
following products need not MATERIALIZE \(Q'q\)
as a separate multi-limb integer:

| Original cutoff | \(N_{\rm lo}/D_{\rm lo}\) | \(N_{\rm hi}/D_{\rm hi}\) | Lower root numerator \(A=HRD_{\rm hi}\) | Upper root numerator \(W=H(R+1)D_{\rm lo}\) |
|---|---|---|---|---|
| even \(n\) | \(T'/Q'\) | \(V/(Q'q)\) | \(qY\) | \(Y+Z\) |
| odd \(n\) | \(V/(Q'q)\) | \(T'/Q'\) | \(Y\) | \(q(Y+Z)\) |

Proof: substitute \(Y=HRQ'\) and
\(Z=HQ'\). For even \(n\),
\(HR(Q'q)=qY\) and \(H(R+1)Q'=Y+Z\).
For odd \(n\), \(HRQ'=Y\) and
\(H(R+1)(Q'q)=q(Y+Z)\). All products
are over the EXACT same original
normalized integer source; the
\(q\) factor is unchanged (a raw next leaf,
NOT its prime-local normalized producer).
The 2×2 matrix product and signed
orientation are unchanged.

The numerator quotient and two
Euclidean remainders therefore remain
*literally identical* to COMP5u's
normalization-coordinate values:

\[
A=2^k(xN_{\rm hi}+\rho)+\ell,\quad
0\le\rho<N_{\rm hi},\quad0\le\ell<2^k
\]

and

\[
W=2^k u+\eta,\quad0\le\eta<2^k.
\]

Thus all three COMP5u decision sectors
and the G12–G14 positive/signed correction
arguments carry over **without** changing
the output floor, adjacent endpoints,
series cutoff, radical guard or
source-scale recipe. This is an
algebraic code transformation, not an
experimental equivalence certificate.

### G16 — failure-only remainder construction and selected cost fibres

Original COMP5u always computes \(\eta\)
using `mpz_fdiv_qr_2exp` on \(W\)
before knowing whether the first strict
upper comparison succeeds.
COMP5v first computes the upper
dyadic **quotient only**, admitting if

\[
u=\lfloor W/2^k\rfloor < (x+1)N_{\rm lo}.
\]

Only if this fails does it materialize
\(\eta=W\bmod2^k\), then perform the
same two signed/unsigned COMP5u
corrections:

\[
u+\left\lfloor\frac{\eta-HD_{\rm lo}}{2^k}\right\rfloor,
\qquad
\rho+\left\lfloor\frac{\ell+HD_{\rm hi}}{2^k}\right\rfloor .
\]

Their source-aligned scale products are
\(HD_{\rm lo}=Z\) and \(HD_{\rm hi}=qZ\)
for even \(n\), reversed for odd \(n\).
No second square-root multiplication
or entire 10005 radicand square is
needed to classify an ordinary
failure. A successful first upper
comparison never creates \(\eta\).
The lower Euclidean \(\rho,\ell\)
are still produced unconditionally
in this variant; a future even
lazier lower-division strategy must
charge reconstructing them on failure
instead of silently treating them
as available.

Resource hypotheses are NOT
performance facts. COMP5u forms
two independently evaluated root
products \(H R D_{\rm hi}\) and
\(H (R+1)D_{\rm lo}\), whereas COMP5v
forms a single shared \(Y=H Q'R\)
and uses additions and source
\(q\)-multiplications. COMP5v adds
potentially costly \(qY\) (even)
or \(q(Y+Z)\) (odd) and on-demand
\(qZ\) correction products.
Neither the arithmetic bit cost
nor actual GMP peak is thereby
proved lower for all n,b,d.
The source's `Counts` ledger
separately records base creation,
single shared radical product,
parity \(q\) products, two lower
divisions, upper quotient, failure-only
upper remainder, correction products
and selected sectors. These counts
are **logical source sites**, not
complete multiplication-bit-work
or measured memory. Existing GMP
allocator hooks remain the
eventual empirical physical receipt
boundary, not a claim that the
current candidate was executed.

### G17 — same projective BIDI and exact carry under shared construction

The source gauge \(G_{0,n}=
\prod_{1\le j<n}24h_j>0\) remains
attached to the indexed normalized
edge. For authentic raw P/Q/T,
\(Q_{\rm raw}=GQ'\), \(T_{\rm raw}=GT'\),
\(V_{\rm raw}=GV\) and
\(\delta_{\rm raw}=G\delta'\).
Therefore \(Z_{\rm raw}=GZ\),
\(Y_{\rm raw}=GY\), \(A_{\rm raw}=GA\),
\(W_{\rm raw}=GW\).
This DOES NOT mean that the
nested Euclidean residues scale
linearly. G14 still applies:

\[
c=\left\lfloor\frac{G\ell'}{2^k}\right\rfloor,\quad
\rho_{\rm raw}=G\rho'+c,\quad
\ell_{\rm raw}=(G\ell')\bmod2^k.
\]

The exact raw-source scale recipe
is optional to evaluate in the
fast floor path; an independently
authenticated producer and
scale reconstruction are still
required if a consumer demands
literal original integer
coordinates or raw quotient
remainders. A zero remainder
in one gauge is not necessarily
a zero remainder in another,
and this is distinct from the
actual source zero mode and
original signed tail.

### COMP5v source owners and next gates

- `scripts/pi_p0_shared_radical_sector.hpp`:
  original-source sign-checked
  common-factor and three-sector
  consumer, with lazy \(\eta\)
  on failure and primitive counters.
- `scripts/check_pi_p0_shared_radical_schedule.cpp`:
  integrated COMP5u-derived independent
  GMP candidate, unchanged full-precision
  original P/Q/T projective leaf
  producer, original source \([n,n')\)
  suffix extension, signed exact-P
  reopening, no changed radix/analytic
  stopping gate, and separate receipt
  fields. The original COMP5u and
  COMP5t comparison candidates remain
  in place, as does measured COMP5j.

| Gate | Exact obligation | Status |
|---|---|---|
| S20 | G15 both-parity common-factor identities and preserved ordered source matrix | Derived algebraically; source candidate committed, kernel OPEN |
| S21 | G16 lazy \(\eta\), signed floor division and identical three-sector classification to COMP5u | Derived; exact-source compilation and negative tests DEFERRED |
| S22 | G17 original projective raw coordinate and Euclidean dyadic carry reopening | Existing helper retained; formal original-source authentication/kernel OPEN |
| S23 | Costed comparison of **one large root product plus q products** against **two root products**, including live GMP limb scratch, on-demand remainder and planning | Structural source counters only; optimized dominance OPEN |
| S24 | Signed odd/even cone, n/d/b separation, source-only suffix and root-only guard retry | Candidate preserved; native acceptance DEFERRED |
| S25 | Analytic original Chudnovsky π, Bishop same-real, formal cost theorem and external independently certified SOTA | P0 OPEN |

**No testing or benchmarks per explicit user direction.**
No C++ compilation, independent Python/SymPy
runtime, GitHub CI, Agda/Lean kernel, measured
runtime/heap/RSS or world-record comparison
performed in this tranche. Mathematical
source identities do not imply a
speedup until bit-cost and memory
work are actually established.
