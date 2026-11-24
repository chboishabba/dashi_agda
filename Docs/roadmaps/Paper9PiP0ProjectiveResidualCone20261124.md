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
