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
