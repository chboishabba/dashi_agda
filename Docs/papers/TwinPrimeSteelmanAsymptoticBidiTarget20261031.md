# Twin-prime steelman BIDI: exact decision target and asymptotic programme

**31 October 2026.** Attribution: Hardy–Littlewood (1923) original prime-pair asymptotic conjecture; Brun, Chen, GPY, Zhang, Maynard–Tao and Polymath8 for sieve and bounded-gap developments; Axiom Math PrimeGapsLib and OpenAI PrimeGaps186 for independently authored formalisation. Existing DASHI arithmetic/Agda owners remain intact. This document adds an unproved research *target*, not a theorem claiming twin primes.

## Keep two targets, not a movable goalpost

- **Acceptance / exact BIDI (T0)**: actual twin-prime infinitude iff real prime-only weighted correlation `P(X)` is unbounded iff infinitely many disjoint dyadic start-point slabs carry positive prime-only weight. The last statement uses **infinitely many**, not merely some slabs, and exact Nat prime ownership.
- **Positive limsup sufficient (T1)**: `limsup S(X)/X > 0`, plus independently proved `E(X)=o(X)`, implies T0. Neither T0 nor the logical equivalence implies T1.
- **Uniform positive density sufficient (T2)**: `liminf S(X)/X > 0` implies T1. This is stronger and remains open.
- **Hardy–Littlewood asymptotic steelman (T3)**: `S(X) ~ 2 C_2 X`, where `C_2 = product_{p>2} [1 - 1/(p-1)^2]`. Under the conventional Hardy–Littlewood singular series normalization, `2C_2 ≈ 1.3203236317`. This implies T2. It is a conjectural goal, not a proved result.
- **Twin counting asymptotic (T4)**: `pi_2(X) ~ 2 C_2 * integral_2^X dt/(log t)^2` (equivalently `~ 2 C_2 X/(log X)^2`). This implies T0; the exact equivalence of T3 and T4 is **not assumed** without a separate weighted-to-unweighted transfer theorem and prime-power control. T3's weighted P asymptotic can imply T4 via partial summation under established weight comparison, but reverse implications require care at error scale.

Classical `S(X) = sum_{n+2<=X} Lambda(n)Lambda(n+2)`, `P(X) = sum_{p+2<=X, p,p+2 prime} log(p)log(p+2)`, and `E(X)=S(X)-P(X)>=0`.

The proper-prime-power support bound
`E(X)=O(sqrt(X)log²(X)+X^(1/3)log³(X))=o(X)`
is elementary and independent of Hardy–Littlewood. Its analytic paper derivation should not be mislabelled kernel-certified Agda. Distinguish genuine PrimeNat certificates from an abstract Mangoldt carrier and real weights.

## Bidirectional proof-search protocol

**Forward (SOTA to target):** import bounded-gap theorems at their *exact* logical strength. H1<=246 and conditional Lean H1<=186 control two primes with an offset bounded by B, **not** offset exactly 2. Chen's almost-prime endpoint is not necessarily prime. No such theorem directly supplies T0 or any positive twin-pair asymptotic.

**Backward (target to minimal lemma):** for T3, the singular-series main term requires a prime-pair correlation cancellation / distribution theorem at exact shift +2 and a remainder `R(X)=o(X)` in `S(X)=2C_2 X+R(X)`. Do not simply define `R=S-2C_2 X` and call it small. For T0, an unbounded nonnegative prime-only weight or cofinally nonempty certified twin windows is sufficient and necessary; a mere infinite sieve survivor sequence is not.

**Discriminator**: any graph/FRACTRAN/CRT/residual transfer must preserve true prime-one labels and sign/weight. Explicit double-composite survivors defeat an argument relying solely on finite modular information. A synthetic receipt or numerical match to 2C2 cannot be promoted to a distribution theorem.

**Steelman bidirectional acceptance:** require (i) exact provenance, (ii) a source theorem's assumptions, (iii) a map to the actual shifted Mangoldt real scalar, (iv) sharp distinction T0 versus T1–T4, (v) a finite adversarial countermodel or obstruction test, and (vi) kernel receipt for formal claims.

## Precise SOTA status

Polymath8b unconditional H1<=246. PrimeGaps186 GitHub README and formalization.yaml declare its 186 result proved in Lean **conditioned** on three external inputs: hyper-Kloosterman estimate, Kloosterman correlation estimate and numerical physical-integral/cap bounds. Thus a successfully checked conditional theorem is not an unconditional H1<=186 proof, much less T0–T4.

References:
- https://github.com/openai/PrimeGaps186
- https://github.com/openai/PrimeGaps186/blob/main/formalization.yaml
- https://annals.math.princeton.edu/2015/181-1/p07
- https://en.wikipedia.org/wiki/Twin_prime#First_Hardy%E2%80%93Littlewood_conjecture

**Proof status:** specification and research plan. Neither T0, T1, T2, T3 nor T4 has been discharged for actual primes. No ESD changes.
