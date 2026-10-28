# Exact cross-pollination ledger: ternary geometry, phase quotients, certified prime-pair sieves

**As at 28 October 2026.** Primary work branch: [PR #1408](https://github.com/chboishabba/dashi_agda/pull/1408). Finite Fourier donor: [PR #1407](https://github.com/chboishabba/dashi_agda/pull/1407). Other reuse: PR #1390 ternary codec and PR #1389 E6/F3^5 exceptional arithmetic. The original owners, their dates and their prior proofs retain attribution.

This ledger distinguishes **equal numbers**, **explicit maps**, **kernel-written proof terms**, **executed local numerical checks**, **kernel-verified results** and **open analytic claims**. Equal dimension is never a same-object theorem. No material here proves infinitely many twin primes.

## A. The actual typed carriers

| Quantity | Actual carrier/operation | Existing owner | New use / limitation |
|---|---|---|---|
| `3×3×3=27` | Cartesian triple of three independently typed balanced trits x,y,z | `Base369Ternary27HypervoxelFabricGeometryExact` | Explicit coordinates, NOT 27 anonymous prime labels |
| `27=1+13×2` | One centre and thirteen strict global sign-orbits of size two | `BalancedTernaryAntipodalOrbitExact` | C₂ symmetry; sign quotient alone loses direction |
| `27→3×5=15` | Retain outer x phase, quotient simultaneous negation of inner pair y,z | `IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact` | Phase-orbit *index*; loses inner sign; NOT a Monster action recognition theorem |
| `27→14` | Quotient **all three axes** by the global C₂ antipode | `BalancedTernaryAntipodalOrbitExact` | Fourteen classes; different operation from 3×5=15 |
| `27↔(14+dependent orientation)` | Lossless quotient plus residual | `BalancedTernaryAntipodalResidualCodecExact` | Exact reconstruction, unlike the bare 14-class quotient |
| `5+10=15` and `15→14→42` | Five mode labels, ten oriented mode labels, omit a distinguished neutral, then 3×14 | `IbrahimMonster42dFifteenFourteenPhaseCarrierExact` | Source-owned finite index decomposition; not the FRACTRAN programme |
| **14** | Ordered Guy/Conway PRIMEGAME rational instructions | Conway 1987, Guy 1983, new `PrimegameSSP15CarrierFactorisationExact` | Exactly 14 historical rules |
| **10** | Distinct typed prime factors actually used in the 14 Guy instructions | `PrimegameSSP15CarrierFactorisationExact` | 2,3,5,7,11,13,17,19,23,29 |
| **15** | Typed Ogg SSP prime carriers | `SignedSSPFRACTRANWeaveExact` | 15 *carrier values*, not 15 historical fractions |
| `27×27=729` | Ordered pairs of two separate three-axis cubes | PR #1407, `R2P227729PairSixTritFibreBidiExact` | True six-coordinate carrier; 343 retained sums /386 outside |
| `4³=64`, `5³=125` | Retained vs full finite quadratic-output Fourier index grids | PR #1407 `FourGridRetainedQuadraticParetoExact` | Consumer-specific alias-freedom, **not** a prime distribution theorem |
| `3⁹=19683` | Nine axes grouped as three separate ternary triples (3+3+3) | `Base369NDimParetoChartExact` | Chart capacity; Pareto dominance still uses the task's actual cost function |
| `3⁵=243`, `5³=125` | Different finite cardinalities; the E6 `F3^5` exceptional study is independently owned by PR #1389 | PR #1389 original E6 mathematical owner; `TwinPrime369IbrahimQuotientBoundaryExact` arithmetic inequality | The two bases and exponents are **not interchangeable**; same-looking form is not an identity |

## B. Real arithmetic structure in the prime-3 slice of 3³

Fix the **first** balanced trit x at −1. Write the other independent coordinates as y,z∈{−1,0,1}. Interpret the centered integer residue

`n = −1 + 3y + 9z (mod 27)`.

The nine values are **2,5,8,11,14,17,20,23,26**, exactly the nine residues in 0..26 satisfying `n≡2(mod 3)`. Every one passes the *local* pair sieve at certified prime 3: `n≢0 (mod 3)` and `n+2≢0 (mod 3)`. This does not assert that both integers are prime.

Interchange the two endpoints by the affine involution `n↦−n−2(mod 27)`. On the centered representation this is exactly **(y,z)↦(−y,−z)**. Consequently, the nine local candidates form **one fixed point and four two-point orbits**, giving five classes. This is a genuine mathematical use of the pre-existing inner two-axis C₂ quotient; it is not a 5-D4-irrep or Monster representation identification.

New source-written Agda owner: `TwinPrimeThreeAxisLocalThreeOrbitExact`, including all nine exact representative cases, both endpoint mod-3 tests, the affine swap identity, original Ibrahim inner inversion transport and the real `LocalPairSurvives` predicate conditional on a certified modulus-3 axis.

**Important counterexample:** centered y=−1,z=+1 gives `n=5`, while its antipode y=+1,z=−1 gives `n=20`. Ibrahim's **3×5** phase-reduced carrier identifies the two. Yet 5 starts the actual prime pair (5,7), while 20 fails even the left primality check. New `TwinPrime369IbrahimQuotientBoundaryExact` uses the existing generic `ConsumerCollision` theorem to prove that **the bare 3×5 quotient cannot determine the true twin-prime consumer**. Its companion reuses the exact global antipodal plus dependent-orientation residual codec to reconstruct all three original axes.

## C. New positive finite arithmetic correspondence: 270 wheel

For the genuine local arithmetic filter over certified prime moduli **2,3,5**, the period 30 has exactly **3** pair-surviving residues (11,17,29). Over period `270=27×2×5=9×30`, exactly **27** distinct residue representatives survive. Their *affine* endpoint-swap C₂ action `n↦−n−2(mod270)` has one fixed point `269` and thirteen two-cycles. The count and C₂ structure match the global antipodal ternary cube.

This time there is an **explicit arithmetic map**, not merely a count:

```text
d(−1)=0, d(0)=1, d(+1)=2
encode(x,y,z) =
  (41 + 108·d(x) + 30·d(y) + 90·d(z)) mod 270
```

The new `TwinPrimeTernary270AffineCRTCodecExact` enumerates the **27 inverse lookup cases**, proves a source-written decode-after-encode equation for each of the 27 ternary points, proves each arithmetic code passes the **real certified** prime-2/3/5 local predicates (when supplied actual certified axes), and establishes that globally negating all three trits satisfies

```text
(encode(x,y,z) + encode(−x,−y,−z) + 2) mod 270 = 0.
```

This is an explicit C₂-equivariant **finite injection and candidate-sieve-preserving code**. The new `cubeToWheel270Injective` theorem derives injectivity from the 27-case left inverse, `cube270GlobalAntipodeInvolutive` proves the true order-two action, and `wheel270CentreCodeIs269` with `wheel270CentreFixedByAntipode` identifies the arithmetic and geometric fixed centre. The independent exhaustive Python check additionally verifies its image equals all 27 arithmetic survivors `n∈[0,269]`; the **Agda file does not yet claim this all-residues coverage theorem**. It does not construct the general coprime CRT inverse E05–E08 or an analytic twin-prime correlation.

The local Python probes `scripts/check_twin_prime_369_ibrahim_local_orbits.py` and `scripts/check_twin_prime_369_affine_270_crt.py` ran independently (the latter from a materially equivalent local copy) and passed all enumerated residue, inversion and 3×3×3 geometry checks. The independent uploaded prior audits `audit_fracprime_local.py` and `audit_sieve_local.py` also reran successfully: 20,000 numeric/valuation steps and 2,703 finite arithmetic witnesses. **None is a successful Agda kernel check.**

## D. Pareto / snowball / Ibrahim decision frontier

- **Reuse:** the typed cube, original C₂ and dependent residual codecs, source-owned Ibrahim 3×5 phase quotient, actual `CertifiedPrimePairModulusExact` arithmetic sieve and generic `ConsumerCollision/ConsumerSufficient`. Do not duplicate upstream action or proof code.
- **Positive transport:** a finite **mod-270** C₂ map is genuinely established by explicit arithmetic. Preserve its proof premises and the 27-element scope.
- **Negative transport:** the 3×5 phase quotient provably loses enough information to distinguish the actual twin-start answers at 5 and 20. Its five-orbit count is not a complete arithmetic classifier.
- **P1 next proof:** use the existing Fin / counting and period owners to prove in Agda that the image of the 27-code is **all** certified 2/3/5 survivors modulo270, not merely 27 injected examples. Current Python exhaustive confirmation is insufficient for a kernel proof.
- **P2 next proof:** source-level numeric ↔ prime-valuation general first-applicable semantics and concrete signed FRACTRAN compiler/reachable readout, beyond the 20,000 executed steps.
- **P3 next proof:** general arithmetic coprime CRT inverse; local p−2 counts and exact survivor cardinality under arbitrary distinct prime moduli.
- **P4 research wall:** quantified correlation or other genuine information proving simultaneous arithmetic primality at distance two. DHJ Polymath8b (2014) established H₁≤246 unconditionally and H₁≤6 under generalized Elliott–Halberstam, with a parity obstruction for *purely sieve-theoretic* routes. That does not imply the twin-prime conjecture or refute all possible signed computation.

**Claim status:** these three new Agda sources are **source-written, kernel-pending**. All distinct original-source contributors retain attribution: Conway/Guy for FRACTRAN, Serre and earlier group representation mathematics, Ibrahim and the original Monster 3B/phase owner, PR #1407's finite Fourier owners, DHJ Polymath8b for analytic sieve limitations, and #1408 for the newly source-written arithmetic bridges. No protected ESD edits, no new axiom, no CI run.

## E. 270-wheel reverse coverage and coordinate decomposition

The new source-written `TwinPrimeTernary270SurvivorCoverageExact`
uses 270 bounded computational proof cases, not a bijection inferred
merely from matching cardinalities. It gives both a typed inverse
witness for each actual mod-270 sieve survivor and a successful
decoder proof. Every other residue fails one of the 2/3/5
divisibility guards by explicit contradiction.

```text
mod 2:  E(x,y,z) = 1
mod 27: E(x,y,z) = 14 + 3*d(y) + 9*d(z)    (9 choices)
mod 5:  E(x,y,z) = 1 + 3*d(x)              (3 choices)
total:  1 * 9 * 3 = 27 admissible classes in mod 270
```

This is the real separation of the three independent *geometry*
coordinates into arithmetic consumers: the outer x coordinate
specifies the mod-5 local choice; the inner y/z plane encodes a
9-element prime-power-3 local fibre. It is NOT three CRT axes with
distinct prime moduli. The earlier Ibrahim 3×5=15 phase quotient
loses information, whereas the full 3×3×3 map is injective.

A finite-completeness source theorem is different from a tested
Agda theorem. No Agda compiler/kernel receipt is available;
the 270-case Python independent check did pass. No evidence of
infinite genuine twin pairs is inferred.

### Same-cube no-promotion example

The complete 3×3×3 code point (x,y,z)=(0,+1,+1)
gives n=119. Both 119=7×17 and 121=11×11 are composite,
though n passes every 2/3/5 local pair guard. This source-written
Agda example reuses `FiniteTwinSieveFactorableLiftExact`
for genuine `Composite` witnesses and exports a refutation of
`TwinPrimeAt 119`. Hence even the **unquotiented, lossless** 27
states do not add arithmetic primality information.

## F. New strongest quotient counterexample: both candidates survive the wheel

The prior 5/20 example establishes a real collision but is outside
the mod-270 2/3/5 survivor carrier. The new separately owned
`TwinPrimeTernary270IbrahimSurvivorCollisionExact` establishes the
stronger consumer collision **inside** that survivor carrier:
`(0,-1,+1) -> 59` and `(0,+1,-1) -> 209` under the original
3x3x3 affine map; 59 and 61 are prime but 209=11×19 is composite.
Both representatives pass the local 2/3/5 guard.

The source-owned Ibrahim phase quotient retains outer x but
identifies the inner antipodal (y,z) pair, so it maps both to the
same one of its original 15 classes. The source-written
`Core.ConsumerCollision` with the existing certified Nat twin
decider proves the quotient cannot supply the actual twin-start
consumer even under finite sieve restriction. This is a
specific useful **negative** cross-pollination, not matching
numerals or a Monster 3B representation assertion.

`PrimegameTypedNumericFirstApplicableBidiExact` is an independent,
positive operational cross-pollination from the **10 original SSP
prime factors used by the 14 original Guy rules** to the inherited
first-applicable interpreter. The preservation includes ordered
prefix failure and terminal no-applicable status, not only an
unordered 14-element label set. It is source-written and does not
provide signed runtime state/action alignment.

### 2026-10-28 numeric evaluator is now *source-instantiated*

`PrimegameTypedNumericFirstApplicableBidiExact` now defines
`exactNumericNext`, `exactNumericNextIsCorrect`, and an inhabited
`concreteExactFractionEvaluator` record. The zero denominator is
rejected by `ExactFractionApplies`; for positive denominators,
Agda's stdlib quotient/remainder equations derive exact output
`next*d=n*a` from the arithmetic integrality witness. This is
not an uninterpreted evaluator axiom. The three canonical TOE roots
export `guyConcreteExactPriorityForward` and
`guyConcreteExactPriorityBackward`.

**Scope/evidence:** source-written Agda with explicit stdlib names,
not typechecked in this runtime. Local exact Python tested the
14 original Guy fractions and 20,000 integer steps; it is not the
Agda kernel. The missing A07/A08/B03/C08 frontier is now the
actual signed SSP/FRACDASH action-state simulation plus readout,
not a missing integer-division specification. No branch-only
#1414 polynomial/quintic/monodromy module was imported: #1414
correctly distinguishes its own 27-label endomorphism/S3 meanings
from cube-coordinate semantics, and no mathematical map into the
actual twin-prime correlation was established. Preserve its own
PR ownership and Ibrahim 3B boundary.

## 2026-10-28 executable Guy PRIMEGAME scanner and non-halting cut

`PrimegameTypedNumericFirstApplicableBidiExact` now has a
**source-written executable `firstApplicableNumeric`** and an
`exactFractionApplies?` decision procedure. For positive
denominator d it reuses standard-library quotient/modulus identities
to show that the integrality guard admits exactly the returned Nat
successor `(n*a)/d`; d=0 is explicitly rejected.
`firstApplicableNumericSound` connects a `just after`
computation to the *existing* FRACDASH
`FirstApplicableStep` relation. `firstApplicableNumericHalt`
connects `nothing` to the original conjunction of blocked rules.
`guyTypedExecutableStepSound` and `guyTypedExecutableHalt`
transport those receipts back to the original ten-factor SSP
representation of all 14 Guy fractions.

**Critical semantic correction:** Guy PRIMEGAME does not halt.
Its last instruction is **55/1**, applicable for every Nat n.
`guyLastRuleAlwaysApplies`,
`guyNumericScannerNeverHalts`,
`guyNumericAlwaysSteps`, and
`guyTypedAlwaysSteps` source-write this fact and an actual
selected transition for **every** natural-number state. The
obligation A09 must therefore treat emitted powers-of-two as
readout events on an ongoing trace, not termination output.

Independent locally executed Python checks:
- 270 arithmetic wheel representatives and the 59/209
  inner-antipodal consumer collision.
- 20,000 Guy states from initial 2 with all 14 instructions
  exercised, matching typed/numeric priorities and arithmetic.
- 21,000 individual numeric fraction guards, 3,048 admitted.
- 20,000 separate Nat inputs with a defined first-applicable step.

This improves A05, A06, C02's representation direction, and the
numeric portion of A09. It **does not** prove A07/A08/B03/C08 for
the signed FRACDASH machine, historical prime-enumeration
completeness, an arithmetic CRT inverse, or gap-two infinitude.
No kernel receipt, CI pass, or full signed executor proof is
reported. All new Agda terms are source-written and need an
actual pinned Agda typecheck before being promoted.

Web historical corroboration: Richard K. Guy's 1983 14-rule
version uses 15/14 plus 15/2 and 55/1. Conway's variant differs
(1/7 replaces 15/14), and must stay separate.
OEIS A267572: https://oeis.org/A267572.
No protected ESD surfaces changed. PR #1414 monodromy
objects are branch-only and independent; no same-object
Monster 3B or quintic prime-distribution claim is made.

## G. The precise (3^n+1)/2 = Stirling≤3 bridge (source-owned)

A check of the actual latest #1244 and #1275 branches found the
general normalization already SOURCE-WRITTEN in
`AlexanderHornedS3WordSignOrbitTransportExact` (#1244).
Given an (n+1)-word over the original three labels, subtract the
first letter modulo 3. Global C3 translation disappears and every
S3 reflection becomes simultaneous negation of the remaining n
coordinates. Its explicit signed section and translation proof give
the mathematical orbit-set bijection
`T^(n+1)/S3 ≅ T^n/C2` for all n≥0, once a first position is chosen.
The left quotient is set partitions of n+1 positions into ≤3
blocks: restricted-growth patterns from the independent #1275
Zipf/Heaps owner. The right count is
`r_n = 1+(3^n-1)/2 = Σ_{k=1}^3 S(n+1,k)`.
Exact local enumeration confirmed n=0..6: 1,2,5,14,41,122,365.
The #1244 signed normalization has no independently observed Agda
kernel receipt and does not yet implement a formal arbitrary-n
quotient equivalence type; see Q01–Q24 in the completion matrix.

**Strongest sound arithmetic transport / no-go:** #1408's
`TwinPrimeTernary270IbrahimSurvivorCollisionExact` now proves
`globalAntipodeSends59To209` and a real
`globalFourteenOrbitLosesTwinConsumer`. Both 59 and 209 survive the
2/3/5 local wheel, and occupy the same global sign class; 59,61
are prime while 209=11*19. Thus the 14 equality-pattern/sign
classes do NOT determine true twin-primality after the 270-wheel
bijection. The dependent orientation residual is indispensable for
that consumer. This is the required negative, non-fabricated
Pareto/Ibrahim cross-pollination; original Monster 3B proof
ownership is untouched.

The #1244 native invariant fields remain a DIFFERENT carrier.
Their rank r_n counts sign orbits, whereas C3-valued field
configurations have cardinality `3^(r_n)`. Conjugacy S3 on
endomorphism tables, S3 permuting word positions, S3 globally
relabeling values, and S3 acting on original horn sectors are
NOT interchangeable. No general CRT/prime correlation follows.
