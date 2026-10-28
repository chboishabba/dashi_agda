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

This is an explicit C₂-equivariant **finite injection and candidate-sieve-preserving code**. The independent exhaustive Python check additionally verifies its image equals all 27 arithmetic survivors `n∈[0,269]`; the **Agda file does not yet claim this all-residues coverage theorem**. It does not construct the general coprime CRT inverse E05–E08 or an analytic twin-prime correlation.

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
