# Twin-prime / bounded-gap intake: exact reuse and remaining proof obligations

Date: 2026-10-28. Status: **finite Agda source written; no Agda kernel receipt**.

## Request and source identity

The user-supplied Veritasium transcript covers the twin-prime conjecture, Brun's sieve, Hardy–Littlewood pair heuristic, GPY weights, Zhang's smooth-modulus breakthrough, Maynard/Tao's multidimensional sieve, and Polymath8. It is **pedagogy**, not a substitute for the papers.

Primary theorem roots and distinct source ownership:

- G. H. Hardy and J. E. Littlewood, *Some Problems of 'Partitio Numerorum'; III*, Acta Mathematica 44 (1923). The prime-pair asymptotic is conjectural, not a lower bound.
- Viggo Brun, early twentieth-century sieve and almost-prime work. The Brun sieve does not prove infinite twin primes.
- D. A. Goldston, J. Pintz and C. Y. Yıldırım, *Primes in tuples I*, Annals of Mathematics 170 (2009). Small normalized gaps, not a finite absolute bound.
- Yitang Zhang, *Bounded gaps between primes*, Annals of Mathematics 179 (2014), 1121–1174, DOI [10.4007/annals.2014.179.3.7](https://doi.org/10.4007/annals.2014.179.3.7). Initial unconditional finite bound below 70,000,000.
- James Maynard, *Small gaps between primes*, Annals of Mathematics 181 (2015), 383–413, DOI [10.4007/annals.2015.181.1.7](https://doi.org/10.4007/annals.2015.181.1.7). H1 <= 600, Hm finite for every m; H1 <= 12 under Elliott–Halberstam.
- DHJ Polymath, *Variants of the Selberg sieve, and bounded intervals containing many primes*, Research in the Mathematical Sciences 1, 12 (2014), DOI [10.1186/s40687-014-0012-7](https://doi.org/10.1186/s40687-014-0012-7). H1 <= 246 unconditionally; H1 <= 6 under generalized Elliott–Halberstam.
- OpenAI, *Improved short gaps between primes*, preprint (30 August 2026), accompanying [PrimeGaps186](https://github.com/openai/PrimeGaps186). Reported H1 <= 186 via DHL[40,2] and an admissible 40-tuple of diameter 186. **Lean is conditional on three declared project axioms**: rank-three hyper-Kloosterman bound, rank-two Kloosterman correlation, and 104 outer/45 inner physical-integral inequalities plus three caps. The cited first two estimates have independent literature roots; the numerical package is checked separately. The source states self-assessed, not independent human semantic review.
- Julia Stadlmann, *Bounded gaps between primes*, preprint (31 August 2026), [arXiv:2608.31126](https://arxiv.org/abs/2608.31126). Independent H1 <= 240.
- [Axiom Math PrimeGapsLib](https://github.com/AxiomMath/PrimeGapsLib) provides substantial Lean prior art for the Maynard/Polymath8 machinery and separates theory from the finite numerical certificate. Its claims and proof status are its authors' responsibility.

The source chronology does **not** turn a conjecture into a theorem. H1 = 2, equivalently infinitely many twin-prime pairs, remains open.

## Existing DASHI source authority: use, do not duplicate

- [PR #128](https://github.com/chboishabba/dashi_agda/pull/128), merged: `DASHI.Analysis.PrimeCountingFunction`, `NatPrimeCountingInstance`, `PrimeCountingAlgorithms`, `PrimeCountingEstimateContracts`. These own finite decidable prime enumeration, exact counting, and clearly separated analytic contracts.
- `DASHI.Arithmetic.PrimeModSixSieveExact`: constructive prime >3 mod-6 dichotomy; source lineage Hardy–Wright.
- `DASHI.Arithmetic.SixWheelSieveCountExact`: finite six-residue carrier and exact survivor partition.
- `DASHI.Arithmetic.SixWheelCRTExact`: arithmetic residue map to moduli 2 and 3 and explicit excluded-class impossibility.
- `DASHI.Arithmetic.FinitePrimeProductSieveExact`: product-coordinate finite survivor counts, **not** mislabeled as full arithmetic CRT.
- Existing canonical `DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact` remains the original cross-domain governance/ownership source. No Monster 3B object or claim is changed.

No dedicated twin-prime theorem or Maynard bounded-gap machinery was located on searched current-master code paths, or in the targeted twin-prime PR search. Searches are not proof that no historical branch contains it.

## This branch: exact new scope

- `DASHI.Arithmetic.TwinPrimeSixWheelExact` defines the explicit +2 rotation of six residues.
- `shiftTwoThreeTimes` proves that applying the rotation three times returns the original residue.
- `PairWheelSurvivor` consumes *existing* CRT nonzero-residue witnesses at both offsets.
- `r5PairSurvives` and `pairSurvivorMustBeR5` prove the **finite exact** statement: a mod-6 starting residue allows both n and n+2 to avoid 2 and 3 exactly when the starting residue is 5.
- `primeAboveThreeWheelClass` reuses the prior constructive prime mod-6 result. A general arithmetic transport of `Nat` modular divisibility into `PairWheelSurvivor` is **not** established by this module.
- `TwinPrimeAt` and `TwinPrimesInfinitelyOften` are definitions/specifications, not witnesses.
- `BoundedPrimePair` counts two primes within a positive bounded shift, without asserting they are consecutive. `twinInfinitudeImpliesBoundedPairsTwo` proves an implication **from an assumed infinitude witness**. It neither creates that witness nor establishes the 186 theorem.
- `scripts/check_twin_prime_six_wheel_finite.py` verifies all six cases, repeated finite blocks, bounded twin pairs, and a concrete survivor that is composite (35). Exact integer computations do not establish infinitude.

This is intentionally an elementary finite sieve rather than an uncredited port of Lean or a synthetic analytic proof.

## Max-cut / Pareto / snowball / Ibrahim proof frontier

| Priority | Exact obligation | Existing source / reuse | Promotion gate |
|---|---|---|---|
| P0 | Prove finite +2 CRT pair classification | SixWheelCRTExact; SixWheelSieveCountExact | Type-check new Agda module |
| P1 | Connect `Nat` modulus to wheel and prime >3 | PrimeModSixSieveExact; NatPrimeCountingInstance | Actual transport theorem, not finite examples |
| P2 | Finite admissible k-tuples and CRT local-factor products | FinitePrimeProductSieveExact plus real CRT arithmetic | All-prime quantified admissibility and tuple certificate |
| P3 | Weighted >1 overlap lemma with nonnegative weights | PrimeCountingAlgorithms finite sums | Exact lemma and objective normalization |
| P4 | Bombieri–Vinogradov and distribution in progressions | PrimeCountingAnalyticBridge (contract only), AxiomMath prior art | Source theorem plus faithful Agda translation |
| P5 | Maynard/Polymath sieve, large-moduli refinements | AxiomMath PrimeGapsLib; OpenAI PrimeGaps186 | Recheck assumptions, dependence graph, parameter calculus, numerical certificate |
| P6 | Bridge two-prime k-tuple occurrence to bounded **consecutive** gap | explicit admissible tuple + bounded interval | Syntactically exact theorem; kernel receipt |

**Cut rule:** do not attempt P4–P6 by inventing generic postulates and presenting conditional corollaries as unconditional theorems. The finite sieve's ~1/6 survivor density is not a twin-prime density and supplies no infinite lower bound. In particular, 35 and 37 pass the mod-6 screen but 35 is composite.

**Attribution rule:** distinguish original historical mathematics, inherited Agda theorem ownership, source-written Agda, executed Python, externally published Lean with axioms, and this repository's kernel verification. Original 2026 claimed 186 bound belongs to OpenAI / GPT-6 Astra and cited mathematical predecessors, not DASHI. Keep the repository's Ibrahim Monster 3B claims in their original ownership lane. No numerical, spectral, moonshine, or Monster fingerprint is evidence for a same-object prime representation.

## Evidence and validation

- Local exact Python run on 2026-10-28: six/six wheel cases, five block sizes, 1,223 twin-pair starting positions in 4..100000, and composite survivor 35: **passed**. No random inputs.
- New Agda source was written through GitHub connector and should be checked using the pinned repository Agda toolchain. **Agda type-check not executed in this environment**.
- The new module is imported into the arithmetic aggregator and all three canonical TOE roots. No ESD surface, upstream theorem owner, or independent Lean file is edited.
- External 186 Lean checks and physical-integral computations were **not rerun**. Do not transfer their check status to this Agda branch.

Run on a checkout of this branch:

```sh
python3 scripts/check_twin_prime_six_wheel_finite.py
agda -i . -i <YOUR_PINNED_STANDARD_LIBRARY_PATH> DASHI/Arithmetic/TwinPrimeSixWheelExact.agda
```

The second command is illustrative: use the repository's pinned preflight/CI setup for the actual Agda invocation. A syntax/preflight check or Python success does not replace the Agda kernel.

## 2026-10-28 cross-repository reuse audit (Veritasium source clarified)

The user identifies the video **Veritasium, “We're 99.9% sure this pattern is true, but no one can prove it”**, [YouTube 8HBDE-msUjw](https://www.youtube.com/watch?v=8HBDE-msUjw), published 14 June 2026, as the explanatory source. The transcript is the motivation. The historical mathematical papers above remain independent theorem owners.

### BIDI search findings: do not overclaim absence

- `dashi_agda/DASHI/Biology/SignedSSPFRACTRANWeaveExact.agda`: fifteen typed SSP prime lanes, balanced signed valuations, numerator/denominator instructions, and machine-oriented semantics. Those fifteen primes are exactly 2,3,5,7,11,13,17,19,23,29,31,41,47,59,71. This is a **fixed finite vocabulary**, not the set of all primes or the first fifteen primes.
- `DASHI/Programmes/FRACDASHPairedPrimeActivityExact.agda`: paired-prime **tag/register** activation yields the existing first-applicable step theorem under explicit activity/applicability witnesses. Paired tags are NOT the mathematical statement that two Nat primes differ by 2. Its canonical boundary flags concrete Nat divisibility iff active-tag as **not closed**. Historical donor: merged [PR #636](https://github.com/chboishabba/dashi_agda/pull/636); source ownership remains with the existing FRACDASH macro and Agda compiler authors.
- `DASHI/Programmes/FRACDASHNumericInterpreterTargetExact.agda`: generic deterministic first-applicable rule, conditional on prefix-blocked and intended-applicable certificates.
- `DASHI/Combinatorics/FractranCOL.agda`: five prime lanes [2,3,5,7,11], fuelled finite evaluation and **termination as a supplied axioms record**, not an unconditional prime theorem.
- `DASHI/Combinatorics/SSP15FractranCompression.agda` / `FractranComputationEquivalence.agda`: explicit simulation, residual and compression contracts, not an automatic arithmetic same-object identity.
- `DASHI/Analysis/RiemannSSP15ProducerMarkedSignedFRACTRANExact.agda`: explicit result that signed FRACTRAN execution **does not create an analytic identity**. Reuse this non-promotion precedent.
- `DASHI/Mathematics/NumberTheory/PrimeGap2026ClaimAuditExact.agda` / `PrimeGap2026SourceAcquisitionExact.agda`: source-bound an announcement concerning unusually **large** prime gaps (Lichtman/Alexeev), *not* the bounded **small** gap theorem in Zhang/Maynard/Polymath/OpenAI 186. Original source acquisition gate is not altered or promoted.
- `dashifine/newtest/primes_krr.py`: empirical kernel-ridge-regression learning of divisibility / p-adic valuations. Predictions and finite MSE metrics are not prime predicates or proof objects. `dashifine/newtest/triality_stack.py` provides CRT-**like** composite phase experiments rather than a certified number-theoretic CRT.
- `dashitest/docs/valuation_primes_plan.md`: a proposed full valuation vector, largest prime power and ultrametric distance benchmark; it is a *plan*, not a proved interpreter or complete sieve. `dashitest` has no GitHub code-search index in this audit; its directly fetched README and plan were inspected. Do not equate missing code-search hits with absence.
- Original upstream CRT and prior arithmetic owners: merged [PR #128](https://github.com/chboishabba/dashi_agda/pull/128), `SixWheelCRTExact`, `FinitePrimeProductSieveExact`, and `PrimeModSixSieveExact`. Existing `FinitePrimeProductSieveExact` proves **single-number** ∏(p-1) survivors, not automatically twin-pair ∏(p-2) survivors. General arithmetic CRT still needs pairwise-coprime and congruence witnesses.

### New explicit reuse on this PR

`DASHI/Arithmetic/TwinPrimeFRACDASHReuseExact.agda` imports the existing wheel and FRACDASH theorem owners. `TwinWheelActivityBridge` requires evidence that the chosen machine's active tag actually represents the paired wheel-survival condition. **It does not construct a concrete machine bridge.** Given such a bridge, `bridgeChoosesFirstApplicable` reuses `activityReceiptYieldsFirstApplicableStep`, while `bridgeActivationForcesResidueFive` reuses `pairSurvivorMustBeR5`. This supplies the correctly typed same-object *obligation* rather than identifying unrelated uses of “paired primes”. It is exposed at all three TOE roots. No satellite, ESD or underlying proof owner is modified.

`scripts/check_twin_prime_ssp15_crt_finite.py` independently checks local pair survival for every SSP15 prime (one excluded residue at 2, two at each odd prime), and the exact finite CRT count for prefixes up to 2·3·5·7·11·13=30030. The surviving count is **1485**, equal to ∏(p-ν_p) with ν_2=1, ν_p=2 otherwise. This is finite integer evidence; no arbitrary-list Agda CRT theorem is claimed. The test also proves by finite counterexample that SSP15 does not include 37,43,53,61,67. Both 2279=43·53 and 2281 avoid the entire SSP15 sieve, although 2279 is composite. Thus SSP15 screening alone is not even a complete primality decision procedure in this range, much less a twin-prime infinitude theorem.

**Max-cut:** (1) Agda kernel-check these modules; (2) discharge concrete arithmetic-to-tag encoding and the missing-primes/general-prime CRT transport; (3) transfer weighted-sieve threshold and analytic distribution results from exact source statements. Reuse the 2026 external Lean work with its declared assumptions. No Monster character fingerprint, numerical correlation, or signed-machine execution may bypass the original Ibrahim attribution and same-object boundaries.

**Executed local exact checks:** both finite Python scripts passed on 2026-10-28. No Agda kernel run, GitHub CI pass, or external Lean recheck is claimed.

## 2026-10-28 P7: SSP-prime generation / arbitrary-modulus symmetry max-cut

**User hypothesis, precisely scoped:** we might generate prime axes from the SSP construction and then use symmetry to calculate new moduli. Existing formalism verifies a related but stricter two-stage route:

1. `DASHI.Geometry.SSP369TreeAutomorphism.actionPreservesPrimeLane` is an exact proof that an SSP unit/refinement action preserves its original *prime label*. Thus an SSP/C3/369 symmetry orbit on a **fixed** lane does **not** generate a new arithmetic prime. Nor do the Stage12 "prime successor" candidate labels automatically carry `Data.Nat.Primality.Prime`.
2. `DASHI.Interop.PrimeSuccessorWitness` contains `candidateOnly=true` with universal-prime promotion blocked. `DASHI.Foundations.MixedPrimeResolution` already provides a third factor axis `2^a 3^b q^c` but explicitly requires `q` primality and pairwise coprime witnesses for CRT. These are the strongest correct existing prime-extension donors, not missing architecture.
3. `DASHI.Analysis.NatPrimeCountingInstance` supplies the existing proof-bearing `Data.Nat.Primality.prime?` and exact prime count. `DASHI.Arithmetic.PrimeModSixSieveExact` already proves that every prime >3 belongs to residues 1 or 5 modulo six. That theorem gives a complete **candidate family**, not a primality certificate for every candidate.
4. `DASHI.Arithmetic.CertifiedPrimePairModulusExact` (new) represents each additional prime as `CertifiedPrimeAxis` carrying `Prime (suc c)`; `certifyCandidate` uses the same proof-bearing Nat decider. `LocalPairSurvives` tests actual `n % p != 0` **and** `(n+2) % p != 0`. The decider `localPairSurvives?` is exact for every certified modulus, not fixed to SSP15. `AllPairSurvive` and `allPairSurvive?` combine arbitrary finite lists; `extendedSieveRetainsEarlier` proves adding a prime does not lose previous restrictions.
5. The exact Agda source lemmas `localModPeriod`, `localOffsetPeriod`, `localPairPeriodic`, and `localPairPeriodicBack` formalise *residue symmetry* under `n -> n+p` for any certified prime `p`. They use the stdlib `[m+n]%n≡m%n` theorem, not an SSP-label substitution. `sspAddressSymmetryPreservesPrime` directly reuses the existing SSP theorem and blocks mixing those two actions.
6. `Product.ResidueCoordinates` / `residueProductEncodeDecode` reuse the existing arbitrary-list mixed-radix codec. The **arithmetic** CRT forward map `canonicalPrimeCRTForward` projects actual `Fin (M*p)` residues to `Fin M × Fin p`. The new `ArithmeticPrimeCRTStep` requires `Coprime M p`, a reconstructed inverse, and both inverse laws. No such general Agda CRT inverse was silently provided or mislabeled complete. This matches existing `DASHI.Biology.DecimalCRTResolutionExact` precedent, which separates a cardinality codec from a coherent CRT inverse.

### Executed numerical cross-check

`scripts/check_twin_prime_arbitrary_crt_symmetry.py` uses the mod-6 candidate generator, exact integer trial-divisor primality certification, and the constructive arithmetic CRT extension

`x = r + M * (((t-r) * M^{-1}) mod p)`

for coprime `M,p`, with asserted reductions modulo each factor, bounds, absence of duplicate residues, and equality with direct exhaustive sieving. It checks:

- Every generated prime through 251 agrees with an independent full candidate scan. Composite numbers 6k±1 are rejected.
- Twelve certified prime axes through 103 absent from SSP15: 37,43,53,61,67,73,79,83,89,97,101,103.
- Modulus-period symmetry for all primes through 103.
- CRT repeated extension through modulus 30030 has 1485 pair survivors; direct enumeration agrees.
- Extension from six-wheel by primes 37 and 43 yields modulus `6*37*43=9546`, with exactly `(37-2)*(43-2)=1435` pair survivors; direct enumeration agrees.

**Exact finite runtime checks executed 2026-10-28.** A Python primality test and an arithmetic CRT regression are source-written executable checks, *not* Agda proof certificates, a general analytic prime asymptotic, or evidence of twin-prime infinitude. The new Agda declarations have not been kernel type-checked in the current environment.

### Updated Pareto/Ibrahim proof frontier

- **P0 finite mod + candidate**: new certified arbitrary prime-axis type, executable local pair decider, and one-axis period/symmetry proofs are source-written and wired into the TOE graph. Agda kernel run remains required.
- **P1 global CRT**: the missing exact Agda proof is a reconstructed inverse satisfying `ArithmeticPrimeCRTStep` for coprime `M,p`. In the canonical source it is a *typed uninhabited obligation*, not the already-owned mixed-radix codec.
- **P2 CRT pair count**: general local count `p-2` for `p>2`, with special `p=2` factor 1; derive finite-product counts on the arithmetic CRT representation, not by relabeling one-number `p-1` counts.
- **P3 prime completeness**: check the source decision procedure against all divisors through `sqrt(n+2)` and the existing complete Nat prime enumeration; a finite mod wheel alone does not prove either endpoint prime.
- **P4 analytic parity barrier**: sieving local congruence classes alone cannot establish infinitely many twin primes. Maynard/Polymath finite-gap methods require global distribution inputs; the bounded-gap best-known source proposal `PrimeGaps186` has three explicit Lean axioms. Preserve source authorship, conditionality and independent numeric receipts. Consult Axiom Math `PrimeGapsLib` for Lean method structure rather than claiming new proof ownership.
- **P5 governance**: no modification to the unrelated large-gap Lichtman/Alexeev intake, to the existing Ibrahim Monster 3B proof ownership, or to ESD modules. No observed residue fingerprint, signed SSP valuation, or machine trace equals a Monster representation or a proof of the twin-prime conjecture.

Primary external URLs: [OpenAI PrimeGaps186](https://github.com/openai/PrimeGaps186), [Axiom Math PrimeGapsLib](https://github.com/AxiomMath/PrimeGapsLib), and the source work credited above. `CRTPeriod.agda` and `DASHI.Biology.DecimalCRTResolutionExact` already provide periodicity and CRT proof-shape donors; the new source **reuses** standard modular lemmas and retains original authorship.


### Further reuse found: the 20-prime Ogg/non-Ogg control universe

The first search missed `DASHI.Moonshine.AllPrimeRepresentationFrickeClosureExact`, which **already** collects all twenty labelled primes below 72. Its theorem `allPrimeCandidateCountIsTwenty` pairs with `nonOggPrimeCandidateCountIsFive`. The five non-Ogg control numerals are precisely 37, 43, 53, 61, and 67; these were *already in the repository*, even though the fixed Ogg/SSP15 carrier omits them. This is a critical attribution and reuse correction: we do **not** claim to discover those prime controls independently.

The inherited catalogue serves a different question: source-owned representation/Fricke/Ogg closure, with the fifteen special primes versus five non-Ogg controls. It does not prove that a chosen control automatically supplies a `Data.Nat.Primality.Prime` proof required by the arithmetic sieve. The new narrow `DASHI.Arithmetic.TwinPrimeOggControlReuseExact` directly imports the original owner and reuses its 20/5 exact finite count theorems. Its `ControlToCertifiedPrime` requires literal equality between an existing control's arithmetic numeral and a separately certified `CertifiedPrimeAxis`; no implicit representation-to-primality promotion.

In summary, the user hypothesis splits into **a finite pre-existing 20-prime representation catalogue** and **a general prime candidate/certificate process**. The former is concrete prior art, the latter gives arbitrary-modulus sieve extension. The already-proved SSP369 automorphism preserves each input prime identity and therefore cannot independently generate new prime values. Explicit new moduli and genuine coprime evidence are still necessary for arithmetic CRT.

This is also why `DASHI.Arithmetic.CoprimeLayer` and `DASHI.Arithmetic.TrackedCoprimeTable` are retained as prior coprimality owners: they prove distinct tracked prime powers coprime and a product-divisibility lemma. Our generic `ArithmeticPrimeCRTStep` requires the *same standard-library `Coprime M p` type* for arbitrary axes, instead of assuming it from distinct SSP labels. The general arithmetic inverse remains an open proof target.

### Exact-head kernel CI requested, not yet observed

The PR now has a separate `pinned-agda` GitHub Actions job, modelled on the existing Math2026 and J369 pin and using the repository's `scripts/run_agda29_parallel_check.sh`. It checks the four new Agda modules independently of the Python finite regression. This is a **scheduled CI instruction in committed source**, not a statement that the job ran or passed. Promotion to kernel-verified requires the exact PR head to produce a successful job receipt, followed by checks of the three canonical TOE aggregate imports.

The local running container does not have `agda` installed. Both previous finite scripts and the newly added arbitrary-prime/CRT Python script were executed in this session and passed; their output must not be substituted for the Agda kernel.

## 2026-10-28 continuation: arbitrary-prime product period, symmetry, and exact 186-tuple prior art

This tranche follows the existing proof graph, rather than strengthening the earlier PR's unverified CRT inverse claim.

### New theorem owner and proof boundary

`DASHI.Arithmetic.CertifiedPrimePairPeriodExact` reuses `CertifiedPrimePairModulusExact.LocalPairSurvives`, `AllPairSurvive`, and Agda stdlib `Data.Nat.DivMod.[m+kn]%n≡m%n`. The source defines:

- `localKPeriod`, `localKOffsetPeriod`, `localKPeriodic` and `localKPeriodicBack`: the paired residue predicate is invariant in both directions under adding any natural multiple `k * p`, for each certified prime modulus `p`.
- `CommonPeriod` (list-indexed, proof-carrying): for each axis, the candidate period `M` is witnessed as `k * p`. This is a *modular arithmetic* obligation, not a claim of CRT reconstruction or primality.
- `scaleCommonPeriod` and `productIsCommonPeriod`: construct the period witness for the **product of any finite list** of certified prime moduli. No pairwise coprimality is needed for periodicity. Duplicates are allowed.
- `allPairCommonPeriodic`/`Back` and `allPairProductPeriodic`/`Back`: transport the *entire finite pair sieve* in both directions by its product period, reusing the local predicates and explicit equality transport.
- `swapFirstTwoPrimeFilters`, `swapFirstTwoFiltersInvolution`, `duplicatePrimeFilterErases`/`Inserts`, and `duplicatePrimeFilterRoundTrip`: exact commutative/idempotent filter symmetry. These are the sound meaning of "further mod()" operations that reorder or repeat constraints. **They cannot generate a new arithmetic prime value from the same SSP label**.

This is logically independent of the outstanding `ArithmeticPrimeCRTStep`, which requires `Coprime M p` plus a genuine inverse of the canonical residue map. A product period is **not** a CRT isomorphism. Similarly, finite filter order/idempotence is **not** a Monster same-object action.

**Agda status:** new source-written declarations, with no source-declared holes, postulates or unsafe flags in the new modules. The runnable pinned-Agda workflow was updated to target the new owner; **no successful kernel receipt has been observed**.

### Independent executed finite regression

`scripts/check_twin_prime_periodic_sieve.py` checks exact integer invariance across nine finite prime lists, including repeated 2 and 3 (deliberately **non-coprime** axes), several multiplier periods, and filter commutation. For pairwise distinct primes it compares full-period survivors with `prod(p - ν_p)`; for duplicate moduli it checks multiplicity scaling over the LCM rather than falsely multiplying local survivor counts. It also retains composite survivor 2279. **Locally executed and passed** on 2026-10-28.

### 2026 short-gap literature: sourced tuple, not borrowed theorem ownership

The public [OpenAI PrimeGaps186](https://github.com/openai/PrimeGaps186) source and [Challenge.lean](https://github.com/openai/PrimeGaps186/blob/main/Challenge.lean) give a particular set `H` of 40 distinct nonnegative shifts with endpoints 0 and 186. `scripts/check_prime_gap_186_tuple_admissibility.py` transcribes this finite data **with source attribution** and independently checks that all 12 primes `p ≤ 40` omit at least one residue class. For every prime `p > 40`, cardinality `|H| = 40 < p` gives an omitted class, independent of the bounded numerical sample. The script additionally samples primes through 256 as a regression, not as a substitute for the cardinality proof.

Observed missing residue witnesses (one per prime): `2→1, 3→1, 5→4, 7→3, 11→7, 13→5, 17→11, 19→8, 23→16, 29→9, 31→4, 37→3`. The separate Python test passed. It establishes the **elementary admissibility of the supplied finite tuple** in ordinary mathematics, but is not a Lean/Agda kernel formalisation of that property. It does not verify `DHL[40,2]` or a gap bound.

Axiom Math's [PrimeGapsLib](https://github.com/AxiomMath/PrimeGapsLib) explicitly separates `PrimeGapsTheory` from `PrimeGapsCert`. OpenAI's 186 formalisation separately declares three analytic/numerical input axioms: the rank-three Kloosterman estimate (classical Katz/Deligne source), the rank-two correlation estimate (Fouvry–Kowalski–Michel), and a numerical physical-integrals/caps package. The conditional Lean proof is **not** imported as an unconditional DASHI theorem. The tuple belongs to the OpenAI source and retains third-party acknowledgments including Axiom Math.

### Cross-PR Pareto/Ibrahim source checks

- [PR #1260](https://github.com/chboishabba/dashi_agda/pull/1260) contains factorial CRT examples and a p=101 control outside SSP15. Its finite certificates are not a general inverse for `Fin(M*p)`.
- [PR #1139](https://github.com/chboishabba/dashi_agda/pull/1139) uses `RadixValuationStageBridge` and signed SSP/FRACTRAN climbing-gym semantics. Its p-adic addresses and wreath actions retain the chosen prime and do not construct a proof of infinitely many arithmetic twin-prime pairs.
- [PR #1334](https://github.com/chboishabba/dashi_agda/pull/1334) explicitly forbids search priority, semantic similarity, external eigen patterns, and numeric matches from being promoted to proof or Monster same-object recognition. This PR reuses those governance principles, without copying their theorem owners.
- Merged [PR #636](https://github.com/chboishabba/dashi_agda/pull/636) is the original source for the finite FRACDASH first-applicable machine interface; merged [PR #128](https://github.com/chboishabba/dashi_agda/pull/128) owns prime enumeration and counting.
- Retain historical ownership of Brun, Hardy–Littlewood, GPY, Zhang, Maynard, Tao, Polymath8, Ogg/Duncan–Ono, Deligne/Katz, Fouvry–Kowalski–Michel, and original Agda/Lean contributors. The Ibrahim Monster 3B results stay in their prior distinct proof lane. No new Monster representation is claimed.

### Next true cut

1. **Kernel**: type-check this PR's five Agda theorem owners at the exact head and the three TOE roots. Fix actual elaboration failures rather than deriving status from source text or Python scripts.
2. **Finite arithmetic CRT**: instantiate `ArithmeticPrimeCRTStep` from coprimality with a computed inverse and both round-trip laws; use existing `CoprimeLayer` where it applies and general Nat coprimality otherwise.
3. **Local pair count**: prove `p - 2` for odd certified `p` and one residue at 2 in Agda. Lift that via a **true** CRT isomorphism to the exact pair-survivor product over distinct prime moduli; explicitly handle duplicate axes.
4. **Analytic**: keep any `DHL[40,2]` or `H_1 ≤ 186` theorem conditional until every external analytic and finite-certificate assumption is discharged. The elementary finite sieve alone cannot provide twin-prime infinitude.

**Status:** five local Python scripts passed; new Agda source checks are static only; no kernel or CI success asserted. Do not mark this PR merge-ready on source/static evidence alone.
