# Signed SSP / FRACDASH → arithmetic twin-prime max-cut

Date: 2026-10-28. Working branch: `feat/twin-prime-six-wheel-bounded-gap-reuse-20261028`.
Working PR: https://github.com/chboishabba/dashi_agda/pull/1408

## Source genealogy / proof authority

- John H. Conway, *FRACTRAN: A Simple Universal Programming Language for Arithmetic*, in T. M. Cover and B. Gopinath (eds), *Open Problems in Communication and Computation*, Springer (1987), pp. 4–26. DOI root https://doi.org/10.1007/978-1-4612-4808-8. The original PRIMEGAME prime-enumeration algorithm and general computation theorem belong to Conway and the original contributors.
- Richard K. Guy, *Conway's Prime Producing Machine*, Mathematics Magazine 56(1), 1983, pp. 26–33, DOI https://doi.org/10.2307/2690263. The **15-fraction Guy variant** uses both `15/14` and `15/2`; do not silently replace it by the distinct 14-fraction `1/7` variant.
- FRACDASH source: https://github.com/chboishabba/FRACDASH, especially `BRIDGE_CORRECTNESS.md`, `formalism/GenericMacroBridge.agda`, `formalism/BridgeInstances.agda`, `fractran/src/Fractran.hs`, and `fractran/src/Compiled.hs`. The source already separates the signed IR in `Z^n` from the nonnegative integer FRACTRAN execution, uses priority first-applicable semantics, and supplies paired-prime state-tag macros. Those are **register semantics**, not arithmetic prime generation.
- In-repo owners `DASHI.Biology.SignedSSPFRACTRANWeaveExact`, `DASHI.Programmes.FRACDASHNumericInterpreterTargetExact`, `DASHI.Programmes.FRACDASHPairedPrimeActivityExact`, `DASHI.Arithmetic.PrimeModSixSieveExact`, `DASHI.Arithmetic.FinitePrimeProductSieveExact`, `DASHI.Arithmetic.CertifiedPrimePairModulusExact`, and `DASHI.Arithmetic.CertifiedPrimePairPeriodExact` retain individual proof ownership. Respect the previous Ibrahim Monster 3B and Pareto/snowball owners (including PR #1334). No Monster same-object inference follows from signed or modulo syntax.
- Classical arithmetic / sieve sources: Eratosthenes, Brun, Hardy–Littlewood (1923), Goldston–Pintz–Yıldırım, Zhang, Maynard, Tao, and DHJ Polymath8b. See the peer-reviewed Polymath8b *Variants of the Selberg sieve...* (2014); its parity analysis explicitly limits **purely sieve-theoretic** gap-two promotion. Current 2026 conditional `PrimeGaps186`/Axiom Math Lean sources do not discharge the twin-prime conjecture.

## Distinguish four actual claims

1. `Representable p`: the integer `2^p` is a valid Nat encoding, trivial for any `p`.
2. `Reachable p`: a specified initial machine actually reaches this code. Conway supplies a historical PRIMEGAME construction; the user-specific **signed SSP** emulator needs its own end-to-end compilation/reachability proof.
3. `Offset-computable p`: arithmetic macro starts at `2^p * 3^2` and executes `[2/3]` twice to `2^(p+2)`; for `p>=2`, `[1/6]` twice to `2^(p-2)`. These are exact integer calculations, independent of primality of either offset.
4. `Twin prime p`: independent certificates `Prime p` and `Prime (p+2)`. Output reachability and modulo-sieve survival are **insufficient**.

## Formal owner / current implementation

### `DASHI/Arithmetic/SignedSSPPrimeOffsetMacroExact.agda`

- `powerTwo` and numeric `plusSource/Middle/Output` and `minusSource/Middle/Output`.
- `ExactFractionStep`: both `denominator ∣ source` and `source * numerator ≡ target * denominator` are required, preventing a spurious fractional update.
- `ExactTwoStepMacro`: two witnessed exact steps.
- `plusTwoFractionMacro`: proofs for fractions `2/3`, including the denominator guards for both steps, for arbitrary `p`.
- `minusTwoFractionMacro`: proofs for fractions `1/6`, with `p=2+k` explicitly, avoiding signed/natural subtraction underflow.
- `minusStartIsPrimeEncoded`, `plusOutputHasOffsetExponent`, `minusOutputHasOffsetExponent`: arithmetic readout equations over all admissible input exponents.
- The sign annotations reuse exactly `SignedSSPFRACTRANWeaveExact.positiveMultiplicity 2` / `negativeMultiplicity 2`, their orientations and signed-negation correspondence. **This is not yet a full compiler witness from the signed IR to the whole numeric first-applicable interpreter; it proves the underlying arithmetic macro.**

### `DASHI/Arithmetic/SignedSSPPrimeOutputBoundaryExact.agda`

- `everyCertifiedPrimeHasAnEncoding`: ordinary representability, no machine run.
- `ArithmeticPrimeEmitter`: **uninstantiated** interface requiring actual reachability for every `Prime p`.
- `certifiedPrimeIsReachableWhenEmitterProved`: field projection conditional on supplied emitter; **not a universal theorem**.
- `twinPrimeInvariantUnderEqualReadout` and reverse: decoded arithmetic twin-primality cannot change under an encoding symmetry that preserves integer readout.
- `pairSieveInvariantUnderEqualReadout` and reverse: the same semantic firewall for certified arbitrary-prime local tests.
- `certifiedNeighboursAreTwinPrimes`: both independent prime certificates required.

All three canonical TOE facades now expose both theorem owners: `DASHI/EverythingTOESymmetryResolved369.agda`, `DASHI/Unifier.agda`, `DASHI/Unified/Everything.agda`. Protected ESD files remain untouched.

### Exact finite execution

`scripts/check_signed_ssp_prime_offset_macro.py` checks:

- 9 historical Conway/Guy PRIMEGAME power-of-two emissions through step 19201 (finite replay only);
- all `p=2..255` against 254 plus and 254 minus FRACTRAN macros with true denominator divisibility, two integer transitions and exact final powers;
- terminal halting (no 3 or 6 denominator factor) and underflow prevention at p=0/1;
- FRACDASH R3 signed prime-tag transport `23 → 17 → 19` as a **distinct** compiler example;
- prime 13 with composite 15 as the non-promotion example.

A materially identical local Python replay passed on 2026-10-28. The committed script and Agda modules are source written. No pinned-Agda Actions success or other kernel receipt has been verified. GitHub workflow is configured to run the new probes and compiler targets.

## All 67 lemma obligations: audit matrix

Statuses: `OWNER` = relevant preexisting theorem owner, not necessarily fully integrated; `SOURCE` = source-written, not Agda-kernel checked; `PARTIAL` = some part exists; `OPEN` = missing implementation or mathematical argument. No status here promotes an external mathematical claim.

| Phase | Individual obligations | Current interpretation |
|---|---|---|
| A. Signed interpreter (10) | A01 SSP lane identity; A02 signed-value interpretation; A03 signed canonical form; A04 register exclusivity; A05 fraction guard equivalence; A06 first-applicable determinism; A07 single-step simulation; A08 multistep simulation; A09 halt/readout integrity; A10 register-renaming invariance | A01,A04–A07 OWNER in source slices; A02,A08,A09 PARTIAL; A03,A10 OPEN |
| B. Arithmetic readout (8) | B01 carrier/output separation; B02 natural readout; B03 compiler readout correctness; B04 addition macros; B05 subtraction macros; B06 underflow guard; B07 compositional soundness; B08 output-value completeness | B01 SOURCE; B04–B06 SOURCE with numerical execution; B02,B03,B07,B08 OPEN for machine-wide compiler |
| C. Prime-generation (9) | C01 Conway program; C02 integer-to-valuation step equivalence; C03 output-marker equivalence; C04 primality soundness; C05 prime completeness; C06 ordering/distinctness; C07 unbounded continuation; C08 signed SSP compiler equivalence; C09 signed-specific advantage | C01 historic OWNER + finite regression; C02,C03,C08 OPEN; C04–C07 historical Conway result, no local kernel import; C09 RESEARCH |
| D. Both offsets (8) | D01 +2 macro; D02 -2 macro; D03 two-step execution; D04 prime-source provenance; D05 ±2 neighbourhood symmetry; D06 certified twin-pair; D07 every twin representable from source; D08 duplicate canonicalisation | D01–D03 SOURCE + executed finite; D04,D05,D07,D08 OPEN; D06 SOURCE conditional |
| E. CRT/sieve (15) | E01 certified modulus; E02 p=2 local exception; E03 odd forbidden residues; E04 p-2 count; E05 CRT reconstruction; E06 forward/inverse; E07 finite prime-product CRT; E08 pair cardinality; E09 global period; E10 filter permutation; E11 duplicate idempotence; E12 refinement; E13 real twin implies survival for sufficiently small sieving primes; E14 arbitrarily large double-composite survivors; E15 FRACTRAN–CRT commuting square | E01,E09–E12 SOURCE, E14 ordinary CRT argument + executed Python; E02–E08,E13,E15 OPEN as complete Agda theorems |
| F. Analytic bridge (9) | F01 distribution in arithmetic progressions; F02 prime-pair correlation; F03 weighted sieve semantics; F04 uniform error; F05 signed-specific quantitative gain; F06 parity-barrier discrimination; F07 positive infinitude criterion; F08 conditional bounded gap transport; F09 external axiom discharge | All OPEN research/conditional imported maths; F03,F08 partly framework-only |
| G. Conclusion/integration (8) | G01 infinitely many certified twin pairs; G02 equivalent infinitude formulations; G03 consecutiveness gap-two; G04 TOE export; G05 forbidden escape audit; G06 pinned Agda kernel check; G07 independent expert review; G08 attribution/promotion review | G04 SOURCE, G05 static scan in workflow, G08 documented; G01 genuinely unsolved, remaining OPEN |

**Max-cut order:** exact-head kernel check and repair → signed compiler/readout (A/B) → genuine Conway-to-signed-SSP reachability (C) → arithmetic CRT inverse and local p−2 counting (E) → prove a **new arithmetic distribution estimate**, not another representation identity (F) → G01 twin infinitude.

**Rigorous stopping point:** all finite modular constraints can be passed by two composite integers arbitrarily far out (previous PR #1408 counterconstruction). Therefore signed machine expressiveness, fixed-product periods, and exact finite CRT alone cannot discharge twin-prime infinitude. The historical 2014 Polymath8b parity result provides the stronger analytic barrier to a purely sieve-theoretic approach.

## Recent PR cross-pollination and reuse policy

On 2026-10-28, recent repo PRs #1409–#1413 concern AO/PNF/evidence and reprojection rather than a prime-pair proof. PR #1407 contains optical-lattice/369 material; no prime-distribution theorem is imported from an analogy with a three-mode lattice. PR #1334 owns the contextual FRACTRAN/SSSP/Ibrahim Pareto normalization and explicitly forbids numeric coincidences or search priority from becoming proofs. PR #1139 owns signed SSP p-radix addressing; PR #636 merged the FRACDASH programme adapter; PR #128 merged the Nat counting/primality layer. This branch reuses the owners without duplicating their proofs.

Independent mathematical significance still depends on a sourced, quantified arithmetic statement that survives decoding of signed machine states. Label orientation, Monster residues or a 369 frequency fingerprint alone are insufficient, and Ibrahim's prior Monster 3B ownership remains intact.

## 2026-10-28 second reuse cut: exact finite-code coverage

The existing `DASHI.Analysis.NatPrimeCountingInstance.natPrimesUpTo` and `DASHI.Analysis.PrimeCountingFunction.primesUpTo` already provide proof-bearing finite prime enumeration, so do not write another primality engine. The new `SignedSSPPrimeOutputBoundaryExact` extends this through:
- `natPrimeAppearsAtOwnCutoff`: for every `Prime (2+n)`, that prime is a member of the existing finite list bounded by itself, proved by case-splitting `Data.Nat.Primality.prime?` and eliminating its `no` case with the supplied prime certificate;
- `encodedPrimesUpTo`: map the existing prime-list owner into `2^p` codes, without altering its prime test;
- `everyPrimeCodeAppearsAtOwnCutoff`: preserves membership through the map, for every certified prime `2+n`.

This **source-written genuine universal finite-code coverage lemma** is not the signed machine's **reachability** or **termination/prime-emission** theorem. The difference is the uninstantiated `ArithmeticPrimeEmitter.coversEveryPrime` field. Consequently update Phase C: finite arithmetic prime-code list completeness is SOURCE; actual signed-SSP FRACTRAN reachability/computational equivalence remains OPEN. The theorem targets were added to both the canonical TOE roots and the pinned source scan, but no Agda kernel success has been observed.

## 2026-10-28 third max-cut: retain arithmetic residual or lose twin primality

This pass searched the actual repository theorem owners first. No duplicate prime-counting engine, FRACTRAN interpreter, lossless SSP codec, or CRT coordinate system was constructed. Relevant older sources not covered in the first roadmap:

- `DASHI.Combinatorics.FractranComputationEquivalence` defines `SameOutcome` and conditional `FractranRepresentation`, with explicit halt, step, and whole-run preservation. Same output does not imply same trace.
- `DASHI.Combinatorics.SSP15FractranCompression` defines `SSP15ResidualCodec` and `codec-roundtrip`; a bare 15-way label is not presumed lossless. This is a stronger existing machine semantics donor than a symbolic orientation analogy.
- `DASHI.Interop.VerifiedFractranCrankPipeline` supplies a general compiler/trace/proposal separation. Reuse it for verified machine lowering; it does not construct a prime-number-theoretic distribution law.
- `DASHI.Analysis.PrimeCountingFunction` already has an abstract proof-bearing finite predicate enumerator and `primeListCountExact`.

### New conditional positive theorem

`DASHI.Arithmetic.SignedSSPTwinObservableTransportExact` reuses the above owners to show:
- **lossless SSP15 label-plus-residual round trip preserves arbitrary arithmetic readout**;
- therefore a correctly decoded lossless state preserves both the exact `TwinPrimeAt` proposition and its true finite counting indicator;
- `SameOutcome` of two concrete FRACTRAN states implies agreement of any deterministic terminal-state twin-primality observable. It proves nothing about equal traces or general source-compiler semantics.

These proofs are source-written and imported into the three canonical TOE roots. `SSP15ResidualCodec` is an uninstantiated record: the proof does not magically supply a concrete lossless SSP15 compression or an end-to-end signed prime enumerator.

### New executable prime-pair owner

`DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact` instantiates `PrimeCountingFunction.PrimePredicate` with the *real* predicate `TwinPrimeAt n = Prime n × Prime (n+2)`, using two independently proved `Data.Nat.Primality.prime?` decisions. It exposes:
- `twinPrimeAt?`, including all arithmetic small-prime exceptions;
- `twinStartsUpTo` and `twinPairCountLE`, using existing recursion;
- `twinStartListCountExact` via the existing abstract counting owner's cardinality proof;
- `certifiedTwinFromSeparatePrimeProofs` and its inverse projection.

This closes **finite arithmetic twin-start classification/counting at source level**. It does not claim infinitely many starts, or that the signed SSP runtime generates every such pair.

### New impossibility theorem for orientation-only classification

`DASHI.Arithmetic.SignedSSPOrientationTwinClassifierNoGoExact` constructs a precise counterexample. Both arithmetic values 5 and 7 have the positive signed SSP orientation, while `TwinPrimeAt 5` is true (5,7) and `TwinPrimeAt 7` is false (7,9). It proves `orientationAloneCannotDecideTwinPrimality`: *no total classifier factoring solely through the three-way signed orientation can agree with the actual twin-prime predicate on all natural numbers*. This is a finite logical no-go theorem, **not** a no-go for a full signed SSP state retaining a sufficient arithmetic residual.

Executed local Python regression `scripts/check_signed_ssp_twin_information_loss.py`: true twin starts with lower endpoint ≤100,000 are **1,224**, including (3,5). This corrects the earlier count **1,223**, which did not include all lower endpoints; there are **1,223 consecutive differences between those 1,224 starts**, a different statistic. All odd tested prime moduli had `p−2` local survivor residues, while p=2 retained exactly one. This is a bounded executable check only.

### 4B material: source-controlled triage

The repository's Monster `4B` content is a conjugacy-class / moonshine datum, not an additional arithmetic prime modulus. Established source roots include Conway–Norton (1979) for monstrous moonshine, with Wilson's class-representative work and later source tables. Its natural power-to-class map must not be identified with `p±2` arithmetic or an actual FRACTRAN prime emitter without a separate semantics-preserving map and representation theorem. Keep inherited Ibrahim Monster 3B ownership intact and treat class names, frame shapes, and prime-exponent encodings only as *source-attributed test cases for the lossless-codec boundary*, not as prime-correlation evidence.

### Next cut

1. Fix/elaborate the added Agda sources against the repository's pinned standard-library API. No kernel acceptance has been observed; do not infer it from Python scripts.
2. Supply an actual `SSP15ResidualCodec` instance for the real signed FRACDASH carrier; discharge round-trip, step, halting and run preservation using `FractranComputationEquivalence` or `VerifiedFractranCrankPipeline`.
3. Supply an actual `ArithmeticPrimeEmitter` from the concrete signed SSP initial state. Code-enumeration completeness does **not** fill its reachability field.
4. Complete arithmetic coprime CRT inverse and exact local-count theorem (`p=2` vs odd p).
5. If claiming a new twin-prime result, prove a quantitative prime-pair correlation estimate that survives decoded arithmetic and is not reducible to parity-limited sieve data. No such result was discovered in #1409–#1413 or current 4B material.

Owner status update: A03,A08,A10 (runtime compiler) remain open; B02/B03 readout now have conditional codec transport but no concrete full-machine instance; C04–C08 remain to be kernel-linked/instantiated; E02–E04 verified by finite Python but not Agda general proof; D06 and exact finite twin enumeration have source-level owners; F05 has a rigorous **orientation-only negative** special case, richer signed invariants remain research. The G01 twin infinitude target is unchanged.

## 2026-10-28 fourth max-cut: prime 2 forces exponent decoding

`DASHI.Arithmetic.SignedSSPRawCodeParityNoGoExact` establishes an exact *counterexample* to treating the integer encoding as its decoded exponent: at arithmetic prime `p=3`, Conway/Guy-style raw output is `2^3=8`, hence raw code `8 mod 2 = 0`, while decoded prime `3 mod 2 = 1`. Consequently **there cannot be a universal equality** `(2^p mod 2) = (p mod 2)`. An actual modular sieve must retain p=2 but apply it to the **decoded exponent**, not the raw FRACTRAN code. This is a critical BIDI source/target representation cut, independent of CI or optimization.

`SignedSSPOrientationTwinClassifierNoGoExact` now also contains `collidingCodeCannotDecideAllTwins`: for **any** carrier and encoding that identifies 5 and 7, no deterministic classifier of that code alone can agree with true arithmetic `TwinPrimeAt` for all naturals. The previous orientation-only theorem is a genuine specialization of this general quotient no-go. This is why the prior SSP15 compression theorem demands a residual channel.

The two no-go theorems and `SignedSSPTwinObservableTransportExact` are jointly exposed from the three canonical TOE roots:
- a lossy quotient can destroy the ability to answer the twin-prime question;
- a genuinely lossless label+residual codec preserves twin-primality and the finite count indicator;
- a raw power-of-two code is **not** the arithmetic exponent, so even a lossless codec requires the actual exponent/readout theorem before applying mod p.

These exact source-written results change roadmap B02/B03/E15 from a vague request into a concrete proof condition. The missing code is an actual `readExponent` with a correct `readExponent(2^p)=p` law on accepted emitted states (or a dependent residual carrying `p` and a proof `code=2^p`). Until that is instantiated, CRT constraints over the raw FRACTRAN integer are invalid. No Agda kernel check has been claimed.

## 2026-10-28 fifth max-cut: concrete certified exponent residual

`DASHI.Arithmetic.SignedSSPProofCarryingExponentExact` constructs a concrete dependent `CertifiedExponentCode` with:
- a signed SSP lane and signed magnitude metadata;
- an explicit Nat arithmetic exponent residual `p`;
- a raw Nat payload `c`;
- proofs that the lane is base-2 SSP and `c = 2^p`.

The canonical encoder uses `Signed.ssp2`, the source-owned `positiveMultiplicity` and the actual `Offset.powerTwo` encoder. Its `decodeExponent` reads `p` from the retained residual, and the source-written `decodeEncodeExponent` and `encodeExponentInjective` provide an exact Nat round trip and lossless injectivity. This directly discharges the *specified-code* arithmetic readout problem; it does **not** establish a decoder for arbitrary unlabeled raw FRACTRAN integers or prime-emission reachability from the actual runtime.

The new `plusMacroSourceMatchesCertifiedCode` and `minusMacroSourceMatchesCertifiedCode` substitute `c=2^p` into the exact fraction-program source with equality witnesses. `plusTwoCode` and `minusTwoCode` then give proof-carrying, correctly decoded output codes. The minus case requires an input proof `p=2+k`; it does not silently underflow. Each numeric two-step fraction execution and signed direction remains owned by `SignedSSPPrimeOffsetMacroExact`. A full concrete FRACDASH machine simulation of the enriched record is still open.

This is a **concrete** lossless code and a partial answer to roadmap B02/B03/D04–D05. It is not an `SSP15ResidualCodec` instance on `FractranCOL.EV5`, which remains a separate bridge. In particular, the code stores `p` as a residual, so no computational compression ratio or extra prime-distribution information follows by itself.

Independent regression `scripts/check_signed_ssp_twin_information_loss.py` ran locally and found exactly 1,224 twin-prime starting integers with lower endpoint ≤100,000, confirming the stronger collision (5,7), and the correct prime-2 odd/modulus distinction. The source-written Agda has not been kernel-checked.

## 2026-10-28 sixth max-cut: exact signed-code / CRT square, both directions

`DASHI.Arithmetic.SignedSSPCertifiedCRTReadoutSquareExact` closes a **concrete proof-carrying arithmetic commuting square** for arbitrary certified prime moduli:
- the existing two-step `2/3` FRACTRAN macro computes the raw code `2^(p+2)`;
- the `CertifiedExponentCode` retains the original p and its power-of-two equality;
- the plus-code decoder computes exactly `p+2`;
- `plusTwoCRTReadoutCommutes` proves modulo any `CertifiedPrimeAxis` gives the same residue as arithmetic `(p+2) mod axis.modulus`;
- `pairSieveTransportThroughPlusCode` and its reverse transport the existing true `AllPairSurvive` predicate across the decoded equality for any list of certified prime axes;
- `twinPrimeToCertifiedCodePair` and `certifiedCodePairToTwinPrime` move two independent actual arithmetic prime certificates between the decoded `p,p+2` pair and the two proof-carrying code endpoints.

This is a source-written finite arithmetic BIDI bridge across all certified moduli, and it directly consumes earlier theorem owners rather than inventing new primality, sign, FRACTRAN or CRT primitives. It is **not** a concrete instance of the FRACDASH VM's `SourceMachine/FractranRepresentation`, not a universal arithmetic `CRTStep` inverse, and not a statement about the original prime program reaching every enriched state. Those remain the first true executable/formalisation frontier. No Agda kernel acceptance has been observed.

**Why this max-cut matters:** raw FRACTRAN code parity and decoded exponent parity disagree already at p=3. The corrected commuting square cannot accidentally delete prime 2. The old SSP and Monster `4B` address/frame information can be included as extra metadata only if it preserves the arithmetic exponent residual; it does not provide missing prime-correlation estimates.

**Attribution scope:** Conway/Guy prime-game semantics; FRACDASH signed paired-register compiler; DASHI prior codec and arithmetic counting owners; Brun/Hardy–Littlewood classic prime-pair mathematics; Ibrahim's separate 3B representation ownership untouched. No external authorship is transferred to the new bridge proof.


## 2026-10-28 seventh max-cut — bidirectional neighbour and faithful reachability

### Exact unsigned arithmetic, both signed directions

`DASHI.Arithmetic.SignedSSPBidirectionalNeighbourExact.agda` completes the negative-offset side of the existing BIDI readout construction. Source-written theorems (Agda kernel pending):

- `plusCodeIsMinusAdmissible`: any certified +2 code has an explicit p=2+k witness for the inverse FRACTRAN -2 macro.
- `plusThenMinusDecodedIdentity` and `minusThenPlusDecodedIdentity`: +2 then -2, and -2 then +2, recover the same **decoded arithmetic exponent**. This is not equality of arbitrary signed machine states, which may retain different metadata and traces.
- `minusTwoCRTReadoutCommutes`: after applying the guarded -2 macro, reduce the **decoded** exponent mod any certified prime axis (including 2), not the raw integer `2^p`. This is the previously missing negative counterpart of `plusTwoCRTReadoutCommutes`.
- `minusTwoPairSieveTransport` and `minusTwoPairSieveTransportBack`: the arbitrary finite certified-prime sieve predicate is preserved in both directions by a proven readout identity.
- `twinAtLowerToCertifiedUpperAndMinus` and `certifiedUpperAndMinusToTwinAtLower`: both genuine arithmetic prime certificates transfer between a lower-start `TwinPrimeAt k` and the signed machine's encoded upper endpoint `k+2` with its genuine -2 offset. This transports evidence; it does not manufacture primality.

**Local computational check**, independently run: `scripts/check_signed_ssp_bidirectional_neighbor.py` tests input exponents `2..499` (498 inputs, 996 exact two-step integer FRACTRAN traces), both output exponent decoders, inverse offsets, real `Prime` checks and modulo tests at certified integer primes `2,3,5,7,11,13,17,19,23,29`. All passed in a local equivalent script. Prime 2 is retained; `2^3=8 mod 2` is not substituted for decoded `3 mod 2`. No infinite or Agda-kernel conclusion follows.

### Exact finite-code enumeration for every actual twin pair

`DASHI.Arithmetic.SignedSSPTwinFiniteCoverageExact.agda` reuses `PrimeCountingFunction.primesUpTo`, `TwinPrimeCertifiedEnumeratorExact.twinPrimeAt?`, and `SignedSSPPrimeOutputBoundaryExact`'s list membership and map transport. It adds `twinStartAppearsAtOwnCutoff`: any genuinely certified `TwinPrimeAt (2+k)` appears in the finite list at cutoff `2+k`. Mapping to `CertifiedExponentCode` preserves membership via `everyCertifiedTwinCodeAppearsAtOwnCutoff`; `encodedTwinListLengthExact` reuses the existing cardinality equality. `twinCountIncrementsAtCertifiedTwin` reuses the generic prime-count-at-certified-member theorem. This completes **arithmetical finite-list coverage**, not the claim the actual machine reaches that emitted code.

### Real source→target reachability transport, conditional on actual alignment

`DASHI.Arithmetic.SignedSSPPrimeEmitterTraceTransportExact.agda` reuses the pre-existing `Core.TypedDependencyCore.DependentActionSystem` and `Core.AdmissibleReachability.Reachable` (no duplicate reachability definition). It defines `ActionTraceCompiler`: every source admissible step has a target admissible step whose **entire next state equals the encoding** of the source's next state. Induction proves `traceSimulation` across arbitrarily long finite traces. Given source PRIMEGAME completeness for every arithmetic prime, the per-state readout agreement and this exact step alignment, `transportReferencePrimeEmitter` constructs the **existing** `ArithmeticPrimeEmitter` interface.

**Important gap isolation:** the existing `Interop.VerifiedFractranCrankPipeline.CompilerSimulation` has forward simulation up to an observed/decode-matching target state; it does not automatically guarantee that the target next state *equals the encoding* needed to iterate that concrete trace proof. Neither generic compiler interface by itself supplies the required concrete signed SSP runtime instance. The trace transport theorem is conditional and does not promote the existence of such an instance or historical Conway/Guy unbounded prime emission into a DASHI kernel proof.

### Adjacent sources and limits

Reviewed latest DASHI PRs #1409–#1413, PR #1407's 27×729 Fourier/codec treatment, and prior owner PRs #1334, #1139, #636 and #128. #1334 explicitly owns contextual FRACTRAN/SSSP, ternary Pareto and Ibrahim snowball BIDI normalization. Those owners remain distinct; no Monster 3B/4B character or 369 analogy is identified with arithmetic prime-pair distribution.

Rechecked mathematical source: DHJ Polymath, *Variants of the Selberg sieve, and bounded intervals containing many primes*, **Research in the Mathematical Sciences** 1, article 12 (17 October 2014), DOI https://doi.org/10.1186/s40687-014-0012-7. The unconditional bound is `H₁≤246`; `H₁≤6` is conditional on generalized Elliott–Halberstam. Its sieve parity analysis does **not** rule out all signed computational approaches, but it does mean exact modular screening alone does not prove `H₁≤2`.

**Next verified blocker:** instantiate actual signed SSP source/target action systems, action-preserving compiler and readout on the entire PRIMEGAME execution, and obtain full kernel checking of the source-written new Agda modules. Separately, general arithmetic CRT reconstruction/inverse and the analytic twin-pair correlation criterion remain open. A finite machine model cannot directly settle the infinite arithmetic conjecture.


## 2026-10-28 eighth max-cut: PR #1407 consumer-specific Pareto transfer

**Cross-PR source, inspected at exact head** `323f15b8de4e1daf4b09531a5b175328c28d5631`, [PR #1407](https://github.com/chboishabba/dashi_agda/pull/1407). Its scientific task is R2P2/finite Fourier and NOT twin primes. The reusable mathematics is an *information-preservation criterion*:

- `R2P227729FourierObserverIncidenceExact` indexes 27 three-coordinate balanced integer modes and 729 ordered input pairs. Exactly 343 ordered sums stay in the retained `[-1,1]^3` output cube; 386 lie outside.
- `R2P227729FourGridRetainedQuadraticParetoExact` establishes that 3-point periodic folding aliases some retained quadratic outputs, whereas a 4-point-per-axis residue grid distinguishes every retained output (even though it identifies outer `+2` and `−2`); 5 points per axis retain the full `[-2,2]^3` output. This is **finite incidence**, not an implemented FFT or measured NS/clock physics.
- `R2P227729BilinearCyclotomicPadCutExact` extends the retained/full statement to independent `f,g` and an abstract coefficient API, subsequently instantiated using the pre-existing exact cyclotomic owner. Coefficient/source ownership remains with #1407.
- `R2P2369WaveOpticalCombInformationCutExact` uses the **existing on-master** `Core.IndexedRelationalHyperfabricSpineExact.ConsumerCollision/ConsumerSufficient`, `Core.IntersectionalNonFactorability` and `Base369WaveContinuousSymbolicCodingExact`: once a coarse projection collides two states that require different answers, postprocessing alone cannot restore the missing information. An exact residual does preserve it.

**What is safely imported into the arithmetic lane:** the generic **on-master** consumer and residual owners above, not PR #1407's branch-only physics modules. New `DASHI.Arithmetic.TwinPrimeConsumerParetoObserverExact` proves at source level:

1. `fiveAndThirtyFiveSameSixWheel`: `5%6=35%6=5`.
2. `twinAtThirtyFiveIsFalse`: the actual proof-bearing prime-pair decision rejects `35` (composite) while `TwinPrimeAt 5` succeeds.
3. `wheelTwinCollision`, `wheelCannotDecideActualTwins`: use the **existing** generic non-factorability owner; modulo-six residue cannot classify true twin-prime starts universally.
4. `postprocessedWheelStillCannotDecideTwins`: any `Nat→Chart` transformation of a mod-six result remains insufficient to decide true twin starts.
5. `primeSieveSymbolicCoding`, `exactTwinQueryCodeRoundTrip`, `exactTwinQueryCodeIsConsumerSufficient`: instantiate the existing symbolic trit-with-exact-residual codec; its full integer payload suffices for the actual twin-prime Boolean query. This is a correctness result, **not** compression or a proof of new prime regularity.
6. `finiteSieveBit` and `sieveBitIsSufficientForFiniteSieveQuery`: the Boolean result of the existing certified all-prime-moduli finite sieve is sufficient **for that exact query**.
7. `finiteSieveBitPeriodic`: the finite Boolean result is periodic by the product of its certified moduli. The proof eliminates impossible yes/no branches using the source-owned two-way `CertifiedPrimePairPeriodExact` transport.

**Why it matters:** an observer can be optimal for one consumer while inadequate for another. The six-wheel is valid as a necessary local filter, not a true prime oracle. By retaining the exact p residual on its actual arithmetic carrier, signed SSP can preserve the genuine question without claiming that coarse modulo classes generate primality.

**Independent local Python replay** `scripts/check_twin_prime_1407_consumer_pareto.py` passed (2026-10-28): 27 modes/729 ordered inputs, 343 retained and 386 outside, 386 retained-output mismatches at 3-grid, zero at 4-grid, zero full-output mismatches at 5-grid; mod-six collision for 5/35; prime-2 raw exponent guard; and five-modulus sieve `(2,3,5,7,11)` periodic with product 2310. `221=13*17` survives that five-modulus screen but is composite. These checks agree with finite incidence arithmetic but are **not** tests of #1407's Agda kernel or an end-to-end signed SSP runtime.

**Updated Pareto / Ibrahim classification:** this transfer pays a clear proof debt on observation sufficiency, rather than importing 27/729/4³/5³ as magical arithmetic constants. Source-written new Agda code is linked to the three TOE roots. No protected ESD or original #1407 owner surface was edited. Ibrahim Monster 3B and other earlier authors retain their original theorem ownership. **Remaining research gates:** actual signed prime-emitter compiler, certified general CRT inverse, quantified joint prime-pair correlation, unconditional twin-prime infinitude. Source-written Agda still awaits a kernel receipt; no CI action was run on request.

### Historical source boundaries

Original Fourier dealiasing priority remains with Patterson/Orszag and subsequent computational Fourier researchers; the #1407 arithmetic index adapter belongs to its PR owners. For the separate number-theoretic frontier, DHJ Polymath (2014), *Variants of the Selberg sieve, and bounded intervals containing many primes*, DOI [10.1186/s40687-014-0012-7](https://doi.org/10.1186/s40687-014-0012-7), proves `H₁≤246` unconditionally and `H₁≤6` conditionally on generalized Elliott–Halberstam. Its sieve parity theorem is a boundary on **purely sieve-theoretic** routes, not an impossibility proof for every signed computational model.
