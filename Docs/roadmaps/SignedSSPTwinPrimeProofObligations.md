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
