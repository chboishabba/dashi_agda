## 21 Nov 2026 P0/CM source-first correction: all-prime owners already on Lean main

**P0 distinction:** original externally checked all-character Dirichlet GRH (`UpperTheory.EveryCharacter`) and its ordinary RH implication remain **external proof-admission work**, not deductions from our selected CM elliptic curve. Exact pinned Lean 4.33.1 statement/kernel/Mathlib root match, and Agda same-object semantic transfer remain DEFERRED, not silently assumed. Lean #113 is the original source-adapter branch; this Agda #1533 tracks admission/geometry, not reproof or source copying. The separate signed G2/G3 original analytic sign inequalities are not thereby inhabited.

**P1 same-curve CM already owns more than finite tests:** current `dashi_lean4@main` has `EisensteinJZeroIntegralHeckeCharacterExact.integralHeckeCharacter` (actual conductor-coprime integral ideal monoid character and multiplicativity), `EisensteinJZeroHeckeLocalAgreementExact.hecke_elliptic_goodPrime_local_agreement` (all rational good primes), `EisensteinJZeroAllPrimeLocalExact.allPrimeLocalEulerPolynomial` (p=2,3 and all good primes), and `EisensteinJZeroConditionalAnalyticEulerExact.conditionalAnalyticEulerProduct_agreement` (all s **conditional on Multipliable**). These main-native declarations were inspected; they do NOT require rebuilding the ideal-normalization/Euler factor engine. Distinguish integral coprime ideal character from full fractional/infinite type analytic Hecke character.

**New #114 source-written original j=0 Hasse weld:** `EisensteinJZeroHasseEulerConvergenceWeldExact` supplies the norm/trace identity and same-jZero good-prime Hasse bound, plus `Nat.Primes.summable_rpow` majorant at Re(s)>3/2. The final original-denominator `Multipliable` theorem **still explicitly takes the pointwise local perturbation norm bound `hlocal`**. Reciprocal Euler multipliability, nonvanishing and original global L-series analytic equality/continuation remain payments, as does elliptic Hecke GRH itself. Different BSD curve `y²=x³−x` Hasse/Euler machinery is a *donor only*, not a proof for `y²=x³+1`.

**Execution/trust:** independent SymPy 1.14.0 symbolic 4N−trace²=3b² and 107/107 good-prime original-curve checks PASS, but no new Lean/Agda kernel, local exact committed bytes or CI acceptance. No blanket implication from Dirichlet GRH to weight-two CM elliptic GRH; no new consequence rows S01–S22 declared proved.

---

# RH / Dirichlet GRH — original screenshots, P0/P1 exact deliverables and consequence matrix

**Date:** 21 November 2026. **Canonical integration:** [PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533), `Docs/roadmaps/AlpogeGRHGeometricTransport20261121.md`. Agda remains the golden programme owner; external Lean claims require statement- and version-locked proof admission. **No CI runs.** Local SymPy is only a finite-arithmetic regression, never a Lean/Agda kernel or an analytic RH proof.

## Source-integrity and enumeration

The user provided **four screenshot images** (a thread of Sadiq's consequence list followed by a post about Alpöge). This is a complete ordered transcription *by discrete claim* of the three Sadiq images; the fourth is context on the alleged author and the RH/GRH announcement, **not** an additional set of mathematical consequences. This table is an inventory of what the post **asserts**, not a blanket endorsement. The first screenshot's seven items are **S01–S07 verbatim in substance**, including the square/cube root and polynomial factorization items.

Counts: **7** algorithms / number-theory items + **3** complexity + **3** software + **4** cryptography + **1** prime-gap + **4** explicit non-implications = **22**. Retain all 22 exactly; never fold the first screenshot into a general "number theory algorithms" row.

### Complete screenshot-to-original-consumer matrix

Legend: **donor** = related original repo infrastructure, *not necessarily a proof of screenshot's exact runtime guarantee*; **audit** = original research statement/condition must be verified; **open** = actual formal deliverable not yet accepted. Source screenshot text is explicitly separated from our corrective interpretation.

| Screenshot | Screenshot claim (complete) | Existing original DASHI owner/donor | Exact remaining named lemma / certificate | Phase / priority |
|---|---|---|---|---|
| **S01** | Miller's fast primality test is provably correct with no randomness | `Analysis/PrimeCountingFunction.agda`; `Analysis/NatPrimeCountingInstance.agda`; prime certificates | `grhMillerDeterministicWitnessBoundSameInteger`: original Miller witness search bound under accurately scoped ERH/Dirichlet GRH; no AKS conflation | P2 / high |
| **S02** | Square roots modulo prime become efficiently deterministic, no random coin flips; currently deterministic generic polylog time is open | original `GF27CompilerBootstrapIntertwinerBoundaryExact`, `EllipticCurveFrobeniusExact`, modular arithmetic | `grhQuadraticNonresidueBoundSamePrime`; `grhTonelliShanksCorrectAndClock` (algorithm and assumptions/version) | P2 / high |
| **S03** | Cube roots and other modular roots likewise become fast deterministic | same finite-field/arithmetic donors | `grhKthRootUniformityScope`, `grhKthRootAlgorithmClock` (fixed/varying k; factorization assumptions) | P2 / medium |
| **S04** | Finite-field polynomial factoring deterministic quasi-polynomial instead of relying on randomization | `GF27CompilerBootstrapIntertwinerBoundaryExact`; `OggSSPMonster3BSelectedGF729WeldExact`; `j369_kernel_field_recognition.py`; #1291 Route C | `grhFiniteFieldPolynomialFactorsSameInput`; `grhFiniteFieldFactorisationQuasiPolynomialClock` | P2 / high |
| **S05** | Direct deterministic construction of any finite field without random search | #1291 Route C field, Frobenius and normal-basis work; GF27/GF729 owners | `grhIrreducibleDegreeNConstructor`; `grhFieldPresentationRoundTripAndClock` (p,n, input encoding) | P2 / high |
| **S06** | Integer factoring provably as easy as computing Euler's totient φ(n), without randomization | `Crypto/FiniteFactorArithmetic.agda`; `Crypto/ShorFactoring.agda`; RSA260 branch | `integerFactorsFromTotientOracleSameN`; `totientReductionDeterminismAndClock` (check unconditional prior results; not plain efficient factoring) | P2 / medium |
| **S07** | For any permitted residue a mod q, a prime exists no larger than approximately q² so finding one is fast | finite prime-count/sieve/CRT and SSP prime owners | `grhLeastPrimeInProgressionExplicitLogFactors`; `leastPrimeEnumerationBitComplexityFirewall`; `residueConsumerFactorsThroughNativeChart` | **P0 after RH certificate**, high |
| **S08** | Feasibility of systems of polynomial equations moves from PSPACE to AM | Karp-21/native verifier, algebraic polynomial machinery | `grhHilbertNullstellensatzInAMExactEncoding`; `hnCompletenessClaimScope` | P3 / medium |
| **S09** | Valiant algebraic P versus NP gets tied to ordinary P versus NP over complex numbers | Karp-21, Lean Clay #108 and algebraic circuit branch donors | `grhValiantComplexBooleanBridgePreciseDirection` (never assert VP/VNP equals P/NP unqualified) | P3 / medium |
| **S10** | A particular 744-state Turing machine is proved to run forever | finite verifier/trace machinery; original exact machine currently unidentified | `grh744StateMachineTransitionTable`; `grh744StateNonhaltingReductionReceipt` | P3 / low until source |
| **S11** | Conditional PARI/GP and Magma results become fully proven | RH/Clay provenance/analytic owners; external software not native donors | `pariMagmaConditionalOutputExactVersionAndHypothesis`; `grhConditionalResultDischargeBySameScope` | P3 / medium |
| **S12** | Class-group computation gets guaranteed running times | number-field, CRT/CM and modular arithmetic donors; classical results | `classGroupRequiredNumberFieldLFunctions`; `classGroupRuntimeScopeUnderRequiredERH` | P3 / medium |
| **S13** | Elliptic curve generation for crypto gets runtime guarantees | CM j / #1529, BSD selected CM curve, `EllipticCurveFrobeniusExact` | `grhCMCurveGeneratorSameCurveAndLFunctionScope`; `cmCurveParametersClockAndPrimality` | P2 / medium |
| **S14** | Hard discrete log on one elliptic curve implies hardness on almost all similar curves | `Crypto/ShorDiscreteLog.agda`, elliptic/isogeny owners | `ecDlogRandomSelfReductionExactFamily`; `ecDlogHardnessScopeAndDistribution` | P3 / medium |
| **S15** | Known quantum attacks on some lattice cryptosystems become provably successful | quantum/Shor and finite-field donors, **not** an identified matching lattice attack | `latticeAttackConcreteSchemeAndGRHInput`; `latticeAttackQuantumClock` | P3 / low until source |
| **S16** | Known quantum attacks on some isogeny schemes receive proved speeds | `ShorOrderFinding`, modular j and isogeny scripts | `isogenyAttackSameFamilyComplexity`; `isogenyAttackRequiredLFunctionScope` | P3 / medium |
| **S17** | BIKE-type code-based crypto gets existence guarantees for necessary special primes | CRT/progression prime owners; no confirmed BIKE-specific theorem | `bikeExactPrimeCongruenceSpecification`; `grhBikeAdmissiblePrimeBound` | P3 / medium |
| **S18** | Every p has another prime within about √p log p, bounding next-prime search | prime count, Zeta/Weil, prime-gap and SSP sieve owners | `rhPrimeGapExplicitNextPrimeBound`; `nextPrimeScanNotPolylogClock` | **P0 after RH certificate**, high |
| **S19** | Does NOT settle P versus NP | P≠NP/Karp-21 frontier ledgers | `rhDoesNotPayNativeKarpGates` (non-promotion policy, not a metatheorem of independence) | P4 / guard |
| **S20** | Does NOT make factoring easy; therefore RSA and ECC remain safe | RSA260, Shor and EC owners | `rhNoGeneralFactoringAlgorithmPromoted`; `rsaEccSafetyNotDeducedFromGRH` | P4 / guard |
| **S21** | Does NOT practically speed things up, since random algorithms already work | CPU/GPU/algorithm benchmark tooling | `derandomisationProofVsRuntimeMeasurementBoundary` | P4 / guard |
| **S22** | Ramanujan graphs, expanders and AG codes unaffected since finite-field RH was proved decades earlier | field, finite spectral/graph and Frobenius owners | `finiteFieldWeilDeligneVsDirichletGRHScope`; `expanderAgCodeActualOwnerAudit` | P3 / medium |

Screenshot claims of "fast", "proved" and "safe" are **not** simultaneously valid without exact complexity/cryptographic hypotheses. Sources for each claimed conditional theorem must be attached **before** promoting the lemma. A related named module is not acceptance.

## Work programme: RH P0, geometry/weld/consumer P1

### P0 — actual RH/GRH proof and original analytic consolidation (highest priority, blocks all promotions)

| Gate | Exact deliverable | Existing owner and evidence | Remaining proof/check |
|---|---|---|---|
| **P0.01** | `originalAlpogeArchiveHashAndFiveChallengeStatements` | 20 Nov Alpöge source; Sutherland checker report; existing PR #1533 ledger | Freeze exact source and independent challenge byte hashes; inspect true theorem types and axiom dependencies |
| **P0.02** | `externalLeanRHKernelAxiomAndStatementReceipt` | independently reported Lean / con-leche / nanoda checks | Reproduce under pinned source/compiler only if permitted locally; **not CI**; current task does not claim this receipt |
| **P0.03** | `originalMathlibRHDirichletGRHScopeDisambiguation` | original `AlpogeGRHGeometricTransportExact`; R1–R4 Clay owners | Directly match ordinary ζ RH vs Dirichlet GRH, distinguish Dedekind/automorphic ERH |
| **P0.04** | `originalCompletedXiWeilFormulaSameObject` | Agda Clay #1499, Lean #108, `RiemannAnalyticSubstrate`, `RiemannExplicitFormula` | Use established *classical* R1 completed ζ + Guinand–Weil source, identify original analytic functions and test normalizations; no new spectral interface |
| **P0.05** | `originalRHLeanAgdaZetaCriticalLineTransport` | `AlpogeGRHGeometricTransportExact.externalRHImpliesDashiRH` | Construct actual Lean/Agda same-object map, zero and critical-line predicate transports; abstract assumed record is insufficient |
| **P0.06** | `rhOriginalWeilSquarePositivityConsumer` | `WeilConvolutionSquare`, `RiemannWeilSquareCriterion`, `DashiWeilSquareBridge` | source-fidelity classical RH⇔Weil-square positivity on genuine test function class, including admissibility and explicit formula; don't confuse RHS bridge with inverse |
| **P0.07** | `rhOriginalPrimeGapExplicitAndGRHLeastProgressionPrime` | original prime/sieve owners, S07/S18 | precise bound/log factors, strict computational cost model, matching character scope |
| **P0.08** | `rhNoPromotionClaimLedger` | Clay six-endpoint roadmap and RH Pareto board | update statuses only on original terminal construction, never from conditional record/source-written text |

**P0 decision:** external formal proof reception can change the status of the *mathematical RH statement*, but it does not automatically fill DASHI's original analytic substrate, solver reductions, or geometrically reconstructed Weil form. Keep each distinct.

### P1 — native geometry, consumer sufficiency and stronger commuting cube (runs alongside P0 only where independent)

| Gate | Exact deliverable | Original owner | Remaining |
|---|---|---|---|
| **P1.01** | `nativeSpatial27Residue27RoundTrip` | `Base369Ternary27HypervoxelFabricGeometryExact`; `JInvariant369Cube27CuspCodecNonIsometryExact` | Reuse completed chart; retain native 54-edge adjacency as transported structure |
| **P1.02** | `native27EveryPointConsumerFactorsThroughFullChart` | `QueryFactorisationSufficiency.FactorsThrough`; new `GRHNative27ConsumerDescentExact.complete27ChartFactors` | source-written canonical owner reuse; original Agda kernel receipt **OPEN** |
| **P1.03** | `native27LostObserverNonDescentWitness` | `ConsumerDescentMinimalObserverExact` / `ConsumerFibreRepairExact` | exact witness for a geometric observable erased by a selected quotient; repair separating coordinate |
| **P1.04** | `originalC3ZetaSquaresSixFaceCube` | `ZetaIrrationalFibreCommutingSquareBidiExact`; `CommutingProvenanceBidiCrossPollination2026Exact`; #1291 `GovernedIndexedResidualCubeExact` | instantiate six actual original squares as faces, preserve eight typed vertices/twelve maps, no irrelevant redefined cube |
| **P1.05** | `originalSixOrderEndpointCoherence` | #1291 `ExactFaces`, six paths and S3 hexagon | exact Agda all-path proof with original source maps, not only SymPy coordinate-zeroing |
| **P1.06** | `originalIndexedResidualHolonomyAndReconstruction` | #1291 indexed residual; `PhysicsLimitCommutingSquare.ResidualControlledCommutation` | compare two source-respecting paths, actual correction operator, retain h/t/k/j/v, not just a named residual type |
| **P1.07** | `originalWeilSpectralFormNativeCubeIsometryOrDefect` | original R1 explicit formula/Weil space, genuine geometric spectral operator | supply actual (Q_W), (Q_G), source isometry or explicitly bounded form discrepancy; finite spectral negative control |
| **P1.08** | `originalBishopXiComplexCarrierSameObjectWeld` | Bishop #1478; Agda #1497; Lean #104 and Clay #1499 | use existing exp/xi/Dirichlet series; prove real-to-complex, completed ζ and convergence identifications without abstract fake equality |
| **P1.09** | `originalGF27FrobeniusConsumerTransport` | #1291 Route C; `GF27CompilerBootstrapIntertwinerBoundaryExact`; GF729 owners | original field/ring/normal-basis structure, not a mere 27-cardinality match or spatial-graph isometry |
| **P1.10** | `originalYangMillsOSPositiveOperatorWeldBoundary` | YM #1444/#1503, BEC #1489, F8 #1527 | optional reusable positive form/Gram identities; retain interacting continuum, physical covariance and mass-gap open |

**Why the commuting cube is stronger:** each face is an existing square, but all six face laws enable path independence for *all six orderings of the three axes*. The diagrammatic cube's eight object-vertices are not the spatial cube's 27 sites. The **actual native 27 can appear in every suitable diagrammatic vertex**; these are two orthogonal layers, not competing definitions of 'cube'.

### P2 — algorithmic consequence proofs after P0 scope admission

Deliverables: S01–S07, S13 and related finite-field/certified prime consumers, exact source version, assumptions, same-input output/witness, and bit-clock. Prioritize **S07/S18 first** for direct RH/Dirichlet GRH; then S04/S05 for Route C; S01/S02/S03 for deterministic versus randomized comparisons; then S06/S13. A program only handling selected GF27 or GF729 is not a generic all-fields constructor.

### P3 — complexities, cryptography, software, finite-field RH

Deliverables: S08–S17 and S22 each with a sourced theorem, assumption-checker, object/parameter family and exact asymptotic bound. Match actual Hilbert Nullstellensatz problem to AM, not arbitrary polynomial-system satisfiability; specify the precise algebraic VP/VNP implication; identify 744-state transition table; require explicit lattice, isogeny and BIKE scheme parameters. Mark **unidentified original source** rather than falsely discharged.

### P4 — non-promotion and machine-readable acceptance

Keep S19–S21, actual Clay RH vs Dirichlet GRH vs extended ERH, and 27-cube versus +1 cycle as versioned negative controls. Every accepted deliverable needs source ID, exact Git SHA, lemma owner, audited statement, local test command/receipt and proof-trust level (source-written, local finite, native kernel, independently accepted math). No CI, no physically inferred YM/KK/NS consequences.

## Most relevant recent PRs checked 21 Nov 2026

| PR | Inspected head | Reuse, not reimplementation |
|---|---|---|
| [Agda #1533](https://github.com/chboishabba/dashi_agda/pull/1533) | current integration | canonical P0/P1 programme; external conditional RH and native 27 consumer bridge |
| [Agda #1291](https://github.com/chboishabba/dashi_agda/pull/1291) | `b9d1e3fa` 20 Nov | indexed residual cube H05, six face laws, Route C and H15 density/Max-Cut |
| [Agda #1497](https://github.com/chboishabba/dashi_agda/pull/1497) | `f213b5bf` 14 Nov | Z7/odd-zeta Bishop same-object and explicit RH boundaries |
| [Agda #1499](https://github.com/chboishabba/dashi_agda/pull/1499) | `251b567d` 16 Nov | original Clay R1–R4, source/classical completion distinctions |
| [Lean #108](https://github.com/chboishabba/dashi_lean4/pull/108) | `c0dcb1f8` 16 Nov | original RH R2/G3 and Clay rollup, not kernel-proved terminal RH |
| [Lean #104](https://github.com/chboishabba/dashi_lean4/pull/104) | `dbda83ae` 14 Nov | exact Xi/Mathlib and Bishop/Z7 sidecar constraints |
| [Agda #1489](https://github.com/chboishabba/dashi_agda/pull/1489) | `bf2eef07` 14 Nov | finite same-H C3 heat/zeta/positive spectral structure, not genuine Xi zero identification |
| [Agda #1529](https://github.com/chboishabba/dashi_agda/pull/1529) | `7b35790d` 20 Nov | exact modular j/CM, constructive split/Pell/dyadic certificates for S13 |
| [Agda #1526](https://github.com/chboishabba/dashi_agda/pull/1526) | `274faf58` 20 Nov | original consumer-sufficient C3 quantization/future-state non-descent |
| [Agda #1444](https://github.com/chboishabba/dashi_agda/pull/1444) | `7fc2bde9` 20 Nov | Yang–Mills physical positive Wilson/OS remaining source obligations |
| [Agda #1503](https://github.com/chboishabba/dashi_agda/pull/1503) | `b93909a0` 15 Nov | F19 YM source convergence; unresolved original scalar weld |
| [Agda #1527](https://github.com/chboishabba/dashi_agda/pull/1527) | `fc5198a3` 20 Nov | S3/C3 mode Reynolds source and explicit non-commuting physical radial operator |

**Recentness note:** dates above are GitHub last-update timestamps shown by connector, not proof-completion dates; latest user PR work across other domains is not automatically a dependency of RH.

## Finite local acceptance and exact remaining gate

The existing `/mnt/data/check_grh_native27_cube.py` was rerun locally: Python + SymPy exact checks PASS on 27/27 chart roundtrips, 54 native spatial edges, all six coordinate-erasure endpoint orders, explicit noncommuting carry/coordinate witness, consumer collision, and Laplacian trace moments `(108,558)` vs cyclic `(54,162)`. This **does not** check actual Agda types, the six original C3/zeta mathematical squares, or RH.

**Highest-alpha next original implementation:** P0.01–P0.06 first, with P1.04–P1.07 developed in parallel only as source-owned finite geometry; attach exact native consumer and original analytic function identification before making any new terminal theorem claim.


## 21 November 2026 — focused last-week Bishop / π / finite arithmetic original-source audit for S02–S07

**Status:** inspected original module bodies, exact PR heads and controlling source roadmaps; this is an **integration and dependency audit**, not a completed GRH-conditional algorithm. No CI, Agda, Lean, or Nix checker was run. Preserve the primary programme ordering: **P0 RH source theorem and genuine analytic consequences** before **P1 native geometry/weld/consumer**. S02–S06 are downstream algorithmic consumers, and S07 is the direct P0.07 prime-in-progression priority.

### Recent donor provenance and actual status

| PR, latest inspected head | Date and exact original source evidence | Consumer-relevant reusable content | Boundary |
|---|---|---|---|
| [#1529](https://github.com/chboishabba/dashi_agda/pull/1529) `7b35790decf33e5da8a5c1ce4ba14853ae244e05` | Updated 20 Nov. `DASHI/Foundations/HypergeometricBSplitIntegerMergeExact.agda`, `BishopPellLucasIntegerInvariantExact.agda`; `Docs/roadmaps/ConstructiveConstantsAndKleinJCMMaxCut20261118.md` and `ConstructivePiBinarySplitMaxCut20261118.md` | Generic integer `P/Q/B/T` merge associativity and tree rotation; rational sum-prefix checker; original Machin atan π, exact Pell norm-one D=2,3,6, dyadic CM(-163) intervals, modular-j proof-relevant chart; total-degree Cayley coefficient/tail control and explicit 81(2/3)^(N+1) bound | Finite integer split merge is NOT a polynomial factorization algorithm; Pell real sqrt is NOT square root mod prime; q/CM analytic identification and exact-head Agda checker OPEN |
| [#1478](https://github.com/chboishabba/dashi_agda/pull/1478) `fb374e50e59a98e2b8a1eee215c77428c5728b68` | Updated 14 Nov. `Docs/roadmaps/AnalyticJTetrationActiveMaxCut20261109.md`; `BishopComplexExpFactEqualsNativeExpExact.agda`; original selected Bishop log `8/27` remainder modules, original eta dyadic source law | Actual Bishop Cauchy-limit/setoid transport, complex exp/log, finite rectangle/triangle tails, selected branch provenance, q↔j same-function consumers | Complex log / sqrt analytic leaves and Bishop sqrt calculus partly uninhabited; no finite-field discrete logarithm or character nonresidue result; no Agda kernel receipt |
| [#1408](https://github.com/chboishabba/dashi_agda/pull/1408) `28d85aa529155352a025de9e12853ecad1e4214e` | Updated 17 Nov. Original `DASHI/Arithmetic/TwinPrimeTernary270AffineCRTCodecExact.agda`, `CertifiedPrimePairModulusExact`, PrimeModSix and wheel owners | Actual chosen affine cube27↔27 admissible residue representatives mod 270, explicit 27-case left inverse, arithmetic local-survivor filters and C2 antipode; chart retains geometry instead of bare count | S07 requires arbitrary q, coprime a, least-prime theorem and effective bound; selected 270 *survivors* need not be prime; full Agda all-survivor surjectivity and generic CRT inverse OPEN |
| [#1497](https://github.com/chboishabba/dashi_agda/pull/1497) `f213b5bfb893e49ae9b29b2915257884b3b0e14e` | Updated 14 Nov. `BishopFastCauchyRationalNormalizationRoundTripExact`, `BishopFastCauchyZetaWeldExact`, `BishopSetoidWeldExact` | Canonical rational embeddings, Cauchy comparison and original ζ same-value **conditional** transport; high-value P0/P1 donor for exact analytic identification | No external Z7→native Bishop complete proof or RH Weil positivity from these finite transport declarations |
| [Lean #104](https://github.com/chboishabba/dashi_lean4/pull/104) `dbda83aec4b6aa07746d5c692d2d99440872bda1` | Last inspected update 14 Nov, selected Mathlib xi reflection and v4.35 theorem sidecar | Version-isolated same-Mathlib ζ, Dirichlet-series/xi names; avoid competing representations in RH P0 | Not a cross-version Lean proof import or same-object Agda kernel certificate |
| [#1291](https://github.com/chboishabba/dashi_agda/pull/1291) `b9d1e3faec8eeeee1bed73840235e364130cfc27` | Updated 20 Nov. `IndexedResidualCube369NineDOFMaxCut20261120.md`, Route C | Geometry-preserving 27 chart, GF(3^9) original-field candidate, relative Frobenius, six-face indexed residual cube, consumer-specific witness retention | Finite fields `GF(27)` and spatial Cube27 are different **operations on the same chosen 27 chart** unless structure transport proved; general arbitrary `GF(p^n)` construction OPEN |

### S02 — deterministic finite-field square roots

**Exact deliverables** (after original GRH theorem scope proof):
- `originalFiniteFieldQuadraticCharacterSamePrime`: use the canonical finite-field arithmetic/Legendre-symbol or Euler-criterion producer rather than Bishop real-order square-root operations.
- `grhLeastQuadraticNonresidueSpecifiedCharacterBound`: state the actual conditional bound in characteristic p and its required L-function family; don't infer it from Pell interval widths.
- `modularRootAlgorithmSameInputCertified`: source Tonelli–Shanks or a specified alternate algorithm; output either a root `x²≡a (mod p)` or a correct nonresidue certificate, with explicit zero and p=2 guards.
- `modularRootAlgorithmBitClock`: complexity in `log p`, with factorization assumptions and deterministic GRH witness search explicitly priced.

**Priority P2-high**, with only the shared integer/squaring/enclosure operations imported from #1529. There is no true direct mathematical identification between positive Bishop sqrt(D) and modular sqrt(a) in F_p.

### S03 — deterministic cube and higher roots

The π roadmap has a **C3 exact cube-root interval producer / Halley** gate and `K05` complex Cayley proof, but those are characteristic-zero algebraic/analytic calculations. Reuse finite polynomial identity, exact division and termination methods only.
- `finiteFieldKthPowerResidueCriterionSameField`
- `finiteFieldKthRootCorrectWitnessOrObstruction`
- `grhKthRootCharacterSearchAndClock`
- `charPAndNoncoprimeKBranchGuards` (p dividing k, gcd(k,p−1), fixed vs input-dependent k)

**Priority P2-medium**. The actual field root problem must not be marked complete by the real Halley certificate.

### S04 — deterministic finite-field polynomial factoring

Reconcile #1529's **integer hypergeometric sum-splitting** with **polynomial factor splitting**, not by naming them the same algorithm:
- `finiteFieldPolynomialOriginalRingAndRepresentation`: explicit coefficient field, degree, monic/zero input and source encoding.
- `finiteFieldSquarefreeDistinctEqualDegreeStages`: factorization stages using original polynomial/Frobenius operations where available.
- `grhDeterministicFactorChoiceExactAlgorithm`: inspect and instantiate the original GRH-conditional deterministic factor-selection algorithm, not a random-choice theorem.
- `grhFiniteFieldFactorisationOutputProductAndIrreducible`: exact reconstruction incl. multiplicities.
- `grhFiniteFieldFactorisationQuasipolyClock`: bit clock and proof of theorem's claimed quasi-polynomial exponent.
- `splitTreeGenericReuseOnlyIfVerified`: use original `HypergeometricBSplitIntegerMergeExact` for verified auxiliary associative multiplication/certificate reduction *if* a genuine same-operation embedding is exhibited; otherwise **do not** weld it in.

**Priority P2-high**. The source-written P/Q/B/T merge identity is a strong reusable certificate/parallel reduction pattern, not evidence that finite-field factoring is solved.

### S05 — arbitrary finite fields (top algorithmic geometry cut)

Existing GF27 and GF729 selected presentations plus #1291 Route C are **strong direct donors**. The original `GF27CompilerBootstrapIntertwinerBoundaryExact.agda` uses explicit irreducible `F₃[a]/(a³+2a+1)`, but its compiler analogy is marked conditional. The fixed-state 27 residue digit chart and spatial geometry must remain separately marked under consumer transport.
- `fieldConstructorAllPrimePAndPositiveN`: specify type `F_p[t]/(f_{p,n})` and arbitrary p,n, not a selected cubic.
- `deterministicIrreduciblePolynomialDegreeN`: actual construction proof, irreducibility and deterministic complexity.
- `fieldNormalBasisFrobeniusCompatible`: original Frobenius map with chosen basis, full field add/multiply, inverses, norm/trace as selected.
- `originalGF27GF729SelectedSpecialisations`: reuse the existing selected field owners as regression/specializations of the general constructor.
- `fieldToGeometric27ConsumerFacts`: explicitly mark which *selected* 27 coordinate consumer facts factor through the chosen chart, and which field addition/multiplication are not spatial grid motions.
- `grhFiniteFieldBuildBitClock`: proof against input bit lengths and explicit source conditional assumptions.

**Priority P2 highest after P0.07**. Reuse #1291's indexed commuting cube for 3-way representation changes, keeping same-carrier invariants and indexed residuals.

### S06 — deterministic factoring relative to φ(n)

The RSA260 and `FiniteFactorArithmetic` owners already supply actual arithmetic and factor-consumer infrastructure. The #1529 integer-only split tree could accelerate auxiliary exact sums but **does not construct an oracle reduction**.
- `integerTotientOracleDomainAndOutputEncoding`
- `integerFactorsRecoverFromTotientOracleSameInput`: explicit adaptive or nonadaptive reduction (whichever the original cited result proves).
- `integerFactorsRecoveryCorrectForRepeatedPrimePowers`
- `totientReductionDeterministicTuringClock`: count oracle calls and bit operations; audit whether this reduction is already unconditional.
- `oracleReductionIsNotFactoringWithoutOracle`: non-promotion test.

**Priority P2-medium**; source-first audit of the actual totient/factoring complexity theorem before adding new code.

### S07 — GRH primes in arithmetic progressions (direct RH P0.07)

A concrete geometric bridge is already present: #1408's exact affine 27-point chart into the **selected** 270-wheel CRT survivor classes. This is not just a count-of-27; it constructs the actual arithmetic local sieve classification.
- `native270WheelSurvivorsFullCoverage`: the original missing Agda proof that **every** admissible class mod 270 is covered.
- `arbitraryModulusCoprimeResidueCRTConsumer`: move from selected 270 to explicit arbitrary coprime (a,q), retaining quotient projections and consumer provenance.
- `dirichletCharactersSameResidueClass`: identify the actual Dirichlet characters and L-functions appearing in GRH bounds.
- `grhLeastPrimeProgressionBoundExactLogFactors`: import or derive the exact least prime inequality with constants, q restrictions and log factors from the real external theorem.
- `primeProgressionSearchCertifiedCorrectness`: certify least/selected prime when found with an existing primality certificate owner.
- `progressionSearchBitClockHonest`: number of tested candidates and bit complexity; brute-force search up to polynomial(q) is exponential in log(q).
- `native27GRHConsumerIndexedSixFaceCube`: specialize original C3/zeta commuting-square faces with actual CRT/character/prime-count observation maps; preserve failed-face residual if arithmetic and geometric operators do not commute.

**Priority P0.07-high**, then P1 geometry/weld. The finite 270 sieve does not prove prime existence in arbitrary progressions.

### Cross-cut reuse — exact rational arithmetic and Bishop π

- `HypergeometricBSplitIntegerMergeExact.mergeAssociative` is a prior **integer algebraic** owner. Its missing semantic correctness `T/(QB)` must be paid before interpreting it as a certified partial sum; no general characteristic-p field factoring is derived.
- `BishopPellLucasIntegerInvariantExact.doubleUnit` proves a source-written Pell norm-one recurrence for D=2,3,6. It is a **real sqrt enclosure donor**, not a finite-field quadratic-character theorem.
- `BishopMachinArctanConstructionExact.bishopMachinPi`, `BishopMachinOriginalCayleyFormalSeriesExact` and `BishopMachinCayleyEquationForcesCoefficientsExact` retain original π/complex phase, useful for analytic constants in P0.04–P0.06 and CM generation, not modular-root witnesses by themselves.
- `BishopOriginalEtaAbelUniformTail20261114.md` provides the classical compact-uniform eta tail estimate with a stated Bishop log/exp/FTC weld debt. It is a **direct P0 analytic same-object donor** to zeta proof admission (not a new zero-location proof).
- `JInvariant369Zeta6561MonsterCrosswalkExact` explicitly distinguishes cyclotomic zeta from Riemann zeta; do not conflate roots of unity in finite-field/cyclic Fourier work with complex ζ(s).

### Acceptance hierarchy and next work packet

1. **P0.01–P0.06 (RH first):** exact external statement/provenance → original classical R1 Xi/Weil formula → original analytic same-object bridge. Consume Bishop eta and Machin π functions only where mathematically identified.
2. **P0.07 / S07 (direct consequence):** original Dirichlet-character scope and least-prime formula plus native CRT-wheel producer with actual prime certificate. Deliver exact bound/complexity, not a claim that a 270-wheel survivor is necessarily prime.
3. **P1 / S05 (geometry):** owner-led field basis/Frobenius and native geometric 27 consumer, six-face indexed commuting cube with actual source operations and quantified residuals.
4. **P2 S02–S04:** conditional nonresidue/kth-root and polynomial factoring, using the known original field arithmetic and proof-preserving reducer patterns.
5. **P2 S06:** totient oracle original reduction theorem, separate from a new unconditional factorization breakthrough.
6. **Review gates:** no CI; locally executable finite SymPy only; no Agda/Lean acceptance unless separately actually checked. The cross-PR review **does not** claim any newly discharged mathematical theorem.


## 21 November — updated P0-first reverse-solve ownership, with exact source integrations

**This supersedes earlier requests to prove the entire old G3/A2 route before importing RH**. Source original `Main.lean` in the externally audited v4.33.1 Alpöge/Claude package already exports Mathlib `RiemannHypothesis`. Our existing Lean `MillenniumExternal.ExactTargetSurface.clayRiemannHypothesis_iff_mathlib` is a literal proof of the needed equivalence, so source-admission rather than a fresh analytic zero-location contradiction is the immediate minimum cut. See [AlpogeRHOriginalSourceBidiMonster369P0P1MaxCut20261121.md](AlpogeRHOriginalSourceBidiMonster369P0P1MaxCut20261121.md).

| New/updated gate | Priority | Already-paid producer / new source | Exact remaining lemma/acceptance |
|---|---|---|---|
| P0.00 author source admission | P0 highest | original 5 theorems in `Main.lean`; independently accepted export; Lean [#113](https://github.com/chboishabba/dashi_lean4/pull/113) pinned source adapter | `alpogeOriginalArchiveLicensedMaterialization`, `alpogeMainNoAxiomSameKernel` — source no redistribution licence; independent full source not downloaded or recompiled in DASHI |
| P0.01 Clay root terminal BIDI | P0 high | existing `MillenniumExternal.ExactTargetSurface`, and #113 original `AlpogeRHBoundaryExact` | `alpogeMainRHIntoSameVersionClayKernel` — actual cross-version coherent import; **the statement equivalence itself is already paid** |
| P0.02 Agda original RH endpoint BIDI | P0 high | original `RiemannAnalyticSubstrate`, original `RiemannZetaProgramBoundary`, source-written `AlpogeRHOriginalClayEndpointBidiExact` | `originalAnalyticStripZeroIff`, `originalAnalyticStripCriticalLineIff`, actual external proof admitted and compatible trusted Agda transport; abstract records still uninhabited |
| P0.03 Dirichlet GRH scope | P0 high | exact external original `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive` | same-definition Dirichlet character / L-function proof import and no wider automorphic/number-field claim |
| P1.11 G2 determinant consumer | P1 highest geometry | `RiemannG2DeterminantConsumerQuotient369Exact.determinantResponseSufficientForFixedKernel` | `originalThetaO2nDeterminantEqualsG2eSourceQ` or typed no-go; fixed-kernel scalar sufficiency is **paid**, not general theta equality |
| P1.12 genuine theta mechanism | P1 high | original `PenumbralSingularThetaIntegral`, `SingularThetaBorcherdsBridge` | `originalThetaLiftWeightSignatureRegularizationBidi`: compare source author's genuine O(2,n) theta chain against this different Borcherds source; no inferred isomorphism |
| P1.13 finite symmetry / Fourier | P1 high | `C3CubeFourier27Exact`, `TernaryPermutationS3LawsExact`, `C3RiemannConjugationBridgeExact`, #1510, #1527 | `originalC3S3XiCharacterConsumerSixFace`: actual source maps, 6 face laws or residuals; cyclotomic ζ3 distinct from Riemann ζ |
| P1.14 Monster and Albert | P1 conditional | #1472 Y443, `Monster369ZetaSameObjectWeldExact`, `Griess1990RationalAlbertTrialityTransportExact`, #1489 | `originalGriessThetaRepresentationActionIdentification` *only if* source matching found; otherwise explicit negative control; does not block RH endpoint |

**Steelman** = preserve original proof's exact spectral, analytic, finite-character and theta directions rather than collapsing them into one generic 'positivity' label. **BIDI** = prove forward and reverse on the same named carrier with the existing actual theorem owners. **Reverse-solve** = walk backwards from the already-paid Lean Clay terminal equivalence; don't allocate work to Riemann G2/G3 unless the external proof's actual audited dependency graph needs it.

No CI, no Lean/Agda native acceptance claimed in this update. Existing finite SymPy checks are P1 regressions, not external proof import evidence.

## 21 November — selective RH source splice and first genuine theta/geometric producer edge

**P0 target now: source-original 5 public claims, as few unnecessary wrapper imports as the actual code permits.** New Lean #113 `RHTopCut.lean` imports only `Statements` and `Supplements.Kernels.MainTheorems` instead of `MainTheoremsAll`. New `RHSelectiveProducerCut.lean` also bypasses `MainConclusion`, directly composing the *original exact underlying theorem terms* `every_character_of_literature_of_vWin`, `vwin_of_row`, `galoisLocalGlobalStrong_recParameter`, `Formalism.VW.rh_of_every`, `Formalism.VW.critLine`, `Claim.strip`. This is a **selective root-import and proof-composition candidate**, not an original deep theorem reproof. Neither has been Lean checked, and each imported source module may have a large transitive dependency closure.

### Actual first geometric crosswalk from inspected external fork source

- `UpperTheory.FinalTheorems.everyCharacter` is produced from the actual `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` in `CharacterBoxes/MainConclusion.lean`.
- The latter is defined by `galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK` in `Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean`.
- `galoisRepresentations_of_thetaLift up` is defined by `galoisLocalGlobalStrong_of_geometry_lift UpperTheory.Gal.Int.Geo.geoOne_holds up` in `GaloisRepresentationsOfThetaLift.lean`.
- `UpperTheory.TP.K.tLiftK` is defined from `UpperTheory.TP.tLift_holds_k` in `ThetaParseval/ThetaKernels/TLiftK.lean`.

These are **source-readback exact producer edges**. They give a much stronger P1 target than 'this resembles our Monster/369 notation': any replacement using native 369, G2, S3, Weil or Monster must furnish an *actual term* for the original `UpperTheory.TP.TLiftK` / `UpperTheory.GalStar.Row0b recT`, or a proven consumer-preserving map into those original types.

| Gate | Priority | Minimal exact deliverable | Status |
|---|---|---|---|
| RH-P0-TC1 | highest P0 | locally typecheck `RHTopCut.lean` against original fork v4.33.1, five exact theorem types and axioms | SOURCE WRITTEN, OPEN |
| RH-P0-TC2 | highest P0 | locally typecheck `RHSelectiveProducerCut.lean` and compare *actual* import closure to TC1 | SOURCE WRITTEN, OPEN |
| RH-P0-TC3 | P0 | import exact Mathlib root RH into existing Clay BIDI on one accepted Lean toolchain; no stale cross-version OLean | open actual version weld |
| RH-P0-TC4 | P0 | original Agda complex/Zeta zero predicate and critical-line transport + actual proof admission | open |
| RH-P1-GEO1 | P1 high | `originalTPtLiftKFromNativeGeometricProducer`: exactly original theta-lift `UpperTheory.TP.TLiftK` with correct range, parameters, measures | OPEN |
| RH-P1-GEO2 | P1 high | `originalRow0bFromGeometricThetaLift`: actual original `galoisLocalGlobalStrong_of_geometry_lift` and source `geoOne_holds` or typed equivalent | OPEN |
| RH-P1-GEO3 | P1 medium | `originalG2DeterminantConsumerFactorsThroughRow0b` or explicit mismatch witness; our `determinantResponseSufficientForFixedKernel` alone is insufficient | OPEN |
| RH-P1-GEO4 | P1 medium | original C3/S3 six-face, Weil test and genuine theta source operator BIDI, fail-closed noncommutation residuals | OPEN |

**World/PG/OpenAI corpus ingestion is postponed**. A source-only manifest exists from an earlier tranche but does not block, accelerate or establish the top-cut theorem. The new cut uses the fork's exact original source in one Lean environment, keeps the old Clay BIDI, and measures actual win only on native local receipts. No CI and no kernel compile occurred during this source inspection.
