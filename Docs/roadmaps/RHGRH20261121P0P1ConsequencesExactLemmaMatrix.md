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
