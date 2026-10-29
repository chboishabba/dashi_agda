# Polynomial video → ternary 27-code orbit quotients: max-cut roadmap

Status date: 2026-10-29. Owner: PR #1414 `feat/polynomial-monodromy-ternary-spin-20261028`. This is a new focus-only machine-readable/theorem-led dependency ledger; it complements, does not replace, `Docs/papers/PolynomialMonodromyTernaryQuaternionBridge.md` (45 video concepts).

## Identity and scope rules
- Main carrier `X = DASHI.Cognition.RecursiveFibreTower.LevelTwoCode = TriTruth³`: the 27 **functions** from a 3-element set to itself.
- Existing action `conjugateCode p f = p∘f∘p⁻¹`; the subgroup `C3 = <permRotate> ⊲ S3`.
- (X/C3) has **11 classes** (3 fixed singleton + 8 triple); (X/S3) has **7 classes** (1,2,3,3,6,6,6). Quotient map `11 -> 7` has 4 two-to-one and 3 one-to-one fibres.
- Their trit-valued invariant function spaces contain `3^11` and `3^7` elements; full functions on `X` contain `3^27`. Pullback is injective, NOT a numeric inclusion.
- This is not the `27 -> 9 -> 5` **different** sign/sector orbit quotient in horn PR #1244. It is not the `27 -> 9 = 2+7` FREE **output-phase** quotient owned by `TernaryEndomorphismPhaseQuotientExact`: its seven nonunit classes do NOT biject to the seven S3 conjugacy shapes; `TernarySevenCanonicalMapSeparationExact` already proves the canonical map's image has only three shapes.
- Polynomial ordered-root action, alternating Vandermonde sign and square discriminant have the same abstract S3 source but different carriers. Nothing here identifies a cubic Galois representation, wild exterior, sound-wave medium or Ibrahim Monster 3B.
- No ESD edits. Reuse owners first, then extend, then make new source.

## Dependency graph with precise acceptance gates

| ID | Prerequisite theorem or operation | Existing owner / deliverable | State (2026-10-29) |
|---|---|---|---|
| O01 | Six S3 permutations, multiplication, inverses, C3 embedding | `TernaryPermutationS3LawsExact`, `TernaryPermutationCyclicSubgroupsExact` | existing source; kernel check pending |
| O02 | S3 conjugation on all 27 tables, composition and identity | `TernaryEndomorphismConjugacyExact`, `TernaryEndomorphismS3ActionLawsExact` | existing source; kernel check pending |
| O03 | Seven S3 shapes and representative orbit witnesses | `TernaryEndomorphismConjugacyExact.ShapeOrbit7` | existing source; kernel check pending |
| O04 | Eleven C3 class constructors and total classifier `classify11 : Code27 -> Orbit11` | new exact owner; 27-case table | SOURCE-WRITTEN; KERNEL PENDING |
| O05 | Eleven canonical representatives, classifier section, C3 rotation selector | new exact owner | SOURCE-WRITTEN; KERNEL PENDING |
| O06 | Every code is a selected C3 rotation of its representative | 27-case witness; no quotient postulate | SOURCE-WRITTEN; KERNEL PENDING |
| O07 | Classifier unchanged by C3 rotation | 27-case Agda proof | SOURCE-WRITTEN; KERNEL PENDING |
| O08 | Induced odd reflection on 11 classes, involution and naturality | 11-case and 27-case Agda proofs | SOURCE-WRITTEN; KERNEL PENDING |
| O09 | `merge11To7 : Orbit11 -> ShapeOrbit7`; classify-seven factors via 11 | 27-case Agda proof; reuse O03 | SOURCE-WRITTEN; KERNEL PENDING |
| O10 | Three fixed 11 classes and four swapped pairs, exact distinctness | 11-case involution + constructor no-confusion | SOURCE-WRITTEN; KERNEL PENDING |
| O11 | `Field7 -> Field11 -> Field27` pullback and composition | pointwise Agda theorem | SOURCE-WRITTEN; KERNEL PENDING |
| O12 | Both pullbacks injective, via representative sections | pointwise Agda theorem | SOURCE-WRITTEN; KERNEL PENDING |
| O13 | `C3`-invariant iff factors uniquely through 11 | explicit rotation witness and pullback section | SOURCE-WRITTEN; KERNEL PENDING |
| O14 | `S3`-invariant iff factors uniquely through 7 | original seven witnesses and six action laws | SOURCE-WRITTEN via existing S3 orbit witnesses; KERNEL PENDING |
| O15 | Ternary function-space counts `3^7`, `3^11`, `3^27` | finite cardinality/bijections; not just arithmetic | SOURCE-WRITTEN vector bijections and pow normalizations; KERNEL PENDING |
| O16 | Fourier C3 action intertwiners, averaging only in char ≠ 2,3 | reuse `PolynomialC3FourierTrialecticChartExact` | CONDITIONAL UNTIL TYPED |
| O17 | Vandermonde alternating action / discriminant invariant | `PolynomialVandermondeDiscriminantExact` | source-written; rational law instantiation outstanding |
| O18 | Compatibility with braid projection `B3 -> S3` | `PolynomialBraidPermutationImageExact` | finite image source; topological braid pending |
| O19 | Compatibility of Q8/2T spin central sign with root S3 parity | genuine intertwiners only; no assumed identity | UNSATISFIED |
| O20 | Quintic actual S5 and A5 derived group, Galois generic quintic | existing #1414 conditional and finite witnesses | INDEPENDENT OPEN |
| O21 | Hatcher genus-one Nielsen wild geometry | #1244 alone; imports only if typed | INDEPENDENT OPEN |
| O22 | Source ownership audit: mathematical authors, repo owners, executed checks, kernel | proof/audit doc and PR | ACTIVE |
| O23 | Exact-head Agda+stdlib compile; all TOE imports; no metas or axioms | verification receipt with pinned commit | NOT RUN |
| O24 | Independent finite script run from exact checked-out commit | attach executable output/sha | EXACT COMMITTED AGDA TABLE REPLAYED IN CONNECTOR JS; committed Python full-checkout runner NOT RUN |

## Prioritized worklist / max-cut
P0: O04–O09 construct the explicit intermediate quotient. Verify source and Python finite model separately. If enumeration disagrees with O01–O03, stop and repair.
P1: O10–O15 invariant-field theorem and reflection sector. No arbitrary 5-mode/Monster/quaternion equivalence.
P2: O16–O19 consume only proven action equivariance in Fourier/Vandermonde/braid/spin.
P3: O20 algebraic Abel–Ruffini, O21 geometry remain independently owned; do not hold O04–O15 hostage.
P4: O22–O24 acceptance; record exact versions and unfulfilled obligations. Ignore CI scheduling, never represent its absence as verification.

## Evidence / attribution
Original math: Galois's S3 alternating subgroup, finite orbit theory, Vandermonde discriminant, finite Fourier character theory. Repository owner: original S3 endomorphism, seven-shape, C3 Fourier and phase-quotient modules. New contributor: only explicitly created 11-class quotient and pullback proofs. Existing Ibrahim Monster 3B is retained independently: character matches/number coincidences are not group/object identification.

## Stop conditions / walls
- If original seven-shape classifier or its orbit witnesses do not compile, document actual error and first required lemma.
- If an Agda source uses equality or function extensionality without proof, do not assume it; use pointwise equalities and existing extensional-code owner.
- If a proposed cross-carrier chart lacks an actual commuting action square, do not introduce it.
- The all-important correction: `C3` conjugation classes **11** vs the already existing free **output-phase** C3 quotient **9**, and (3^11) invariant trit fields do not imply (3^9) or (3^5) are the same source space.

## Implementation checkpoint: 2026-10-29

**New source-written owner** `DASHI/Foundations/PolynomialC3S3TwentySevenOrbitQuotientExact.agda`:
- 11 concrete constructors; exhaustive `classify11` table and selected `representative11`; `classifyRepresentative11` section.
- 27-case chosen rotations `rotationToRepresentative`, `codeFromClassRepresentative`, `classify11CycleInvariant`. True orbit equivalence is proved in both directions by `relatedHasSameClass` and `sameClassHasRotation`, using the nine-case group difference/cancellation proof.
- Induced `reflectionOn11`, 11-case involution, 27-case naturality; constructor-exhaustive `reflectionFixedClassIsOneOfThree`, 3 fixed classes and 4 transposed pairs.
- `mergeToSeven` factors the original seven-shape classifier; its reflection invariance and seven-shape representative section are explicit.
- Pullbacks `inflate7`, `inflate11`, `inflate7To27`; commutative composition; pointwise injectivity via sections.
- C3-invariant iff pointwise descent through the eleven classes: `inflate11C3Invariant` plus `everyC3InvariantFieldDescends`; S3-invariant iff descent through the existing seven classes: `inflate7To27S3Invariant` plus `everyS3InvariantFieldDescends`; reflection-invariant eleven-fields iff seven-fields via `inflate7ReflectionInvariant` and `everyReflectionInvariantFieldDescends`.
- Strong **negative result:** `noEquivariantMapFromConjugationToFreeOutputPhase` uses an actual fixed identity code and the original `rotateOutputCodeHasNoFixedPoint` proof. Thus the same `Code27` carrier has NON-EQUIVALENT C3 actions. The `27 -> 11` conjugacy quotient and original `27 -> 9` free-phase quotient must not be equated.
- The earlier `PolynomialC3S3TwentySevenOrbitRefinementExact` now explicitly types its inherited Vandermonde and discriminant aliases.

**New `DASHI/Foundations/PolynomialC3S3OrbitFieldVectorAtlasExact.agda`:** chooses ordering and writes `encode7/decode7`, `encode11/decode11`, and `encode27/decode27` with pointwise two-sided inverse proofs and explicit numeric `3^7=2187`, `3^11=177147`, `3^27=7625597484987`. Vector order is additional data and does NOT commute with arbitrary S3 permutations. Source-written, no actual Agda kernel check. `Fin.suc` applications normalized to nested constructor syntax.

**Independent executed evidence:** local Python exact group enumeration PASS: 27 functions, C3 orbit sizes `1×3,3×8`, S3 sizes `1,2,3,3,6,6,6`, 4 merged pairs/3 fixed, exact dihedral action, and 100 sampled C3-invariant fields factor through the 11 orbit classes. Separately GitHub readback of the **actual committed Agda classifier and representative tables**, analysed directly in connector JS, passed all 729 pairwise C3 orbit-equivalence assertions, 11 representatives and seven-class refinement. These are FINITE COMPUTATION checks, not Agda typechecks. The updated committed Python script now also parses the Agda table from a checkout; **it has not been executed from that checkout**.

**TOE integration:** All three canonical roots import the quotient and vector-atlas owners; no ESD edits. This implementation does not discharge global polynomial analytic monodromy, (S_5/A_5) Galois radical theory, continuous Spin cover, the independent #1244 Hatcher genus-one geometry, or Ibrahim/Monster 3B same-object representation.

### Remaining max-cut
- **KERNEL-P0:** exact-head Agda typecheck and repair source proof elaboration; standard library version/API alignment; check all three TOE import graphs. No CI needed.
- **P1:** function-space cardinality as an imported/first-class cardinality theorem, if the chosen vector bijections and standard `|Vec T n|=|T|^n` owner are not kernel accepted; formal four-paired reflection orbit counts if desired as cardinality rather than no-confusion and table.
- **P2:** the video's alternating Vandermonde sign character vs C2 action on eleven orbit classes. Require an explicit equivariant map/tensor product; shared S3 parity alone is not isomorphism of actions.
- **P3:** Fourier on eleven/seven orbits; construct action/intertwining for a defined coefficient ring and a real operator. No averaging in characteristic three.
- **P4:** independent polynomial radical/Galois, braid topology, continuous Spin, Hatcher wild-geometric obligations remain separately tracked in `PolynomialMonodromyTernaryQuaternionBridge.md`.
- **PROVENANCE:** preserve current owner and original mathematics vs code/executed/kernel receipts, negative-promotion contracts, zero ESD surface changes.
