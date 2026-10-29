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

## Pareto snowball continuation: actual orbit-sampling operators, no characteristic-three division

Source-written `DASHI/Foundations/PolynomialC3S3OrbitSamplingProjectionExact.agda` defines the natural chosen-representative sampling maps on `Field27`:
`P_C3(f)(x) = f(representative11(classify11(x)))`, and
`P_S3(f)(x) = f(Shape.shapeRepresentative(Shape.shapeClass(x)))`.
It source-writes:
- `projectC3Idempotent`, `projectS3Idempotent`: both retractions satisfy `P²=P` pointwise.
- `projectC3Invariant`, `projectS3Invariant`: their ranges lie in the respective fixed-point/invariant-field spaces.
- `projectC3FixesInvariant`, `projectS3FixesInvariant`: every field invariant under the relevant original permutation action is fixed by its projector, establishing exact range.
- `chosenSevenRepresentativeIsElevenRepresentative`: the original seven-shape representatives coincide with the selected representatives of their eleven C3 classes. This is a REAL typed compatibility identity, checked by seven constructor cases, not a cardinality match.
- `projectC3AfterS3IsS3`, `projectS3AfterC3IsS3`: the projections absorb in both orders, `P_C3 P_S3 = P_S3 P_C3 = P_S3`.

Mathematical receiver: idempotent invariant-field normalization. This is **not** the character-theoretic Fourier-average `(1/|G|) Σ_g g·f`; it works on three-valued fields in characteristic three without a division operation, but it depends on chosen representative order. Do not call it a canonical orthogonal projection or physically calibrated wave operator.

Independent executed Python check: 100 finite random 27-fields verified both idempotences and two-sided absorption using consistent nested orbit representatives. Agda original-source heads were read back, but Agda kernel, exact full-checkout Python runner and CI remain unrun. No ESD edit, no external owner or Ibrahim Monster 3B status change.

**Prioritized obligation O25**: pin Agda/stdlib and type-check this actual sampling projector and 7/11/27 vector atlas; repair any elaboration failure.
**O26**: if useful for the video's phase/Fourier representation, instantiate a true scalar `C3`-character transform on `Field11` with explicit source/target ring, compare `P_C3,P_S3` to the corresponding averaging projectors ONLY after confirming the correct coefficient extension/characteristic and action intertwiner.


## 29 October continuation: executed rational Reynolds / C2-character max-cut

Source-written independent script committed in PR #1414 at `scripts/check_polynomial_c3_s3_reynolds_character_exact.py`, commit `a402835d980bcebd42b553469eaa434faf416622`. A locally executed equivalent exact Fraction-based Python script PASSED 24 independent rational-valued 27-state field trials and full finite group orbit/character counts. **The committed script has not been re-executed from the remote checkout** and the Agda kernel has not been run.

**Historical original mathematical authority:** finite-group character theory, Burnside's orbit lemma, Reynolds averaging and the C2 ±-character projectors (not new DASHI discoveries). General finite-field Reynolds averaging requires invertible group order; the current experiment uses **rationals**, not trits or characteristic 3. See MathWorld Reynolds Operator, https://mathworld.wolfram.com/ReynoldsOperator.html, and primary published invariant-theory expositions. Cite original historical authors when dating a priority claim; treat this numeric experiment as independent implementation only.

**Exact action:** S3 conjugates all 27 functions from a 3-element set to itself. Character traces (fixed-code counts) are identity 27, nonidentity 3-cycles 3, and transpositions 3. Burnside gives C3 invariant dimension `(27+3+3)/3=11` and S3 invariant dimension `(27+2·3+3·3)/6=7`. On 11 C3 classes, reflection has exactly three fixed classes and four exchanged pairs. Hence the rational `C3`-invariant subspace decomposes as seven reflection-even and four reflection-odd coordinates, with genuine idempotent operators:
`R3 f = (f + rotate f + rotate² f)/3`;
`R6 f = (sum_{p in S3} p·f)/6`;
`Pplus f = (R3 f + reflect(R3 f))/2 = R6 f`;
`Pminus f = (R3 f - reflect(R3 f))/2`.
The test confirms `R3²=R3`, `R6²=R6`, `R3 R6=R6 R3=R6`, `R3=Pplus+Pminus` pointwise, reflection sign on minus, and zero S3 average for minus. All of these are classical consequences of the group action, not kernel-verified Agda theorems in this commit.

**Strict owner distinction:** existing `PolynomialC3S3OrbitSamplingProjectionExact.agda` defines CHOSEN-REPRESENTATIVE sampling, which is defined on trit-valued fields and is not linear Reynolds averaging. The new script evaluates the same literal 27-code conjugation action over rational function values; no identification of those two operators is claimed. Four antisymmetric coordinates are justified in this rational representation, strengthening the previous `11=7+4` bare coordinate count for a **new, typed coefficient domain**. This is not Fourier on `F3`, not a physical wave operator, not a Monster representation and not the free output-phase `27→9` quotient.

**Worklist status update:** 
- [x] O27 finite rational Reynolds and character trace receipt (exact local script execution, standalone GitHub script committed; exact checkout execution pending).
- [x] O28 rational 7-even/4-odd representation decomposition finite regression.
- [ ] O29 source-write an Agda theorem over explicit rational coefficient carrier and literal S3 action; reuse existing abstract finite-sum/group character theorem owners first; no trit-field division.
- [ ] O30 check the exact committed script on branch head and run Agda kernel with pinned stdlib (CI unnecessary).
- [ ] O31 investigate conditional objective/count-preservation connections to OpenAI ETH family counting or Max-Cut **only** after a concrete same-problem graph/CNF action and polynomial encoding bound. Maintain independent #1260 radian Pickover sign problem and original #1414 Galois/Spin/Hatcher obligations.
- [ ] O32 original-prior-art ledger and repository proof ownership: label Burnside/Reynolds as inherited mathematics, #1414 as code owner, #1260 as prior Pickover arithmetic source, exact executed arithmetic check, kernel-pending status, unchanged Ibrahim Monster 3B ownership.

**Negative control corrected during experiment:** transposition has **3 fixed codes**, not 7; seven is the number of `S3` orbits. Conflating these counts breaks Burnside. Script enforces all three conjugacy-class fixed counts.

## Highest-alpha follow-up, 29 October: actual S3 parity character and F3 reflection Fourier

**Why this is a genuine connection:** the *same* sign quotient `S3 -> S3/C3 ≅ C2` operates on (i) the video's alternating Vandermonde on ordered rational cubic roots and (ii) the involution of the **11 genuine conjugacy classes** of the 27 native trit endomorphisms. These are different S3 representations. Their shared source is the sign character, not a bijection of their carriers, Monster identity, physical gauge equivalence or an Hatcher wild-space identification.

**New proof owners, added to all three TOE root imports:**
- `PolynomialC3S3ReflectionParityFourierExact.agda`: scalar chart `TriTruth≃Phase3≃F3`; on each of four reflection-swapped pairs `e=(a+b)/2`, `o=(a-b)/2` where `1/2=2=-1` in F3. Proves all six nine-case scalar identities, defines `Field11 ↔ (Field7 × Odd4)`, source-writes all 11 field decode-after-encode cases, 7 even and 4 odd encode-after-decode cases, and that reflection fixes even coordinates while negating all four odd coordinates. This is **C2** Fourier in characteristic three; C3 averaging by 1/3 would be invalid. The choice of four ordered pairs is explicit.
- `PolynomialC3S3ReflectionParityLinearExact.agda`: reuses the original `Phase3` addition. Four independent 81-clause scalar proofs show even averaging, odd half-difference and both reconstructions preserve addition; lifts them to seven even slots, four odd slots, and decoding of all eleven slots. Thus the two-sided chart respects addition; it is more than a numeric equality `3^11=3^7·3^4`.
- `PolynomialVandermondeOrbitParityIntertwinerExact.agda`: `S3 -> Stage.C2` parity homomorphism in 36 explicit source cases, action of C2 on `Orbit11`, six-element S3 action and 162 total source cases that original `conjugateCode` classification intertwines it; reuses the original cubic Vandermonde `sign` proof to factor both representations through the same parity. No map from rational root triples to 11 tables is claimed.
- `PolynomialVandermondeOrbitSignCharacterExact.agda`: full S3 pullback of eleven-class fields; even seven coordinates fixed and the four odd coordinates carry the sign character under all six permutations, 24 explicit odd-coordinate proof cases.
- `PolynomialS3TwentySevenPermutationCharacterExact.agda`: enumerates exactly 27 endomorphism codes and counts six original conjugation-map fixed sets: `[27,3,3,3,3,3]`. Burnside arithmetic reproduces S3 seven orbits and C3 eleven orbits. The **characteristic-zero S3 character table** numerically reconstructs `7 trivial ⊕ 4 sign ⊕ 8 standard(2D)`: dimension 27, 3-cycle trace 3, reflection trace 3. This is a character-level calculation and requires a separate Maschke/representation reconstruction receipt before an actual direct-sum module isomorphism is called kernel-proved. Over **F3**, S3 has order 6 divisible by 3 and full semisimplicity does NOT follow; the only F3 splitting proved here is the C2 action on the eleven C3-invariant coordinates.
- New reproducible checkout checker: `scripts/check_polynomial_s3_c2_reflection_fourier_20261029.py`. It parses current Agda source tables and checks all 729 C3-orbit pairs, 162 S3 sign actions, six fixed-count values, six nine-case scalar sets, 324 scalar additivity cases, 24 odd sign proof clauses, and all 177147 function tables for the 11-dimensional split.

**Evidence actually executed this turn:** independent Python exact arithmetic exhaustively tested all `3^11=177147` eleven-value fields for two-sided coordinate reconstruction and reflection parity (PASS); verified `[27,3,3,3,3,3]` fixed-point counts and seven/eleven orbit partitions (PASS). Separately, connector JS read the exact committed Agda sources and checked all 162 parity/classifier cases, all 36 parity-group cases, and 324 source-written arithmetic lemma case lines against the independent F3 formulas (PASS). These are computational checks, NOT AGDA KERNEL PROOFS. The **committed checkout checker script** itself was not executed against a cloned GitHub branch in this session; the container cannot fetch the repo and no Agda compiler is installed.

### Expanded follow-up obligations O27–O36

| ID | Dependency / acceptance test | Status |
|---|---|---|
| O27 | Construct explicit F3-valued four-pair C2 even/odd Fourier chart `Field11 ↔ Field7 × Odd4` | SOURCE-WRITTEN; kernel pending |
| O28 | Prove pointwise forward/backward inverses and reflection action (+1 on 7, -1 on 4) | SOURCE-WRITTEN; kernel pending; 177147 independent checks PASS |
| O29 | Prove encoding/decoding preserve actual F3 addition, not only cardinality | SOURCE-WRITTEN; kernel pending; 324 scalar cases PASS |
| O30 | Instantiate actual `S3->C2` parity and 162-classifier action, reusing original S3 carrier | SOURCE-WRITTEN; kernel pending; 162 source cases independently checked |
| O31 | Connect polynomial Vandermonde sign and four odd orbit coefficients by sharing the same parity character, not carrier identity | SOURCE-WRITTEN; kernel pending |
| O32 | Compute actual six-permutation fixed-point trace `[27,3,3,3,3,3]`, Burnside orbit counts 11/7 | SOURCE-WRITTEN; kernel pending; independent exact count PASS |
| O33 | Import/build characteristic-zero irreducible S3 character table, semisimplicity, uniqueness, and obtain an *actual* rational module equivalence `Q^27 ≃ 7·triv⊕4·sign⊕8·std` | OPEN; numerical character consistency alone is insufficient |
| O34 | Preserve modular distinction: char(F3)=3 divides |S3|=6; **do not** infer full F3 S3 semisimplicity from O27–O32 | NEGATIVE GATE, ACTIVE |
| O35 | Execute exact committed checkout checker and pin Agda/stdlib/TOE kernel receipts; repair any real errors, do not worry about CI | OPEN |
| O36 | Continue the separately tracked actual analytic polynomial root monodromy, generic quintic Galois/radicals, continuous spin, wild Hatcher and Ibrahim/Monster attribution gates | INDEPENDENT, OPEN |

**Highest-alpha next cut:** kernel acceptance of actual owners; then O33 for a genuinely proved characteristic-zero representation decomposition; or a lawful field-valued Fourier diagonalization of the full S3 action after establishing its actual coefficient representation. No new 3/6/9 numeric coincidence is needed. Original historical mathematical authors, repo owners, source-written, executed computational evidence and kernel receipts remain separately attributed.

### Original-source representation construction for O33 (donor search completed)

A repository code search for exact S3 standard/permutation representation owners found no directly reusable matching S3 decomposition; existing `IbrahimMonster*PermutationCharacter*` and `IbrahimMonsterCharacterToTwoIsotypicBlocksMathlibSnowballExact` are distinct owned Monster-character results, and their receipt/attribution discipline is reusable but not their mathematical object identity.

The source-derived **constructive route** is shorter than a generic character-reconstruction postulate: the original seven S3 conjugacy orbits have actual sizes `1,2,3,3,6,6,6`. Over a characteristic-zero field, the permutation representation of a:
- size-1 orbit gives `trivial`;
- size-2 orbit gives `trivial ⊕ sign` (permutation of the two cosets of C3);
- size-3 orbit gives `trivial ⊕ standard₂`, each of the two 3-orbits;
- size-6 orbit gives the regular representation `trivial ⊕ sign ⊕ 2·standard₂`, each of the three regular orbits.

Adding the actual orbit owners yields `7·trivial ⊕ 4·sign ⊕ 8·standard₂` at dimension 27, with exactly the six fixed-point trace values already source-computed. This is **mathematical consequence of classical characteristic-zero S3 representation theory**, not a newly kernel-verified code-level equivalence in #1414. Actual next formal obligation: construct (or import) S3-stable orbit vectors and explicit invertible block-intertwining matrices for the size-2,3,6 components; prove the original 27 table-code action is conjugate to their disjoint union, then glue the block maps.

External sources/preserved attribution: Serre, *Linear Representations of Finite Groups* (1977); Pavel Etingof and colleagues, *Introduction to Representation Theory* (MIT notes, https://klein.mit.edu/~etingof/reprbook.pdf); Princeton lecture *Modular Representations of Symmetric Groups*, ordinary/Brauer character table of S3 (https://web.math.princeton.edu/~charchan/ModularRepresentationsSymmetricGroupSeminar); Maithani, 2025, Reynolds operator (DOI 10.1112/blms.70175); Mathlib4's original `Equiv.Perm.sign` group homomorphism (https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/Sign.html). Original repository character code and Ibrahim Monster 3B ownership remain independent.

### Final source-level reuse cut before characteristic-zero representation wall: O37–O40

Instead of creating a duplicate 27-state group owner, `PolynomialC3S3OrbitFieldVectorAtlasExact.agda` was EXTENDED in place:
- `codeForIndex27 : Fin 27 -> Code27`, `indexCodeRoundTrip` and `codeIndexRoundTrip`: literal 27-index chart with 54 two-sided constructor equations. This is an actual carrier equivalence using the existing `index27`, not a 27=27 count.
- `transportS3OnIndex27`, `transportIndexIdentity`, `transportIndexComposition`: transports the original S3 conjugacy action to the finite 27-index carrier, using the ORIGINAL `TernaryEndomorphismS3ActionLawsExact` group-action proofs.
- `transportIndexPreservesShape`: all S3 index transports stay in the original seven-shape orbit block; proof reuses `shapeClassInvariant` and the lossless chart.
- `transportIndexParity`: the square `Fin27 -> Code27 -> Orbit11` is equivariant for the exact parity action `S3 -> C2` constructed earlier. This is a compositional operation-preserving bridge, not an identification with polynomial root positions.
- All three TOE roots export these names under the ORIGINAL vector-atlas import rather than creating a new duplicate module.

Independent GitHub SOURCE readback checked 27 index cases in the lexicographic order of original ternary codes, and both sets of 27 inverse declarations (PASS). Original S3 composition source and earlier exact 162 code action checks support the finite mathematics. **No Agda kernel proof receipt.**

| ID | Formal requirement | Status |
|---|---|---|
| O37 | Complete two-sided code/index chart `Code27 ≃ Fin27` | SOURCE-WRITTEN; exact source-table readback PASS; kernel pending |
| O38 | Transport existing S3 action to `Fin27`; prove identity and composition | SOURCE-WRITTEN; kernel pending |
| O39 | Prove seven-shape block preservation and parity-square commutativity after transport | SOURCE-WRITTEN; kernel pending |
| O40 | Construct explicit characteristic-zero S3 intertwiners on the seven invariant orbit blocks of sizes 1,2,3,3,6,6,6 and assemble an actual `Q^27 ≃ 7 triv ⊕ 4 sign ⊕ 8 std₂` S3-module isomorphism | OPEN; representation matrices and exact-head kernel witness required |

With O37–O39 the group-set/coarse-quotient side is source-complete at the existing finite carrier level. The next mathematical wall is **not** numeric: a characteristic-zero block-intertwiner theorem (O40) and compiler/kernel acceptance of the existing source; separately, actual continuous polynomial braid and Galois results remain open. No CI work is needed, but no CI absence can be confused with successful kernel checking.
