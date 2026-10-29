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
| O04 | Eleven C3 class constructors and total classifier `classify11 : Code27 -> Orbit11` | new exact owner; 27-case table | TO IMPLEMENT |
| O05 | Eleven canonical representatives, classifier section, C3 rotation selector | new exact owner | TO IMPLEMENT |
| O06 | Every code is a selected C3 rotation of its representative | 27-case witness; no quotient postulate | TO IMPLEMENT |
| O07 | Classifier unchanged by C3 rotation | 27-case Agda proof | TO IMPLEMENT |
| O08 | Induced odd reflection on 11 classes, involution and naturality | 11-case and 27-case Agda proofs | TO IMPLEMENT |
| O09 | `merge11To7 : Orbit11 -> ShapeOrbit7`; classify-seven factors via 11 | 27-case Agda proof; reuse O03 | TO IMPLEMENT |
| O10 | Three fixed 11 classes and four swapped pairs, exact distinctness | 11-case involution + constructor no-confusion | TO IMPLEMENT |
| O11 | `Field7 -> Field11 -> Field27` pullback and composition | pointwise Agda theorem | TO IMPLEMENT |
| O12 | Both pullbacks injective, via representative sections | pointwise Agda theorem | TO IMPLEMENT |
| O13 | `C3`-invariant iff factors uniquely through 11 | explicit rotation witness and pullback section | TO IMPLEMENT |
| O14 | `S3`-invariant iff factors uniquely through 7 | original seven witnesses and six action laws | TO IMPLEMENT |
| O15 | Ternary function-space counts `3^7`, `3^11`, `3^27` | finite cardinality/bijections; not just arithmetic | TO IMPLEMENT |
| O16 | Fourier C3 action intertwiners, averaging only in char ≠ 2,3 | reuse `PolynomialC3FourierTrialecticChartExact` | CONDITIONAL UNTIL TYPED |
| O17 | Vandermonde alternating action / discriminant invariant | `PolynomialVandermondeDiscriminantExact` | source-written; rational law instantiation outstanding |
| O18 | Compatibility with braid projection `B3 -> S3` | `PolynomialBraidPermutationImageExact` | finite image source; topological braid pending |
| O19 | Compatibility of Q8/2T spin central sign with root S3 parity | genuine intertwiners only; no assumed identity | UNSATISFIED |
| O20 | Quintic actual S5 and A5 derived group, Galois generic quintic | existing #1414 conditional and finite witnesses | INDEPENDENT OPEN |
| O21 | Hatcher genus-one Nielsen wild geometry | #1244 alone; imports only if typed | INDEPENDENT OPEN |
| O22 | Source ownership audit: mathematical authors, repo owners, executed checks, kernel | proof/audit doc and PR | ACTIVE |
| O23 | Exact-head Agda+stdlib compile; all TOE imports; no metas or axioms | verification receipt with pinned commit | NOT RUN |
| O24 | Independent finite script run from exact checked-out commit | attach executable output/sha | NOT RUN |

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
