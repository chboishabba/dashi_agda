# Pointed Ternary Bulk, Reduced-53 Orbit Candidate, Sporadic Tarot, and Cabarlah Cross-Pollination

## Purpose

This tranche implements the exact mathematics developed in the attached discussion while preserving the distinction between:

- proved cardinal arithmetic;
- concrete finite carriers and actions;
- candidate orbit anatomy;
- mathematical sporadic-group data;
- symbolic Tarot/Kabbalistic correspondence;
- and historical or political analogy.

The central corrected architecture is:

```text
196884 = (1 + 9) * 3^9 + 54
196883 = (1 + 9) * 3^9 + 53
54     = 1 invariant mode + 53 reduced modes
53     = 1 + 26 * 2                         arithmetic candidate only
```

The branch does not infer a sporadic-group, symmetric-group, sign-twisted, or Monster action from these equalities.

## Exact 196830 pointed ternary bulk

`PointedTernaryBulkExact.agda` replaces ten unexplained copies of the ternary nine-sheet with a concrete carrier:

```text
MarkedOrUnmarkedSite = 1 + nine sheet sites
PointedTernarySheet  = MarkedOrUnmarkedSite x Sheet3
```

Hence:

```text
marker count = 1 + 9 = 10
sheet count  = 3^9 = 19683
bulk count   = 10 * 3^9 = 196830
```

The same count is proved in the equivalent forms:

```text
3^9 + 9 * 3^9 = 196830
3^9 + 3^11    = 196830
```

The interpretation is exact:

```text
all unmarked ternary sheets
+
all ternary sheets with one marked site.
```

The marker coordinate and sheet coordinate carry matching quarter-rotation and vertical-reflection generators. Four rotations return every pointed sheet, and reflection is involutive.

## D4 anatomy of the ten marker labels

The existing raw nine-site representation has:

```text
R[I9] = 3 A1 + B1 + B2 + 2 E
```

and no raw `A2` component. Adding the fixed unmarked label contributes one additional `A1`, giving:

```text
R[1 + I9] = 4 A1 + B1 + B2 + 2 E
```

with exact dimension:

```text
4 + 1 + 1 + 2 * 2 = 10.
```

The raw pointed carrier still has `A2` multiplicity zero.

## Three different ten-element presentations

`DecimalTenTernaryPresentationExact.agda` keeps distinct:

```text
Fin 10
1 unmarked + 9 marked sites
5 D4 irrep species x 2 orientations
```

All have cardinality ten. They are not definitionally the same carrier and do not automatically carry the same action or semantics.

The existing `canonicalTenSectors` supplies the five-irrep-species by two-orientation list. It includes `A2` as an oriented role even though `A2` is absent from the raw nine-site permutation representation. A meaningful bridge from marked sites to irrep/orientation sectors must therefore provide both a carrier equivalence and commuting rotation/reflection observations, together with an explicit source for the `A2` refinement.

## Reduced 53 and the one-fixed-point candidate

The existing repository theorem remains authoritative:

```text
FullMode54 = invariant mode + ReducedMode53
```

where `ReducedMode53 = Fin 53` is the nonconstant or positive-Laplacian mode carrier of the existing six-by-nine fibre.

`ReducedFiftyThreeOrbitCandidateExact.agda` separately constructs:

```text
CandidateR53 = 1 + Fin 26 x C2
```

with an involution that fixes the singleton and exchanges the two points in each of the twenty-six fibres. It proves:

```text
1 + 26 * 2 = 53
involution(involution(x)) = x
```

and proves that the positive and negative points in every binary fibre are nonfixed.

This does not identify `CandidateR53` with the actual `ReducedMode53`. Promotion requires an explicit equivalence and an intertwining involution. Even after that, twenty-six involution orbits are merely twenty-six binary orbits; a further bijective orbit-labelling invariant is required before they can be named after the twenty-six sporadic groups.

## Multiple observers of one C2 fibre

The candidate binary fibre has separate observations into:

```text
even-like / odd-like
direct / inverse
light / shadow
positive / negative orientation
```

These are distinct codomains. They are observers of the same two-point carrier, not claims that permutation parity, transport direction, Tarot polarity, and physical orientation have identical meaning.

A genuine sign representation requires an independently constructed symmetric-group action and parity character. The dependency order is formalised as:

```text
arithmetic cardinality
-> pointed D4 action
-> equivalence with the reduced carrier
-> one-fixed-point involution
-> canonical twenty-six-orbit quotient
-> sporadic orbit labels
-> symmetric permutation action
-> sign-twisted module
-> Monster intertwiner.
```

The sign-twisted stage occurs seven explicit promotions after bare arithmetic.

## Correct sporadic inventory and symbolic Tarot layer

`SporadicTarotDependencyExact.agda` contains all twenty-six sporadic simple-group constructors and the standard family count:

```text
5 Mathieu
+ 7 Leech-lattice groups
+ 8 Monster-section groups
+ 6 pariahs
= 26.
```

It records exactly three Conway sporadic constructors. A `Co4SyntheticCard` is allowed as a symbolic card label but maps to no Conway sporadic referent.

The five Mathieu natural permutation degrees are checked as:

```text
M11: 11
M12: 12
M22: 22
M23: 23
M24: 24.
```

The 22-point Witt-design block arithmetic is checked division-free:

```text
77 * C(6,3) = C(22,3)
77 * 20     = 1540.
```

A Major-Arcana carrier has twenty-two positions, leaving a cardinal deficit of four relative to the complete sporadic inventory. A Tarot mapping is therefore represented by an explicit `TarotCorrespondenceRule` with an assignment, rationale, and authority for every group. Without such a rule, the card system remains a symbolic proposal rather than a mathematical classification.

## Typed dependency graph rather than one linear tower

The visual tower is replaced by edges carrying one of several authorities:

```text
same carrier with stronger axioms
same object in another presentation
construction input
automorphism group
stabiliser or quotient
subgroup or subquotient
vertex-operator-algebra bridge
historical association
symbolic correspondence.
```

The canonical finite graph has sixteen typed edges. This retains the useful pedagogical ascent without pretending that every node canonically generates the next.

## Cabarlah, Palestine, Pine Gap, and reflecting-pool cross-pollination

`CabarlahTraumaProjectionBridgeExact.agda` imports the existing:

- Cabarlah/Palestine historical and authority boundary;
- Indigenous military-intelligence circuit;
- enemy-abstraction boundary;
- and trauma-memory sublation boundary containing the reflecting-pool and executive-residence observations.

It keeps four roles distinct:

```text
Palestine / Amalek       -> absolute-enemy compression
Cabarlah / Borneo        -> military legibility and memory
Pine Gap                 -> Indigenous-Country intelligence circuit
Reflecting Pool          -> symbolic national-image defect attribution.
```

A shared candidate sequence

```text
unresolved injury or defect
-> compressed external carrier
-> mobilised response
```

is retained only as a descriptive cross-lane mechanism. The aggregate reuses the existing proofs that:

- reflecting-pool symbolism does not establish factual motive;
- prior injury does not authorise civilian harm;
- the Indigenous-Australian/Amalek comparison is structural only;
- Pine Gap protest demands include both land return and Palestine justice;
- and those demands do not publicly verify a link to a particular strike.

## Sources

`PointedBulkSporadicTarotSourceAtlas.agda` records four bounded source records:

- J. H. Conway, R. T. Curtis, S. P. Norton, R. A. Parker, and R. A. Wilson, *Atlas of Finite Groups: Maximal Subgroups and Ordinary Characters for Simple Groups*, Oxford University Press, 1985, ISBN `0-19-853199-0`; no DOI assigned;
- R. T. Curtis, *Natural Constructions of the Mathieu Groups*, DOI `10.1017/S0305004100068158`;
- William Fulton and Joe Harris, *Representation Theory: A First Course*, DOI `10.1007/978-1-4612-0979-9`;
- Richard E. Borcherds, *Monstrous Moonshine and Monstrous Lie Superalgebras*, DOI `10.1007/BF01232032`.

Each source carries an imported role and an excluded promotion.

## Authority boundary

The implementation does not claim:

- that decimal notation creates a group action;
- that the three ten-element presentations are canonically identical;
- that the raw nine-site or pointed-site representation contains `A2`;
- that `53 = 1 + 26 * 2` constructs an involution on the actual reduced carrier;
- that twenty-six binary orbits are automatically the sporadic groups;
- that an `S26` action or sign character may be reused without construction;
- that a twenty-two-card deck is a complete sporadic inventory;
- that a synthetic `Co4` card is a sporadic simple group;
- that every exceptional-object relation is one canonical implication;
- that a coefficient identity constructs the Moonshine module;
- or that a shared political projection shape makes distinct histories identical.

## Validation

The focused checker is:

```bash
AGDA_JOBS=1 bash scripts/check_pointed_bulk_sporadic_tarot.sh
```

It cascades through the existing conscious-access Round Five checker and the Cabarlah-Palestine checker, rejects holes, postulates, unsafe escapes and placeholder right-hand sides, verifies the principal scope guards, and invokes the pinned Agda 2.9 toolchain on:

```text
DASHI.EverythingPointedBulkSporadicTarot
```
