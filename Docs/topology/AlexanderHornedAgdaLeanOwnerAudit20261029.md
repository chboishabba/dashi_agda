# Exact-source audit: native ternary meridian / cap-relative geometry

Date: 2026-10-29. Target branch: PR #1244, inspected head 5599dd37a.
Purpose: source-first dependency audit, not another purported geometry proof.

## Agda files actually opened and examined
- `DASHI/Mathematics/Topology/AlexanderHornedBalancedTernaryCommutatorTowerExact.agda`: `refineMeridian` is [child -, child 0][child 0, child +]; `rotate` changes ONLY the EXTERNAL sector; `rotationRefinementCommutes` and `rotationCommutesAllTernaryStages` already establish all-depth naturality for that rotation. Do NOT reprove as child-cycle rotation.
- `DASHI/Mathematics/Topology/AlexanderHornedTernaryPantsMeridianBoundaryExact.agda`: `pantsNotHornByAbelianCharacter` separates four-boundary pants from horn word; `ternaryHornAsGenusTwoSurfaceBoundary` is a syntax-level word construction; `singleCommutatorCyclicWord` is a chosen cyclic conjugate and is not asserted as a syntactic equality of free words.
- `DASHI/Mathematics/Topology/AlexanderHornedC3ExteriorBridge.agda`: `EquivariantMeridianGroup` contains supplied meridian and rotation laws; `interpretExpansion` follows from the assumed refinement. No actual exterior fundamental group supplied.
- `DASHI/Mathematics/Topology/AlexanderHornedTetralemmaRelativeHandleSlideGateExact.agda`: `RelativeHandleSlideSupplier` does not supply any PL topology; `mapFixesStationaryCap` preserves cap membership, not pointwise cap fixation. It is not instantiated by the source.
- `DASHI/Topology/TernaryCylinderPantsGeometryExact.agda`: finite cylinder prefix and pants slot correspondence, expressly combinatorial.
- `DASHI/EverythingTOESymmetryResolved369.agda`: current imports of core ternary tower, boundary, five-orbit, cylinder and tetralemma owners.

## Lean search and coverage limits
Read the GitHub recursive tree for `chboishabba/dashi_lean4` main. It contains imported Agda snapshots and Lean topology files including `RequestProject/OntologyTopology.lean` and `RetractTopology.lean`. GitHub reports `truncated=true` at 38,146 entries: absence of a matching source in these returned entries does not prove absence from the repo. No native Lean theorem of the exact cap-relative wild satellite was verified. Do not claim exhaustive deduplication.

## Exact dependency / no-go correction
The signed 48-case stabilizer excludes pure signed cyclic permutations of the child meridian labels. The separate explicit nonlinear Nielsen order-three automorphism (previous committed audit) preserves the conjugacy class of the parent word, so signed-label obstruction is not a general local-C3 no-go.
The separate `rotate` in the canonical ternary tower is EXTERNAL ROOT-SECTOR rotation, and it already commutes with all refinements. Its theorem is *not* a realisation of the nonlinear local Nielsen automorphism as a geometric finite-order action.

## Highest-alpha remaining cut
1. Exhibit actual complementary child-meridian charts, not merely handlebody core generators or homological dual linking.
2. Construct a specific cap-collar-disjoint PL support and a homeomorphism on that chosen complement, with verified inverse and based path transport.
3. Embed the once-punctured torus in the SAME complement, with its peripheral boundary [a,b][b,c] as a based loop.
4. Prove stage inclusion on actual pi1 and compatibility with external root-sector rotation. A local nonlinear Nielsen action requires a separate order-three geometric realisation check.
5. Construct nested tame stages, shrinking clearances, retained cap collar and actual wildness, then apply open-exhaustion / van Kampen to identify exterior pi1.

No current source inspection discharged (1)-(5). `RelativeHandleSlideSupplier` is weaker than the requested certificate; do not instantiate it with a finite carrier and call it geometry.

## Verification and attribution
This document is a checked source and literature audit, not kernel-checked mathematics. No CI or Agda compile was run. Preserve Alexander (1924), Hatcher *Algebraic Topology* Example 2B.2, classical Nielsen/free-group normal form and Hensel handlebody literature. Preserve existing original DASHI authors and #1414 polynomial, #1405 wave, #1254 pants and prior Ibrahim Monster 3B ownership; do not infer Monster representation or physical acoustics from the numerical chart. Protected ESD surfaces untouched.
