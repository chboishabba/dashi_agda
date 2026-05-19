# LILA-R2 E8 Root Enumeration Preflight

Date: `2026-05-13`
Status: `Concrete 112/128/240 finite generator surfaces plus executable equality/duplicate/disjointness checks and boolean-backed structural bridge layer available; native structural completeness remains blocked; non-promoting`
Owner: `Cayley / Lane 1 E8 concrete family generation`

`DASHI/Algebra/Trit/E8RootEnumeration.agda` is prepared around the standard
doubled-coordinate E8 root split:

| Family | Shape | Expected count |
|---|---|---:|
| Integer roots | eight coordinates with exactly two nonzero entries, each `+/-2`, ranging over all coordinate pairs and sign choices | `112` |
| Half roots | eight coordinates, every entry `+/-1`, with even minus parity | `128` |
| Combined | disjoint append of integer and half families | `240` |

The preflight now exposes both `Vec HalfTrit 8` and `Vec HalfTritIndexed 8`
as eight-coordinate carrier shapes. The local HalfTrit API is present in
`DASHI/Algebra/Trit/HalfTrit.agda` with constructors `negOne`, `negHalf`,
`zero`, `posHalf`, and `posOne`, but that module explicitly records
`constructsE8RootEnumeration = false`.

`DASHI.Algebra.Trit.HalfTritIndexed` is present and imported by
`DASHI/Algebra/Trit/E8RootEnumeration.agda`. It provides the
`HalfTritIndexed` carrier, the `embedIndexed` map from `HalfTrit`, and an
injectivity proof for that map. It now also provides a concrete `Fin 5`
coordinate index API, both roundtrip laws, decidable equality for
`HalfTritIndexed`, the canonical five-value coordinate list, a length-`5`
proof, and a local no-duplicates witness for that coordinate list. Its receipt
remains explicitly non-promoting: it records coordinate-level duplicate freedom
only, `e8DuplicateFreedomClosedHere = false`, and `constructsPromotionClaim =
false`.

The indexed bridge materially narrowed the previous blocker: E8 has a typed
indexed eight-coordinate carrier and list carrier, plus finite coordinate
equality/all-values support. Lane 1 now adds concrete finite generator
surfaces:

- `allCoordinatePairs8 : List CoordinatePair8`, with `length = 28`
- `integerIndexedRoots : List (Vec HalfTritIndexed 8)`, generated as 28
  coordinate pairs times four sign choices, with normalized `length = 112`
- `integerRoots : List (Vec HalfTrit 8)`, obtained by forgetting indexed
  coordinates back to `HalfTrit`, with normalized `length = 112`
- `halfIndexedRoots : List (Vec HalfTritIndexed 8)`, generated from recursive
  even-parity sign vectors over eight coordinates, with normalized
  `length = 128`
- `halfRoots : List (Vec HalfTrit 8)`, obtained by forgetting indexed
  coordinates back to `HalfTrit`, with normalized `length = 128`
- `combinedIndexedRoots`, appending integer and half indexed families, with
  normalized `length = 240`
- `combinedRoots`, appending integer and half `HalfTrit` families, with
  normalized `length = 240`

These are finite list/cardinality surfaces, not a completed E8 enumeration
receipt. The current length proofs are definitional `refl` witnesses after
normalization of the concrete generators.

The next proof layer is now also present:

- `decEqIndexedRoot`, a root-level decidable equality procedure for
  `Vec HalfTritIndexed n`
- `memberIndexedRoot`, an executable membership check over indexed root lists
- `noDuplicatesIndexedRootList`, an executable no-duplicates check
- `disjointIndexedRootLists`, an executable disjointness check
- `integerIndexedRootsNoDuplicatesCheckIsTrue : ... = true`
- `halfIndexedRootsNoDuplicatesCheckIsTrue : ... = true`
- `integerHalfIndexedRootsDisjointCheckIsTrue : ... = true`
- `combinedIndexedRootsNoDuplicatesCheckIsTrue : ... = true`
- `halfIndexedRootsEvenParityByConstruction`, recording that the half-family
  is exactly the image of `evenSignVectors 8`

The next bridge layer is now present as a boolean-backed structural surface:

- `IndexedRootMember`, inhabited from `memberIndexedRoot ... = true`
- `IndexedRootNoDuplicates`, inhabited from `noDuplicatesIndexedRootList ... = true`
- `IndexedRootFamiliesDisjoint`, inhabited from
  `disjointIndexedRootLists ... = true`
- `HalfIndexedRootParitySound`, inhabited from the explicit even-sign-vector
  construction equality
- `canonicalE8BooleanBackedStructuralBridgeLayer`, packaging:
  - integer-family no-duplicates
  - half-family no-duplicates
  - combined-family no-duplicates
  - integer/half family disjointness
  - half-family parity-by-construction

The exact propositional lift targets are now named in
`canonicalE8NativePropositionalLiftTargets`:

- lift executable membership to native root membership
- lift executable no-duplicates to native `Unique` / no-duplicate structure
- lift executable family disjointness to native disjointness
- lift half-family construction equality to a native even-parity predicate
- lift the integer generator to two-sparse completeness
- lift the half generator to even-parity completeness
- lift the combined generator to E8 completeness

This is deliberately weaker than `E8RootEnumerationComplete`. It packages the
normalized executable checks as typechecked proof objects, but it does not yet
bridge them to native structural predicates for E8 lattice membership,
two-sparse completeness, even-parity completeness, or combined completeness.
The bridge layer records `completesE8RootEnumeration = false`.

Available local machinery includes `Nat`, `List`, `List.length`, `List.map`,
`List.concatMap`, list append, `Vec`, root-level indexed equality/membership
checks, the prepared `Vec HalfTrit 8` and `Vec HalfTritIndexed 8` root-carrier
shapes, and coordinate-level finite support for `HalfTritIndexed`. This is
enough for a typechecked concrete generator/cardinality/executable-check
preflight, not a promotion receipt.

## Remaining Blockers

- bridge from executable indexed membership/equality checks to native
  propositional membership predicates
- bridge from boolean-backed no-duplicate checks to native no-duplicate proofs
- integer-root completeness proof
- half-root even-parity soundness as a structural predicate, beyond the
  construction equality / boolean-backed parity bridge
- half-root completeness proof
- bridge from boolean-backed disjointness check to native structural family
  disjointness
- bridge from boolean-backed combined no-duplicate proof to native combined
  no-duplicate structural proof
- combined completeness proof

The exact native bridge obligations are now also recorded in
`canonicalE8StructuralBridgeResidualObligations`:

- `bridgeExecutableMembershipToNativeMembership`
- `bridgeExecutableNoDuplicatesToNativeNoDuplicates`
- `bridgeExecutableDisjointnessToNativeDisjointness`
- `bridgeEvenSignConstructionToNativeParityPredicate`
- `proveIntegerTwoSparseCompleteness`
- `proveHalfEvenParityCompleteness`
- `proveCombinedE8Completeness`

## Typed Obstruction Fields

`E8RootEnumeration.agda` now records the exact remaining concrete proof
obligations in `canonicalE8RootEnumerationProofObligations`:

- `integerIndexedRootsNoDuplicatesObligation`
- `integerIndexedRootsCompleteForTwoSparseShapeObligation`
- `halfIndexedRootsEvenParitySoundnessObligation`
- `halfIndexedRootsNoDuplicatesObligation`
- `halfIndexedRootsCompleteForEvenParityShapeObligation`
- `integerHalfIndexedRootsDisjointObligation`
- `combinedIndexedRootsNoDuplicatesObligation`
- `combinedIndexedRootsCompleteForE8ShapeObligation`

No LILA-R2 completion, E8 promotion, LILA promotion, or downstream physics
promotion is claimed from this preflight.
