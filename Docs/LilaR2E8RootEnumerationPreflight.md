# LILA-R2 E8 Root Enumeration Preflight

Date: `2026-05-13`
Status: `Concrete 112/128/240 finite generator surfaces available; proof obligations remain blocked; non-promoting`
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

Available local machinery includes `Nat`, `List`, `List.length`, `List.map`,
`List.concatMap`, list append, `Vec`, the prepared `Vec HalfTrit 8` and
`Vec HalfTritIndexed 8` root-carrier shapes, and coordinate-level finite
support for `HalfTritIndexed`. This is enough for a typechecked concrete
generator/cardinality preflight, not a promotion receipt.

## Remaining Blockers

- integer-root membership decision and root equality bridge
- integer-root no-duplicate proof
- integer-root completeness proof
- half-root membership decision, root equality bridge, and even-parity proof
- half-root no-duplicate proof
- half-root completeness proof
- family disjointness
- combined no-duplicate proof
- combined completeness proof

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
