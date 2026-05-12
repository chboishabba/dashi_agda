# LILA-R2 E8 Root Enumeration Preflight

Date: `2026-05-13`
Status: `HalfTrit available; blocked on enumeration/cardinality machinery; non-promoting`
Owner: `Turing / Lane 2 E8 root enumeration`

`DASHI/Algebra/Trit/E8RootEnumeration.agda` is prepared around the standard
doubled-coordinate E8 root split:

| Family | Shape | Expected count |
|---|---|---:|
| Integer roots | eight coordinates with exactly two nonzero entries, each `+/-2`, ranging over all coordinate pairs and sign choices | `112` |
| Half roots | eight coordinates, every entry `+/-1`, with even minus parity | `128` |
| Combined | disjoint append of integer and half families | `240` |

The preflight uses `Vec HalfTrit 8` as the future eight-coordinate carrier
shape. The local HalfTrit API is present in
`DASHI/Algebra/Trit/HalfTrit.agda` with constructors `negOne`, `negHalf`,
`zero`, `posHalf`, and `posOne`, but that module explicitly records
`constructsE8RootEnumeration = false`.

## Missing Fields

- root equality decision
- concrete `integerRoots : List (Vec HalfTrit 8)` enumerator
- concrete `halfRoots : List (Vec HalfTrit 8)` enumerator
- no-duplicate predicate/proof bridge for root lists
- list/Vec cardinality bridge connecting no-duplicate lists to `112`, `128`,
  and `240`
- integer pair/sign count proof
- half-family even-parity count proof
- disjointness and completeness proofs

No LILA-R2 completion, E8 promotion, LILA promotion, or downstream physics
promotion is claimed from this preflight.
