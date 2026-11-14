# Conway chained arrows, factorial iteration, and prime-address bridges

## Verified source of the rules

John H. Conway's positive-integer chain semantics (as described in
https://en.wikipedia.org/wiki/Conway_chained_arrow_notation) are not
binary arrow-associative. In particular:

- `2 -> 3 -> 2 = 16`
- `2 -> (3 -> 2) = 512`
- `(2 -> 3) -> 2 = 64`

## Native finite implementation

`DASHI/Foundations/ConwayChainedArrowFiniteBridgeExact.agda`:

- reuses `DASHI.Cognition.RecursiveFibreTower.pow` and `.tetration`;
- defines `up a r b` with rank 0 = exponentiation and rank 1 = tetration;
- defines `three a b (suc r) = up a r b`;
- defines `iterate f n x`, `fourLastTwo a b c`, and `fourLastThree a b c`;
- proves finite wikipedia examples as closed Agda equality terms;
- adds factorial-tower instances separate from hyperoperations.

The four-term identity is

    (a -> b -> 2 -> 2) = (a -> b -> (a^b))

since `a -> b -> 1 = a^b`. For example,
`2 -> 3 -> 2 -> 2 = 2 -> 3 -> 8`: seven Knuth arrows.

## Existing repository consumers and donors

- `DASHI/Cognition/RecursiveFibreTower.agda`: triadic functional tower.
- `DASHI/Biology/SelfIndexingHyperfabricTetrationExact.agda`: 9-valued carrier.
- `DASHI/Foundations/DNATetrationalClosure.agda`: 4-based tower,
  with height offset `tower n = tetration 4 (suc n)`.
- `DASHI/Foundations/PrimorialBaseSequences.agda` and
  `PrimorialFactorAddressConcrete.agda`: primorial addressing, not chained arrows.
- `DASHI/Foundations/WetteArithmeticRepresentationExact.agda`:
  prime exponent/Godel representation, not chained arrows.
- `DASHI/Moonshine/ConwayNortonTheorem.agda`:
  Conway-Norton moonshine, separate from this operator.
- `DASHI/Moonshine/MonsterOggNonaryProbeAuthorityExact.agda`:
  Conway FRACTRAN provenance, separate from this operator.

## Remaining exact max-cut

| Gate | Required closure | State |
|---|---|---|
| C01 | Canonical full positive-list Conway parser and semantics | OPEN |
| C02 | One/two/three-term source examples | SOURCE WRITTEN for two/three |
| C03 | All finite hyperoperation ranks and fixed-base tetration bridge | SOURCE WRITTEN |
| C04 | Four-term terminal 2 and 3 functional iteration | SOURCE WRITTEN |
| C05 | Arbitrary four-term terminal value with general nested recursion | OPEN |
| C06 | General arbitrary-length chains, well-founded reduction proof | OPEN |
| C07 | Source tests and exact-head Agda `--safe` acceptance | OPEN |
| C08 | Domain/positive-index guarantees and factor-address semantic weld | OPEN |

The three- and four-term functions deliberately use a zero-argument
placeholder outside the positive Conway domain. No equality with the
full Conway semantics is claimed for zero-containing input chains.

Do not identify factorial towers, multifactorials, primorials,
prime-factor exponent trees, and chained arrows: they are separate
recursion/representation schemes, which can be connected through a
typed comparison layer if desired.
