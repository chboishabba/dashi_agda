# DASHI Exact-Nearest Tékum Rounding Enumeration Receipt

This receipt is DASHI discovery evidence, not Hunhold attribution. All numerical values use exact `fractions.Fraction` and mirror the repository's balanced-ternary, anchor, parser, and exact-rational equations. The discovery script first reproduces the existing finite Proposition-5 counterexample exactly.

## 10→8 exhaustive census

- ordinary 10-trit source words: **59,046**
- ordinary finite 8-trit target words: **6,558**
- source values with a nearest-set tie: **708**
- raw truncations landing on reserved special strings: **24**
- ordinary→ordinary raw truncations: **59,022**
- ordinary raw targets that are not exact-nearest: **29,875**
- maximum absolute raw→canonical-nearest source-code displacement: **6,558**

The displacement maximum equals the entire ordinary 8-trit carrier size, so no small source-code neighbourhood around the raw candidate can implement the exact-nearest oracle uniformly even at 10→8.

A maximum-radius witness has source word (LST first)

`T T 0 T T T T T T T`

with raw 8-trit target

`0 1 1 1 1 1 1 1`

and canonical exact-nearest target

`0 T T T T T T T`.

The source-code displacement is `-6558`.

## 12→10 exhaustive census

- ordinary 12-trit source words: **531,438**
- ordinary finite 10-trit target words: **59,046**
- source values with a nearest-set tie: **712**
- raw truncations landing on reserved special strings: **24**
- ordinary→ordinary raw truncations: **531,414**
- ordinary raw targets that are not exact-nearest: **266,073**
- maximum absolute raw→canonical-nearest source-code displacement: **59,046**

Again the displacement maximum equals the entire ordinary target carrier size. This refutes any width-independent small local correction strategy based on source-code neighbourhood of the raw result.

## Canonical DASHI tie rule used for discovery

When the exact nearest set has more than one target, choose the member with the lower balanced source-integer code. This is intrinsic to the target representation and independent of Python enumeration order. It is a DASHI policy, not source/Hunhold semantics.

## First source-code-minimal 12→10→8 no-double-rounding mismatch

The first ordinary 12-trit source, scanned in increasing balanced source-integer code, for which two-stage and direct canonical exact-nearest rounding differ has source code

`-265591`

and source word (LST first)

`T 0 1 0 0 T T T T T T T`.

Its exact rational value is

`-448599938492324310442483952132513863641390497147438380708009220498080919908972335004317`.

The unique canonical 10-trit nearest value is

`-457064088275198354035738366323693370502548808414371180344009394469742824058198228117606`

at source code `-29510`, word

`1 0 0 T T T T T T T`.

Rounding that 10-trit intermediate to 8 trits is an exact tie between:

- code `-3279`, word `0 T T T T T T T`, value `-685596132412797531053607549485540055753823212621556770516014091704614236087297342176409`;
- code `-3278`, word `1 T T T T T T T`, value `-228532044137599177017869183161846685251274404207185590172004697234871412029099114058803`.

The canonical lower-code tie rule selects code `-3279`.

Direct 12→8 exact-nearest rounding is unique and selects code `-3278`.

Therefore canonical exact-nearest rounding under this intrinsic tie policy does **not** satisfy no-double-rounding:

`round₁₀→₈(round₁₂→₁₀(x)) ≠ round₁₂→₈(x)`.

This is a tie-mediated failure, not a failure of stagewise nearestness.

## Max-cut consequences

1. exact-nearest semantics remains viable;
2. the nearest set is genuinely multi-valued on finite widths, so a separate tie policy is necessary;
3. raw truncation is not a uniformly local approximation to exact nearest in source-code distance;
4. the proposed efficient bounded raw-neighbourhood correction lane is refuted by exact exhaustive data;
5. canonical lower-source-code exact-nearest rounding fails no-double-rounding at 12→10→8, so the global theorem lane stops and becomes an exact falsifier lane.
