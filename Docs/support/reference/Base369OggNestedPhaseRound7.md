# Base369 Ogg nested phase — Round 7

This tranche separates finite carrier theorems from still-open Monster/modular promotions.

## Exact nonary square

Every nonary digit has one high and one low base-three coordinate. The implementation constructs a two-sided equivalence

```text
NonaryTruth ~= SSPTrit x SSPTrit
```

using the signed digit convention `0 -> sspZero`, `1 -> sspPosOne`, `2 -> sspNegOne`. This is a carrier/address equivalence; it does not identify `Z/9Z` and `F_3^2` as groups or rings.

The low coordinate gives the exact fibres

```text
neutral  : 0,3,6
positive : 1,4,7
negative : 2,5,8
```

and additive complement modulo nine reverses the low SSP trit while fixing neutrality.

## Ogg residue bridge

`MonsterOggNonarySSPTritBridgeExact.agda` connects the existing exact `p = 9q+r` table to `SSPTritCarrier.agda`.

It proves:

```text
p = 3                  -> neutral low trit
Ogg prime p > 3        -> nonneutral low trit
r -> -r mod 9          -> SSP-trit polarity reversal
(complement mode, local orientation) -> canonical SSP residue trit
```

The previous direct/counter orientation is local to each complement mode. Modes `18` and `45` use direct as positive and counter as negative; mode `27` uses the opposite convention. The pair consisting of mode and orientation, rather than orientation alone, recovers the global low residue trit.

This is generic coprimality geometry plus an exact typed bridge. It does not explain why the fifteen Ogg primes are selected.

## Completion and overflow

`Base369CompletedRelationalDigitExact.agda` separates:

```text
nonary address
balanced relational polarity
instantiation/completion
nesting scale
```

The ordinary zero and completed nine share residue zero but have different completion coordinates. A completed nine emits an uninstantiated zero at the next scale. A dependent status family prevents the full raw product from being declared meaningful automatically.

`Base369PhaseCompletionAndNestedEvaluationExact.agda` then distinguishes a completed balanced phase fibre from its observation. Promotion retains the fine negative/neutral/positive sectors in the fibre while producing one coarser state. It keeps separate witnesses for empty zero, balanced evaluation zero and invariant neutral zero.

## Five modes, two phases, nine ordinary states plus completion

`Base369FiveModePhaseQuotientExact.agda` constructs the exact finite theorem

```text
D4IrreducibleType x BinaryOrientation
  ~= PointedNonary10
```

where `PointedNonary10` is nine ordinary states plus `completionJ`. Identifying the two orientations of the distinguished `A1` mode gives a nine-state quotient. This is a carrier model; no actual Monster 5-local action is asserted.

`MonsterFivePrimaryRelationalModelBoundaryExact.agda` states the smallest honest promotion contract. An observer from an actual Monster 5-local carrier must intertwine actual transport with transport on the nine-channel quotient. The entire actual carrier is not required to have nine states.

## One structured 3B carrier, two observers

`Monster3BBalancedRegularFibreExact.agda` organizes the certified 3B numbers as

```text
residual = 53
regular multiplicity = 65610 = 729 * 90
identity evaluation = 53 + 3*65610 = 196883
nontrivial phase evaluation = 53
```

The conformal line gives `196884` at identity and trace `54` at 3B. The complete regular fibres remain present in the fine carrier while contributing zero to the nontrivial phase observer.

## Horizontal phase width versus vertical primary depth

`MonsterOggPrimaryDepthAndNestedEigenCarrierExact.agda` records the exact Monster exponents

```text
2^46 3^20 5^9 7^6 11^2 13^3
17 19 23 29 31 41 47 59 71
```

and separates:

```text
p       = horizontal cyclic phase resolution
v_p(M)  = vertical p-primary depth
```

For each odd Ogg prime, it proves the finite phase decomposition

```text
p = 1 + 2*((p-1)/2)
```

as one fixed phase plus inverse-oriented pairs. Each proposed nested relational cell now carries an explicit `Fin p` phase coordinate as well as its local Base369 cell.

## Exact boundary

The following remain open and are not promoted:

```text
an actual Ogg-indexed nested Monster/modular eigencarrier
Fricke reversal = eigencharacter inversion on one actual carrier
D4 five-mode quotient = actual Monster 5-local representation
an actual nine-channel observer on a Monster 5-local carrier
Base369 trit observations = representation-theoretic irrep labels
nonary carrier geometry = explanation of the Ogg list or genus zero
```

The typed boundaries record exactly the data an actual nested carrier, Fricke/eigen inversion bridge and 5-local relational observer must provide.
