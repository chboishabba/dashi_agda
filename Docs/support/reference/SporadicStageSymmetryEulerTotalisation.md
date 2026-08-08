# Balanced stage symmetry, JMD totalisation, and Euler/Monster separation

This tranche extends the source-faithful JMD v2 transcription without rewriting it.  The poster remains a partial source object:

```text
21 actual sporadic assignments
+ 1 synthetic Co4 card
+ 5 omitted actual sporadic groups.
```

A second, explicitly named **family-compression totalisation** now supplies one concrete total map from all 26 sporadic groups to the 22 Major Arcana.  It preserves all 21 displayed actual-group assignments, assigns the five omissions with written rationales and `declaredSymbolicAuthority`, and exposes all collisions.  It is neither source-forced nor unique.

## 1. Nomenclature and ordinal block structure

`JMDSporadicTarotOrdinalTotalisationExact.agda` records conventional abbreviations and eponyms for all 26 groups, including Mathieu, Conway, Janko, Higman--Sims, McLaughlin, Suzuki, Fischer, Held, Harada--Norton, Thompson, O'Nan, Rudvalis, Lyons, the Baby Monster, and the Fischer--Griess Monster.

The displayed sequence is represented as five ordered blocks:

```text
0..4   Mathieu
5..8   Conway sequence, with synthetic Co4 at 8
9..10  HS / McL
11..14 J1 / J2 / J3 / J4
15..21 Ru / Suz / O'N / Ly / Th / B / Monster.
```

The score carrier keeps four axes separate:

```text
ordinal fit
family fit
mathematical referent fit
narrative fit.
```

In particular, the Janko block has maximal ordinal fit but only weak mathematical forcing of the card narratives.

## 2. Concrete totalisation

The total policy is:

```text
Fi22  -> Strength
Fi23  -> Judgement
Fi24' -> World
He    -> Tower
HN    -> Sun.
```

The first fills the actual-group vacancy hidden by synthetic `Co4`.  The remaining four are declared family-compression collisions:

```text
Fi23  / Baby Monster -> Judgement
Fi24' / Monster      -> World
He    / Suz          -> Tower
HN    / Th           -> Sun.
```

These are symbolic choices with rationales, not group-theoretic identities.  The original `jmdV2Assignment` continues to report all five as source omissions.

## 3. Balanced ternary and retained Stage-5 constituents

`BalancedTernaryStageSymmetryExact.agda` represents a triad as three literal digits in

```text
{-1, 0, +1}.
```

The amplitude is stored only as a projection.  The checked examples are:

```text
+++ -> positive balance (3,0)
++0 -> positive balance (2,0)
+-0 -> balanced count (1,1)
--- -> negative balance (0,3).
```

The central carry equations are division-free:

```text
2 + 1 = 3
3 + 2 = 5
5 + 1 = 6
5 + 3 + 1 = 9
2 * 3 = 6
6 + 3 = 9
3^2 = 9.
```

Stage 5 is therefore not represented by the scalar `5` alone.  Its literal constituent is:

```text
(+++) dot (++0).
```

The `5 -> 3` fallback is implemented as a coarse retraction to the completed `+++` constituent while preserving `++0` as a residual fibre.  A proof field records that the residual is not erased.

## 4. Symmetry type versus amplitude

The symmetry tower distinguishes carrier cardinality from action:

```text
C2             : direct / inverse
C2 x C2        : four-state square
C3             : negative / neutral / positive
C2 x C3        : six-state content-orientation carrier
C3 x C3        : nine-state comparison carrier.
```

The exact cardinalities are `2`, `4`, `3`, `6`, and `9`.  Six retains both readings:

```text
6 = 2 * 3
6 = 9 - 3.
```

At Stage 5 the completed `+++` triad has an `S3` stabiliser tag, while `++0` has only the pair `S2` stabiliser.  The decision coordinate is precisely the distinguished open line.

Counterposition is also separated from inverse.  Full digitwise inversion of `+++` is `---`, while the concrete counterposition `++-` is proved unequal to that inverse.

## 5. Balanced radix tree and 3/6/9 charts

Five and six receive balanced addresses:

```text
5 = (1,-1,-1)_3, represented by 5 + 4 = 9
6 = (1,-1, 0)_3, represented by 6 + 3 = 9.
```

They share the high-order prefix `(1,-1)` and diverge only at the final digit.  `SharedPrefixWitness` records that retained prefix as an ultrametric witness rather than flattening the states to integers.

The simultaneous closure profiles record:

```text
5 = 1*3 + 2,  5+1=6,  5+4=9
6 = 2*3 + 0,  6+0=6,  6+3=9.
```

## 6. Image, hexagram, frame selector, and SSP15

`DialecticSheetFrameSelectorExact.agda` separates:

```text
three binary proposition slots
ternary signed comparison
nine-cell 3x3 relational sheet
six-line lower/upper triad observation.
```

The frame selector returns a dependent witness containing:

```text
frame
condition-one affirmation
condition-two affirmation
synthesis affirmation
glue proof.
```

It does not return only a Boolean.  A finite regression selects a frame in which the two conditions and their synthesis are jointly inhabited.

Image features are typed receipts projected through an explicit context into a hexagram.  Tarot supplies a downstream candidate frame.  Both external prediction and universal-truth promotion are blocked.

The SSP15 signature is indexed by the 15 Ogg-prime lanes:

```text
2,3,5,7,11,13,17,19,23,29,31,41,47,59,71.
```

Each lane retains projected pattern, stabiliser, status, and residual flag.

## 7. The exact 71 and 54/53 arithmetic

The tranche proves:

```text
9^2 = 81
10 + 71 = 81
71 is the declared Ogg-71 lane.
```

It does not construct an invariant 71-dimensional complement or Monster action.

It also records:

```text
196884 = 2430*81 + 54
196883 = 2430*81 + 53
54 = 6*9
53+1 = 54.
```

The authority boundary states that the mod-81 equations are derived coordinate compatibility, not independent evidence for the previously selected `10*3^9 + 54/53` chart and not a canonical 81-block module decomposition.

## 8. Dual 9/10 indexing and the Janko block

`SecondRevolutionJankoTarotExact.agda` proves that every global address 11 through 14 has two simultaneous charts:

```text
11 = 10+1 = 9+2
12 = 10+2 = 9+3
13 = 10+3 = 9+4
14 = 10+4 = 9+5.
```

It maps the local offsets to `J1..J4` and to Justice, Hanged Man, Death, and Temperance exactly as displayed by JMD.  The arithmetic and poster index facts are exact; identification of a stage carrier with a Janko group and derivation of Tarot narrative from group theory remain false.

## 9. Euler and Monster meanings

`EulerMonsterMeaningSeparationExact.agda` separates:

```text
Euler--Lagrange stationarity
Euler characteristic
Euler--Poincare alternating sum
graded Euler supertrace
ordinary Moonshine graded trace.
```

A finite `1,2,1` complex has equal even and odd totals.  The ordinary Moonshine weight-two identity trace is separately recorded as `196884`, with `196883+1=196884`.

A genuine Euler/Moonshine bridge would require a parity-graded complex, a square-zero differential, a group action commuting with that differential, and a proved equality between equivariant supertrace and Moonshine trace.  No such bridge is fabricated here.

## Validation

The cumulative root is:

```text
DASHI.Biology.PointedBulkSporadicTarotEverything
```

and the focused checker remains:

```bash
AGDA_JOBS=1 bash scripts/check_pointed_bulk_sporadic_tarot.sh
```

The checker rejects holes, postulates, unsafe options, and placeholders; checks the retained-residual, symmetry, Ogg, totalisation, Janko, selector, and Euler authority markers; and invokes the pinned Agda 2.9 root.  Kernel acceptance is claimed only after an observed successful workflow run.
