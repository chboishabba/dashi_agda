# Balanced stage symmetry, JMD totalisation, and Euler/Monster separation

This tranche extends the source-faithful JMD v2 transcription without rewriting it. The poster remains a partial source object:

```text
21 actual sporadic assignments
+ 1 synthetic Co4 card
+ 5 omitted actual sporadic groups.
```

A second, explicitly named **family-compression totalisation** supplies one concrete total map from all 26 sporadic groups to the 22 Major Arcana. It preserves all 21 displayed actual-group assignments, assigns the five omissions with written rationales and `declaredSymbolicAuthority`, and exposes all collisions. It is neither source-forced nor unique.

## 1. Nomenclature and ordinal block structure

`JMDSporadicTarotOrdinalTotalisationExact.agda` records conventional abbreviations and eponyms for all 26 groups. The displayed sequence is represented as five ordered blocks:

```text
0..4   Mathieu
5..8   Conway sequence, with synthetic Co4 at 8
9..10  HS / McL
11..14 J1 / J2 / J3 / J4
15..21 Ru / Suz / O'N / Ly / Th / B / Monster.
```

The score carrier keeps ordinal, family, mathematical-referent, and narrative fit separate. The Janko block therefore has maximal ordinal fit but only weak mathematical forcing of its card narratives.

## 2. Concrete totalisation

The declared total policy is:

```text
Fi22  -> Strength
Fi23  -> Judgement
Fi24' -> World
He    -> Tower
HN    -> Sun.
```

The first fills the actual-group vacancy hidden by synthetic `Co4`. The remaining four are declared family-compression collisions:

```text
Fi23  / Baby Monster -> Judgement
Fi24' / Monster      -> World
He    / Suz          -> Tower
HN    / Th           -> Sun.
```

These are symbolic choices with rationales, not group-theoretic identities. The original `jmdV2Assignment` continues to report all five as source omissions.

## 3. Balanced ternary and retained Stage-5 constituents

`BalancedTernaryStageSymmetryExact.agda` represents a triad as three literal digits in `{-1,0,+1}`. The amplitude is only a projection. Checked examples include:

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

Stage 5 is not represented by the scalar `5` alone. Its literal constituent is `(+++) dot (++0)`. The `5 -> 3` fallback is a coarse retraction to `+++` while preserving `++0` as a residual fibre; `residualErased = false` is proved.

## 4. Symmetry type versus amplitude

The symmetry tower distinguishes carrier cardinality from action:

```text
C2             : direct / inverse
C2 x C2        : four-state square
C3             : negative / neutral / positive
C2 x C3        : six-state content-orientation carrier
C3 x C3        : nine-state comparison carrier.
```

The exact cardinalities are `2,4,3,6,9`, and six retains both readings `6=2*3=9-3`. At Stage 5, `+++` has an `S3` stabiliser tag while `++0` has only `S2`. Counterposition is separated from inverse: full inversion of `+++` is `---`, while `++-` is proved unequal to it.

## 5. Balanced radix tree, ultrametric, and 3/6/9 charts

Five and six receive balanced addresses:

```text
5 = (1,-1,-1)_3, represented by 5 + 4 = 9
6 = (1,-1, 0)_3, represented by 6 + 3 = 9.
```

`BalancedTernaryUltrametricExact.agda` proves symmetry and transitivity of prefix agreement, constructs prefix balls, and proves that five and six agree through depth two. It gives the exact valuation-depth form of the ternary ultrametric without falsely claiming a real-valued metric, and suffix constituents remain retained.

## 6. Image, hexagram, and inhabitable-frame selector

`DialecticSheetFrameSelectorExact.agda` separates:

```text
three binary proposition slots
ternary signed comparison
nine-cell 3x3 relational sheet
six-line lower/upper-triad observation.
```

The selector returns a dependent witness containing the frame, two affirmation proofs, synthesis affirmation, and a glue proof. Image features are typed receipts projected through an explicit context into a hexagram; Tarot supplies a downstream candidate frame. External prediction and universal-truth promotion are blocked.

## 7. Tetralemma over carrier, cubie, and binary decision policy

`DialecticCubieTetralemmaExact.agda` formalises the tetralemma as:

```text
SupportCounterSquare x retained prior carrier.
```

The four support positions therefore classify a carrier without erasing it. A third ternary context axis turns the `3x3` comparison sheet into a 27-position cubie carrier. Positions and ternary three-slot states are not identified merely because both have cardinality 27.

Two explicit ternary-to-binary decision policies are constructed:

```text
positive-only
nonzero.
```

They are proved to disagree on a negative observation, so Stage-5 commitment cannot silently appeal to a unique canonical quotient. A hyperfabric record retains cubies plus an incidence relation and a separate gluing-witness flag; a cubie list alone does not prove a manifold.

## 8. Reused SSP15/Ogg multiscale signature

`StageSymmetrySSP15BridgeExact.agda` reuses, rather than redefines, the established:

```text
MoonshinePrimeLaneReceiptSurface.MonsterPrimeLane
SupersingularPrimeLaneBridge.canonicalSupersingularPrimeLaneNats
MonsterOggPrimeCorrectionReceipt.
```

The SSP15 signature is indexed by the existing lanes:

```text
2,3,5,7,11,13,17,19,23,29,31,41,47,59,71.
```

Each lane retains projected pattern, stabiliser, status, and residual flag. A lane does not replace the underlying carrier and does not promote physical Moonshine.

## 9. Exact 71 and 54/53 arithmetic

The tranche proves:

```text
9^2 = 81
10 + 71 = 81
196884 = 2430*81 + 54
196883 = 2430*81 + 53
54 = 6*9
53+1 = 54.
```

The mod-81 equations are derived coordinate compatibility, not independent evidence for `10*3^9+54/53`, a canonical 81-block module, or an invariant 71-dimensional Monster complement.

## 10. Signed sporadic 53 carrier and 22-card observer

`SporadicSignedFiftyThreeTarotProjectionExact.agda` reuses the existing binary-fibre observers and constructs the concrete carrier:

```text
SporadicSigned53 = 1_star + (SporadicGroup x C2).
```

It proves:

```text
26*2 = 52
1+26*2 = 53
1+(1+26*2) = 54
196830+(1+26*2) = 196883
196830+(1+(1+26*2)) = 196884.
```

The involution fixes the distinguished centre and flips each binary fibre. Group, polarity, sign, transport, light/shadow, and orientation are separate projections.

A downstream Arcana observer uses the concrete totalised correspondence. Both polarities of a group share a card while retaining distinct light/shadow observations. The centre card is an explicit parameter; the canonical example chooses The World but does not claim that choice is source-forced or that the centre is the modular `q^{-1}` vacuum.

The module also records the dimension ledgers suggested by:

```text
1_star + P26 + (P26 tensor sign)
1_star + 1 + sign + V25 + (V25 tensor sign).
```

No `S26` representation, sign-twisted module, ReducedMode53 equivalence, or Monster intertwiner is fabricated. The Kabbalistic layer is retained only as a 22-slot carrier because the supplied poster does not provide a complete Hebrew-letter or Tree-of-Life incidence map.

## 11. Dual 9/10 indexing and Janko block

`SecondRevolutionJankoTarotExact.agda` proves:

```text
11 = 10+1 = 9+2
12 = 10+2 = 9+3
13 = 10+3 = 9+4
14 = 10+4 = 9+5.
```

It maps the offsets to `J1..J4` and Justice, Hanged Man, Death, and Temperance exactly as displayed. Arithmetic/poster facts are exact; stage-carrier identity with a Janko group and derivation of Tarot narrative from group theory remain false.

## 12. Euler and Monster meanings

`EulerMonsterMeaningSeparationExact.agda` separates:

```text
Euler--Lagrange stationarity
Euler characteristic
Euler--Poincare alternating sum
graded Euler supertrace
ordinary Moonshine graded trace.
```

A finite `1,2,1` complex has equal even and odd totals. The ordinary Moonshine weight-two identity trace is separately `196884`, with `196883+1=196884`. A genuine Euler/Moonshine bridge would require a parity-graded complex, square-zero differential, commuting group action, and proved equivariant-supertrace equality. No such bridge is fabricated.

## Validation

The cumulative root is:

```text
DASHI.Biology.PointedBulkSporadicTarotEverything
```

The focused checker is:

```bash
AGDA_JOBS=1 bash scripts/check_pointed_bulk_sporadic_tarot.sh
```

It rejects holes, postulates, unsafe options, and placeholders; checks retained residuals, ultrametric laws, symmetry, tetralemma/cubie boundaries, reused SSP15/Ogg, totalisation, signed 53 projection, Janko, selector, and Euler authority markers; and invokes the pinned Agda 2.9 roots. Kernel acceptance is claimed only after an observed successful workflow run.
