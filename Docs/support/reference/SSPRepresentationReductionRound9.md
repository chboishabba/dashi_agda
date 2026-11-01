# SSP representation-reduction Round 9

## Status

This tranche corrects the logical direction of the SSP/Ogg programme.

The Ogg list is **not** used to choose a representation, subgroup, nonary
address, or branching pattern.  The representation side is computed first on
an unfiltered candidate domain; the known Ogg/supersingular classification is
an independent downstream comparison column.

The implemented architecture is

```text
continuous SU(2)/SO(3) irrep
  -> candidate-indexed finite restriction
  -> branching spectrum
  -> target-valid fixed-space probes
  -> optional derived 3/6/9 coordinate

same candidate level n
  -> arithmetic / Hecke / modular column
  -> Ramanujan-tau fingerprint
  -> Fricke / supersingular authority boundary

representation side x arithmetic side
  -> future intertwiner / defect comparison
  -> compare derived exceptional locus with external Ogg locus
```

The classical intertwiner and exceptional-locus equality are still open.  No
module in this tranche claims otherwise.

## Primary source calibration

The representation-theoretic modules cite:

- William Fulton and Joe Harris, *Representation Theory: A First Course*,
  Graduate Texts in Mathematics 129, Springer,
  DOI `10.1007/978-1-4612-0979-9`;
- Jean-Pierre Serre, *Linear Representations of Finite Groups*, Graduate Texts
  in Mathematics 42, Springer, 1977,
  DOI `10.1007/978-1-4684-9458-7`.

The modular/arithmetic lane additionally cites:

- Jean-Pierre Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7,
  Springer, 1973, DOI `10.1007/978-1-4684-9884-4`;
- Toshitsune Miyake, *Modular Forms*, Springer Monographs in Mathematics,
  Springer, 2006, DOI `10.1007/3-540-29593-3`;
- Nicholas M. Katz and Barry Mazur, *Arithmetic Moduli of Elliptic Curves*,
  Princeton University Press, 1985, DOI `10.1515/9781400881710`;
- Andrew P. Ogg, *Automorphismes de courbes modulaires*, Seminaire
  Delange-Pisot-Poitou 16 (1974-1975), expose 7, MR 417184; no DOI asserted;
- John F. R. Duncan and Ken Ono, *The Jack Daniels Problem*, Journal of Number
  Theory 161 (2016), 230-239, DOI `10.1016/j.jnt.2015.06.001`.

Citations calibrate definitions and standard representation/modular facts.
They do not import an SSP-reduction theorem that those sources do not state.

## 1. Unbiased continuous carrier

`DASHI.Foundations.SU2SO3IrrepDimensionExact` uses integral highest weights.

For SU(2), highest weight `n` has dimension

```text
n + 1.
```

The SO(3) descent lane used here is the even-highest-weight lane

```text
n = 2*j,
```

with dimension

```text
2*j + 1.
```

The scan is `j = 0..35`, so the spatial dimensions are every odd value from 1
to 71.  Level 2 is kept separately as the SU(2) spinor doublet.  This makes the
special p=2 boundary typed rather than silently pretending that `j=1/2` is an
integer SO(3) angular momentum.

`DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact` packages the
complete upstream domain:

```text
spinor level 2
+
spatial levels 1,3,5,...,71.
```

In particular 9, 15, 21, 25, 27, 33, 35, 43, 53 and 67 are first-class
controls.  The domain is not constructed from `MonsterOntos.SSP`.

## 2. Generic restriction carrier

`DASHI.Foundations.FiniteRepresentationRestrictionCore` implements

```text
ContinuousIrrep
  -> FiniteIrrepFamily
  -> BranchingSpectrum
  -> FixedSpaceSpectrum
  -> FiniteRestriction.
```

A branching spectrum must carry exact dimension conservation.

`DASHI.Foundations.CandidateIndexedFiniteRestrictionFamilyExact` strengthens
this to a dependent family

```text
j -> H_j -> Res_(H_j)(V_j) -> Sigma_(H_j)(j).
```

The assembled `FiniteRestriction` is definitionally built from the same target
family, branching proof and fixed-space spectrum.  A caller cannot declare one
branching spectrum and attach an unrelated restriction receipt.

The exact Ogg-selecting candidate-dependent family is intentionally not
constructed yet.

## 3. Four exact finite rotation controls

The current concrete control lenses are:

```text
rotational D4       order  8
rotational A4       order 12
rotational S4       order 24
rotational A5       order 60
```

The corresponding scans live in:

- `D4SO3RestrictionJ0To35Exact`;
- `TetrahedralSO3RestrictionJ0To35Exact`;
- `OctahedralSO3RestrictionJ0To35Exact`;
- `IcosahedralSO3RestrictionJ0To35Exact`.

All `j=0..35` branching tables have exact dimension conservation.  Companion
modules exhaustively verify the restricted class character on every row:

```text
36 x 5 D4 cases
36 x 4 A4 cases
36 x 5 S4 cases
36 x 5 A5 cases.
```

The A4 order-three classes use exact Eisenstein `Z[omega]` bookkeeping.  The A5
order-five classes use exact `Z[phi]` bookkeeping.  No floating character
comparison is required.

`PolyhedralFiniteRestrictionInstancesExact` then instantiates the generic core.
Fixed-space probes are admitted only for cyclic rotation orders actually
present in the target group:

```text
D4 : C2, C4
A4 : C2, C3
S4 : C2, C3, C4
A5 : C2, C3, C5.
```

## 4. Five irreps of nine

The existing repository already had a D4 action on a 3x3 nine-cell carrier.
Its permutation representation decomposes as

```text
3 A1 + B1 + B2 + 2 E,
```

so `A2` is absent.

The new continuous-restriction calculation asks a different question: restrict
the actual nine-dimensional SO(3) `j=4` irrep to rotational D4.  The result is

```text
V_4 | D4 = 2 A1 + A2 + B1 + B2 + 2 E
         = 1 + Reg_D4.
```

All five D4 irrep species occur.

This gives a precise version of the remembered "five irreps of nine" idea while
also proving that it is **not** the same representation as the old 3x3 cell
permutation action.  Equal dimension plus equal acting group does not identify
representations.

## 5. The regular-representation shift theorem on the control scans

The restriction tables expose a common mechanism.

For these four rotation groups the nonidentity SO(3) class characters repeat
with periods

```text
D4 :  4
A4 :  6
S4 : 12
A5 : 30.
```

In each case

```text
2 * period = group order.
```

Across one period the continuous dimension rises by exactly the group order,
while every nonidentity class character repeats.  The character difference is
therefore the regular character.  The finite scans witness

```text
Res_D4 V_(j+4)  = Res_D4 V_j + Reg_D4
Res_A4 V_(j+6)  = Res_A4 V_j + Reg_A4
Res_S4 V_(j+12) = Res_S4 V_j + Reg_S4
Res_A5 V_(j+30) = Res_A5 V_j + Reg_A5
```

whenever both angular momenta lie in the `0..35` scan.

This immediately proves that a selector depending only on one fixed group's
branching spectrum **modulo regular summands** is too weak.

Concrete Ogg/non-Ogg collisions are formalized:

```text
A4 : dimension  3 (Ogg)  ~ dimension 15 (non-Ogg)
S4 : dimension  5 (Ogg)  ~ dimension 53 (non-Ogg)
A5 : dimension  7 (Ogg)  ~ dimension 67 (non-Ogg)
```

where `~` means equality after forgetting the appropriate number of regular
summands.

This does not refute a candidate-dependent reduction family or a Hecke-coupled
selector.  It rules out a materially weaker hypothesis.

## 6. Fixed-space probes are real, but small fixed-space summaries are too lossy

For an axial cyclic subgroup `C_n`, the SO(3) weight basis gives

```text
dim(V_j ^ C_n) = 2 * floor(j/n) + 1.
```

`PolyhedralFixedSpaceSpectrumJ0To35Exact` implements the C2/C3/C4/C5 versions
by division-free recurrences and verifies the C2/C3 character-average identities
through the complete scan.

It also locks an important notation boundary:

```text
C3 = cyclic order-three rotation subgroup
S3 = six-element ternary coordinate permutation group.
```

They are not the same group.

Even combining four whole-group invariant dimensions is insufficient.  The
signature

```text
(dim V_j^D4, dim V_j^A4, dim V_j^S4, dim V_j^A5)
```

collides at

```text
j=14, dimension 29, Ogg     -> (4,2,1,0)
j=17, dimension 35, non-Ogg -> (4,2,1,0).
```

Thus the final representation defect must retain more than these four scalar
fixed-space dimensions.

## 7. 3/6/9 is now downstream

`PolyhedralFixedSpaceDerivedNonaryExact` derives a deliberately small Q9
coordinate from actual fixed-space data:

```text
j
 -> (dim V_j^C2 mod 3, dim V_j^C3 mod 3)
 -> PhaseQuotient9
 -> NonaryTruth.
```

This reverses the old logical direction.  `NonaryTruth` is a coordinate on a
reduced signature, not evidence from which the symmetry is inferred.

The projection is intentionally lossy.  It has period 18 on the current scan,
and gives the same nonary address to

```text
j=3,  dimension 7,  Ogg
j=21, dimension 43, non-Ogg.
```

Therefore derived nonary data remains a diagnostic coordinate rather than the
SSP selector.

The older `7+7+1` Ogg carrier is treated the same way.  It remains a valid
finite carrier equivalence and comparison surface, but
`TernarySevenOggSSPComparisonExact` now states explicitly that it is **not** the
upstream Ogg selector.

## 8. Independent arithmetic fingerprint

`RamanujanTauCandidateFingerprintJ0To35Exact` supplies the same unbiased
candidate domain with exact Ramanujan-tau values:

```text
level n -> tau(n)
```

for level 2 and all odd levels through 71.

It reuses the existing exact level-2/3 Hecke checksum and the already-checked
values at 9 and 27.  The accompanying stdlib-only audit script independently
rebuilds

```text
Delta(q) = q * product_(m>=1) (1-q^m)^24
```

through `q^71` and compares every candidate coefficient.

Tau is an arithmetic spectral fingerprint here, not a claimed Ogg classifier.

## 9. External Ogg authority is downstream only

`DASHI.Physics.Moonshine.SupersingularPrimeLaneBridge` already separates the
external Ogg theorem surface from internal finite machinery.

`CandidateLevelExternalOggPredicateExact` transports that classification to the
unfiltered candidate-level domain only for post-computation comparison.  The
representation restriction modules do not import this predicate.

This prevents the circular construction

```text
known Ogg level -> choose special reduction -> rediscover Ogg.
```

The intended direction is

```text
candidate level
 -> derive reduction defect independently
 -> derive arithmetic/modular defect independently
 -> compare zero loci
 -> compare resulting exceptional locus with external Ogg classification.
```

## 10. Equality is the wrong bridge; intertwining is the target

The older physical SSP/Hecke receipt leaves a carrier-equality bridge open.
Round 9 replaces that as the conceptual target with

```text
Phi o R_n = T_n o Phi.
```

`CandidateLevelRepresentationHeckeSquareExact` and
`SSPRepresentationHeckeIntertwinerBoundaryExact` make this distinction typed.
The representation carrier and arithmetic carrier may remain different while
their candidate-indexed operators intertwine.

No classical intertwiner is claimed yet.

Likewise, `ModularCurveJFrickeInterfaceExact` still does not manufacture a
Fricke genus-zero proof internally.  The external modular/Ogg classification
remains an independent authority boundary until that analytic/arithmetic lane
is built more deeply.

## 11. Current falsifiable frontier

The strongest open statement is now approximately:

```text
find a candidate-dependent reduction family H_n and representation defect D_rep
find an independent arithmetic/modular defect D_mod
construct or derive their comparison
prove on the unfiltered candidate domain:

    D_rep(n) closes <-> D_mod(n) closes

then compare that derived zero set with the external Ogg locus.
```

Equivalently, at operator level the target is an actual map `Phi` satisfying

```text
Phi (R_n x) = T_n (Phi x).
```

The fixed D4/A4/S4/A5 calculations are controls for this search.  They are not
promoted into the final selector because the exact collisions above prove that
several natural quotients lose too much information.

## 12. Validation boundary

The focused aggregate is

```text
DASHI.EverythingSSPRepresentationReductionRound9
```

with regression surface

```text
DASHI.Moonshine.OggRepresentationReductionRegression
```

and the independent finite audit

```text
python3 scripts/check_ogg_representation_reduction.py
```

No GitHub Actions/CI or CodeRabbit is required for this tranche.  A local Agda
2.9 kernel run is still required before calling these new modules typechecked.
The source tree intentionally keeps the open analytic/intertwiner obligations
visible rather than replacing them with postulates or receipt fields that
assume the desired Ogg theorem.
