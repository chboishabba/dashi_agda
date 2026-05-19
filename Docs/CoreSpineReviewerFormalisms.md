# CoreSpine Reviewer Formalisms

Declared surface level: `bridge` with explicit gaps.

This note translates the six reviewer-facing mathematical statements into the
repo's current Agda surfaces. It separates theorem-backed statements from
interpretive or still-open claims.

## I. Ternary Group Isomorphism

Supported by:

- `DASHI.Algebra.TritTriTruthBridge`
- `Base369`

Current formal support:

- `Base369` defines the cyclic `TriTruth`, `HexTruth`, and `NonaryTruth`
  carriers and their rotation periods;
- `toTriTruth : Trit -> TriTruth`
- `fromTriTruth : TriTruth -> Trit`
- roundtrips `toFrom` and `fromTo`
- cyclic rotation `rotTrit`
- rotation equivariance with `Base369.rotateTri`
- transported operation `tritXor`
- `tritXor-identityˡ`
- `tritXor-assoc`

Important correction:

`Trit.inv` is an involutive carrier reflection and is used by the metric lane
as an isometry. Under the transported `tritXor` group law it is not a group
automorphism. The code records this explicitly through
`inv-reflection-not-tritXor-hom-at-neg`.

Do not read the 3/6/9 carrier family as mystical numerology. Also do not read
it as a theorem that Tri/Hex/Nonary phases already have theological,
actor-count, or geopolitical semantics. Those semantics require separate
carrier maps and preservation proofs.

## II. Moonshine Bridge

Supported by:

- `CRTPeriod`
- `JFixedPoint`
- `DASHI.Algebra.MoonshineBridge`
- `DASHI.Physics.CRTPeriodJFixedBridge`

Current formal support:

- `CRTPeriod.period-thm` proves periodicity of the local digit function
  `CRTPeriod.d`.
- `MoonshineBridge` proves
  `CRTPeriod.period + 1 == JFixedPoint.contract JFixedPoint.unit-obs`.
- `CRTPeriodJFixedBridge` proves the p47, p59, and p71 active-wall field
  positions.

Boundary:

The repo does not yet formalize `c1(j)` as a modular-function coefficient or
the Monster's smallest non-trivial irreducible representation. Those are now
named by `MoonshineRepresentationObligation`.

## III. Prefix Ultrametric

Supported by:

- `DASHI.Metric.AgreementUltrametric`
- `DASHI.Physics.TritCarrierBridge`

Current formal support:

- `AgreementUltrametric.ultrametricVec` proves the strong triangle inequality
  for `Vec Trit n`.
- `AgreementUltrametric.dNat-inv` proves reflection isometry.
- `TritCarrierBridge.dNat-rotTrit` proves cyclic rotation isometry.

## IV. Fixed-Point Theorem

Supported partially by:

- `Contraction`
- `DASHI.Physics.FascisticContractionInstance`
- `FascisticContractionBridge`

Current formal support:

- `StrictFascisticMap` names strict contraction over the agreement ultrametric.
- `FixedPointCertificate` names a fixed point plus uniqueness proof.
- `strictContractionFromCertificate` converts this certificate into the repo's
  `Contraction.StrictContraction` surface.
- `ContractionDescent` keeps concrete descent explicit.

Boundary:

The repo does not yet prove the fully automatic theorem "every strict
fascistic map on `Vec Trit n` converges in at most `n` steps." That remains a
real theorem target, not a current theorem.

## V. Stage Quotient

Supported by:

- `LogicTlurey`
- `DASHI.Algebra.StageQuotient`
- `Ontology.BrainComputer.LogicTlureyQuotientBridge`

Current formal support:

- `q = stageTone`
- low/mid/high representatives are explicit
- seed/counter/resonance equivariance is proved
- overflow non-equivariance is proved as `overflow-equivariance-fails`

Important correction:

Because equivariance fails, this is not a group homomorphism. Therefore
`{seed, overflow}` should not be called a group-theoretic kernel, and the
sequence should not be described as an exact sequence of groups. The supported
statement is a quotient/collapse seam with a distinguished two-element fiber.

## VI. Carrier-Physics Bridge

Supported by:

- `DASHI.Physics.TritCarrierBridge`
- `DASHI.Physics.CRTPeriodJFixedBridge`

Current formal support:

- the componentwise `Trit` / `TriTruth` bridge over `Carrier n`
- vector roundtrip laws
- rotation lift equivariance
- rotation/reflection isometry for `dNat`
- p47/p59/p71 active-wall channel positions
- `W3` as the three-prime active-wall pressure surface

Boundary:

The claimed periodicity
`W3 (x + k * CRTPeriod.period) y == W3 x y`
is not currently proved. It is named as `W3PeriodicityObligation`. This is
stronger than the existing `CRTPeriod.period-thm`, which applies to
`CRTPeriod.d`, not to `activeWallScaledAt`.

## Publication-Ready Status

The safe publication-ready chain is:

```text
TriTruth <-> Trit
  -> Carrier n = Vec Trit n
  -> agreement ultrametric
  -> strict-contraction certificate interface
  -> fixed point when a certificate/descent witness is supplied

CRTPeriod.d periodicity
  -> period + 1 == JFixedPoint.contract unit-obs
  -> p47/p59/p71 active-wall channel positions
```

The unsafe overclaim is:

```text
every stable physical configuration automatically lives in a proved
active-wall modulation window of Monster-irrep period
```

That statement still requires:

1. a formal `c1(j)` / Monster representation object,
2. a proof of `W3PeriodicityLaw`,
3. a concrete descent theorem for the selected physical `K`,
4. a domain-specific interpretation theorem connecting the fixed point to the
   intended physical, biological, chemical, or computational system.
