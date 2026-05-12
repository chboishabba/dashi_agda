# Maxwell Gauge Field Equation Scope

Status: typed G2 obligation surface; non-promoting.

Agda module:

```text
DASHI/Physics/Closure/MaxwellGaugeFieldEquationScope.agda
```

This scope records what is available for a future
`MaxwellGaugeFieldEquationTheorem` and what is still missing. It does not claim
G2.

## Already Inhabited Inputs

The scope imports the current theorem-backed canonical gauge/matter surfaces:

| Field | Source |
|---|---|
| `knownLimitsFullMatterGauge` | `canonicalKnownLimitsFullMatterGaugeTheorem` |
| `recoveredMatterField` | `canonicalGaugeMatterRecoveredMatterFieldTheorem` |
| `recoveredMatterFieldCarrier` | `RecoveredMatterFieldCarrier` from the canonical recovered matter-field theorem |

The recovered matter theorem already supplies:

- carrier/observable compatibility;
- transport/observable compatibility;
- admissible collapse to interpretable charge;
- recovered matter preservation under `evolve`, `coarse`, and `offset`.

This is still bundle-shaped recovered matter. It is not a Maxwell
field-equation theorem.

## Obligation Fields

The Maxwell-specific missing surface is grouped under
`G2MaxwellEquationComponentObligations`:

| Obligation field | Purpose |
|---|---|
| `ConnectionCarrier` | carrier for a gauge connection or discrete substitute |
| `FieldStrengthCarrier` | carrier for the field strength |
| `CurrentCarrier` | carrier for matter current extracted from recovered matter |
| `MaxwellEquationCarrier` | carrier for Maxwell equation consumers |
| `fieldStrengthFromConnection` | construct field strength from connection |
| `currentFromRecoveredMatter` | extract sourced current from recovered matter |
| `homogeneousMaxwellEquation` | homogeneous equation component |
| `inhomogeneousMaxwellEquation` | sourced equation component |
| `homogeneousMaxwellEquationLaw` | law for the homogeneous component |
| `inhomogeneousMaxwellEquationLaw` | law for the sourced component |
| `gaugeCovarianceLaw` | covariance condition for the construction |

## Curvature And Discrete Maxwell Surface

`G2MaxwellCurvatureDiscreteEquationSurface` now records the inspected
finite-gauge support:

| Field | Current support |
|---|---|
| `finiteGaugeCouplingSurface` | `shiftFiniteGaugeCoupling` |
| `gaugeCurrentConsistencySurface` | `shiftGaugeCurrentConsistency` |
| `staticGaugeConnectionCarrier` | `SFGC.GaugeField`, a static `Phase4` link assignment |
| `discreteCurrentEdgeCarrier` | `SGCC.Edge`, reusing the current edge surface |
| `recoveredMatterCurrentCarrier` | `ℤ`, the current magnitude carrier exposed by `SGCC.edgeCurrent` |
| `discreteCurvatureCarrierRequirement` | `canonicalSFGCGaugeDiscreteCurvatureCarrierObligation` from `G2DiscreteCurvatureCarrier` |

The surface is obligation-only. The exact first missing field is
`DiscreteCurvatureCarrier for SFGC.GaugeField`. After that carrier exists, the
first missing lemma is named as
`curvatureToFieldStrengthFromShiftGaugeConnection`.

`DASHI/Physics/Closure/G2DiscreteCurvatureCarrier.agda` now gives the typed
carrier shape:

```text
DiscreteCurvatureCarrier SFGC.GaugeField
```

and a conditional bridge path:

```text
curvatureToFieldStrengthFromShiftGaugeConnection
```

The bridge requires an actual `DiscreteCurvatureCarrier SFGC.GaugeField`
argument. The current finite/static gauge files still do not provide that
argument, so this is not a promotion.

The immediate upstream surface is now sharpened as a conditional
`PrimeLattice2CellLayer SFGC.GaugeField`. That layer must provide:

- `PrimeLattice0Cell`;
- `PrimeLattice1Cell`;
- `PrimeLattice2Cell`;
- a plaquette carrier and plaquette boundary into prime-lattice 1-cells;
- discrete 0-, 1-, and 2-form carriers;
- `discreteExteriorDerivative0`;
- `discreteExteriorDerivative1`;
- `zeroDiscrete2Form`;
- `exteriorDerivativeSquaredZero`, the typed `d² = 0` law;
- `connectionTo1Form` from `SFGC.GaugeField`;
- `fieldStrengthFrom2Form`.

Only after that layer is supplied can the helper
`discreteCurvatureCarrierFromPrimeLattice2CellLayer` produce the required
`DiscreteCurvatureCarrier SFGC.GaugeField`. The current repo does not define
the prime-lattice 0/1/2-cell carriers, plaquette boundary operator,
shift-gauge-to-1-form embedding, or exterior-derivative/nilpotency laws, so the
new surface records these as typed obligations rather than constructing them.

The inspected `Phase4`/finite-gauge support is not enough to define a genuine
cochain complex. A real `d0`, `d1`, and
`exteriorDerivativeSquaredZero` proof still require:

- `updateVec15-commutes` is now available for the FactorVec/prime-bump side,
  and `FactorVecInstances` proves `primeBumpCommutes`,
  `by-abelian-factorvec`, and `bumpPrimeCommutes`; this does not by itself
  supply a prime-lattice cochain geometry;
- oriented prime-lattice edge endpoint maps;
- an oriented/signed plaquette boundary, not just an unordered list of
  1-cells;
- the corrected signed square boundary
  `+bottom,+right,-top,-left`, where top and left are negated because their
  canonical edge orientations oppose the square traversal;
- a `boundaryOfBoundaryZero` incidence law for those cells;
- coefficient zero/additive inverse/addition laws for 0/1/2-cochains;
- an abelian-group normalization/solver for the selected coefficient table
  (currently `Phase4` only exposes operations and target law surfaces);
- finite incidence summation laws tying `d0` and `d1` to the oriented
  boundary operators.

The Agda side now names this exact contract as
`CorrectedSquareBoundaryCochainSurface.corrected-square-δ₁∘δ₀≡0`. It is a typed
obligation surface, not an inhabited proof for the current `SFGC.GaugeField`.

Without those base laws, defining `d1` as a constant zero map would only create
a degenerate carrier, so it is not accepted as a G2 curvature promotion.

## Vacuum Hecke Eigenvalue Reality Boundary

`DASHI/Physics/Closure/G2DiscreteCurvatureCarrier.agda` also records the
inspected vacuum/Hecke/eigenvalue route for the candidate
`vacuumHeckeEigenvaluesReal`.

The candidate cannot be constructed from the current definitions. The inspected
support provides:

- `SFGC.vacuumGaugeField`, a static `Phase4` gauge-link assignment;
- `HS.HeckeFamilyOn`, a Hecke operator/compatibility-scan shape;
- `PHEM.EigenProfile`, a coarse `Nat` counter profile over
  `earth`/`spoke`/`hub`.

That support is not enough to prove real Hecke eigenvalues on the vacuum. The
new non-promoting bridge surface names the missing fields exactly:

- `VacuumState`;
- `activeMode`;
- `heckeEigenvalue`;
- `imaginaryPart`;
- `zeroImaginaryPart`;
- `RealEigenvalue`;
- `realEigenvalueBridge`.

The conditional helper `vacuumHeckeEigenvaluesRealFromBridge` only says that if
such a bridge is supplied, zero imaginary part can be converted into the bridge's
real-eigenvalue predicate. The canonical obligation
`canonicalVacuumHeckeEigenvalueRealityObligation` records that the current repo
does not supply that bridge and therefore does not construct
`vacuumHeckeEigenvaluesReal` or a vacuum-flatness proof from it.

The inspected gauge/current modules do not currently provide a dynamic
curvature carrier, an exterior derivative, a nontrivial current-to-phase law, or
a discrete Maxwell equation consumer. Therefore no
`MaxwellGaugeFieldEquationTheorem` is inhabited.

## Sector-Restriction Route

The current proof route is now recorded separately under
`G2MaxwellSectorRestrictionObligations`.

The distinction is important:

- the homogeneous/Bianchi side is expected to be routine once field strength
  and an exterior-derivative or discrete substitute are supplied;
- the sourced Maxwell equation is not routine and requires a theorem that the
  canonical spine action restricts to the `U(1)` Yang-Mills sector, with a
  compatible matter-current extraction.

| Obligation field | Purpose |
|---|---|
| `SpineActionCarrier` | carrier for the canonical spine action or scoped substitute |
| `U1SectorCarrier` | selected electromagnetic `U(1)` sector |
| `YangMillsActionCarrier` | Yang-Mills action carrier for the selected sector |
| `KillingFormDecompositionCarrier` | decomposition evidence for the selected sector normalization |
| `ChargeNormalizationCarrier` | charge-normalization evidence for the `U(1)` sector |
| `ExteriorDerivativeCarrier` | exterior derivative or discrete substitute |
| `ExteriorDerivativeNilpotencyLaw` | law corresponding to `d^2 = 0` |
| `bianchiIdentityFromNilpotency` | routine Bianchi route once nilpotency is supplied |
| `spineActionU1SectorRestriction` | restriction from spine action to the `U(1)` sector |
| `u1SectorToYangMillsAction` | binding from `U(1)` sector to Yang-Mills action |
| `killingFormDecompositionForU1Restriction` | Killing-form decomposition candidate for the restricted sector |
| `chargeNormalizationForU1Sector` | charge normalization candidate after decomposition |
| `killingFormDecompositionDerived` | proof obligation for the decomposition route |
| `chargeNormalizationDerived` | proof obligation for normalized electromagnetic charge |
| `sectorRestrictionPreservesFieldStrength` | field-strength preservation under restriction |
| `currentExtractionCompatibleWithSectorRestriction` | compatibility of recovered matter current with the selected sector |
| `sourcedEquationFromSectorVariation` | sourced Maxwell equation produced by varying the sector action |
| `sectorVariationMatchesSourcedMaxwellEquation` | equality between the sector-variation result and the inhomogeneous Maxwell equation consumer |

This is still an obligation surface. It does not prove the sector restriction,
does not identify a concrete spine action, and does not derive
`d * F = J`.

Spine preservation is separate under
`G2MaxwellSpinePreservationObligations`:

| Obligation field | Purpose |
|---|---|
| `SpineCarrier` | canonical spine carrier for section comparison |
| `MaxwellLaneCarrier` | Maxwell lane carrier |
| `embedMaxwellInSpine` | Maxwell lane embedding into the spine |
| `recoverMaxwellFromSpine` | recovery from spine to Maxwell lane |
| `maxwellSpineSection` | section proof needed by the G6 `section-EM` gate |

## Postulate Boundary

The Agda file has three postulates, all explicitly named as obligations:

```text
obligationMaxwellEquationComponentFields
obligationMaxwellSectorRestrictionFields
obligationMaxwellSpinePreservationFields
```

They are not theorem witnesses. They keep the surface typed while making the
missing proof obligations explicit.

## Obstruction Status

The obstruction certificates are dependency certificates, not negation proofs:

```text
firstMissingObligationOnlyNoNegation
```

The named blockers are:

- `missingFieldStrengthFromConnection`;
- `missingDiscreteCurvatureCarrierForShiftGaugeField`;
- `missingCurvatureToFieldStrengthFromShiftGaugeConnection`;
- `missingDiscreteMaxwellEquationFromFieldStrengthAndCurrent`;
- `missingHomogeneousMaxwellEquation`;
- `missingInhomogeneousMaxwellEquation`;
- `missingMatterCurrentExtraction`;
- `missingSpineActionU1SectorRestriction`;
- `missingYangMillsSectorRestriction`;
- `missingKillingFormDecomposition`;
- `missingChargeNormalization`;
- `missingBianchiFromExteriorNilpotency`;
- `missingSourcedEquationFromSectorVariation`;
- `missingGaugeCovarianceLaw`;
- `missingSpinePreservationSection`.

A real obstruction would require a concrete failed Maxwell lane candidate. This
scope only records the first missing typed obligations.

## No-Promotion Boundary

`canonicalMaxwellGaugeFieldEquationScope` records:

- no `MaxwellGaugeFieldEquationTheorem` is constructed;
- no upgrade beyond bundle-shaped recovered matter fields is claimed;
- the finite/static gauge lane has no discrete curvature carrier for
  `SFGC.GaugeField`, so the curvature-to-field-strength lemma is not yet
  typeable as a closed theorem;
- the Bianchi/homogeneous route is recorded only as a nilpotency obligation;
- the sourced route is gated on `SpineActionU1SectorRestriction`, Yang-Mills
  sector binding, Killing-form decomposition, charge normalization, current
  extraction, and sector-variation equality;
- field strength, Maxwell equations, current extraction, gauge covariance, and
  spine preservation remain obligations;
- G6 `section-EM` remains unsatisfied.
