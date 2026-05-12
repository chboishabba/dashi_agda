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

The Agda file has two postulates, both explicitly named as obligations:

```text
obligationMaxwellEquationComponentFields
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
- `missingHomogeneousMaxwellEquation`;
- `missingInhomogeneousMaxwellEquation`;
- `missingMatterCurrentExtraction`;
- `missingGaugeCovarianceLaw`;
- `missingSpinePreservationSection`.

A real obstruction would require a concrete failed Maxwell lane candidate. This
scope only records the first missing typed obligations.

## No-Promotion Boundary

`canonicalMaxwellGaugeFieldEquationScope` records:

- no `MaxwellGaugeFieldEquationTheorem` is constructed;
- no upgrade beyond bundle-shaped recovered matter fields is claimed;
- field strength, Maxwell equations, current extraction, gauge covariance, and
  spine preservation remain obligations;
- G6 `section-EM` remains unsatisfied.
