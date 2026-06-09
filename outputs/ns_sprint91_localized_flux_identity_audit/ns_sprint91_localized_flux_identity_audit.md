# NS Sprint 91 Localized Flux Identity Audit

- Contract: `ns_sprint91_localized_flux_identity_audit`
- Route decision: `NS_SPRINT91_LOCALIZED_FLUX_IDENTITY_ROUTE_OPEN`
- Receipt: `DASHI/Physics/Closure/NSSprint91LocalizedFluxIdentityAndCoefficientBudget.agda`
- Anchors present: `True`
- Forbidden term count: `0`
- Localized enstrophy flux identity closed: `True`
- Dominance gate closed: `False`
- Pointwise gate closed: `False`
- Independent coefficient budget closed: `False`
- Clay Navier-Stokes promoted: `False`
- Fail closed: `False`

## Gates

| Gate | Exported | Expected | Actual | Status |
| --- | --- | --- | --- | --- |
| `LocalizedEnstrophyFluxIdentityClosed` | `True` | `True` | `True` | `TRUE_BOOKKEEPING_RECORDED` |
| `FullIdentityFixedK` | `True` | `True` | `True` | `TRUE_BOOKKEEPING_RECORDED` |
| `LocalizedFluxIdentityClosedHere` | `True` | `True` | `True` | `TRUE_BOOKKEEPING_RECORDED` |
| `ClayNavierStokesPromoted` | `True` | `False` | `False` | `FALSE_NO_PROMOTION` |
| `DominanceGateClosed` | `True` | `False` | `False` | `FALSE_ANALYTIC_GATE_OPEN` |
| `PointwiseTailFromLocalDissipationClosed` | `True` | `False` | `False` | `FALSE_ANALYTIC_GATE_OPEN` |
| `PointwiseH1TailWithIndependentEpsilonCoefficientClosed` | `False` | `not_exported_or_false` | `False` | `NOT_EXPORTED` |
| `IndependentCoefficientBudgetClosed` | `True` | `False` | `False` | `FALSE_ANALYTIC_GATE_OPEN` |
| `IndependentEpsilonCoefficientClosed` | `False` | `not_exported_or_false` | `False` | `NOT_EXPORTED` |
| `LocalizedFluxIdentityAliasClosed` | `False` | `not_exported_or_false` | `False` | `NOT_EXPORTED` |
| `NoForbiddenStubOrHoleLanguage` | `True` | `0` | `0` | `PASS` |

## Source Surfaces

- `S1` `DASHI/Physics/Closure/NSSprint91LocalizedFluxIdentityAndCoefficientBudget.agda`: `PASS`, missing anchors `none`.

## Forbidden Terms

- none

## Open Obligations

- materialize the Sprint 91 receipt at the audited path if missing
- export fixed-k/localized flux identity bookkeeping as true when the receipt claims it
- keep dominance, pointwise, and independent coefficient gates false until proved
- keep Clay Navier-Stokes promotion false
