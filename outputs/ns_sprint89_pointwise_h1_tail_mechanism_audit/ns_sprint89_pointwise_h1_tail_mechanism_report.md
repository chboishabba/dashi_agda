# NS Sprint 89 Pointwise H1-Tail Mechanism Audit

- Contract: `ns_sprint89_pointwise_h1_tail_mechanism_audit`
- Route decision: `fail_closed`
- Receipt: `DASHI/Physics/Closure/NSSprint89PointwiseH1TailCandidateMechanismReceipt.agda`
- Anchors present: `True`
- Forbidden term count: `0`
- Pointwise H1 tail with independent epsilon closed: `False`
- Clay Navier-Stokes promoted: `False`
- Fail closed: `True`

## Gates

| Gate | Expected | Actual | Status |
| --- | --- | --- | --- |
| `LocalEnstrophyDangerShellDissipationMechanismClassified` | `True` | `True` | `CLOSED_RECORDED` |
| `TimeIntegratedToPointwiseConversionClassified` | `True` | `True` | `CLOSED_RECORDED` |
| `CoefficientIndependenceClassified` | `True` | `True` | `CLOSED_RECORDED` |
| `NoSelfUseOfAbsorptionClassified` | `True` | `True` | `CLOSED_RECORDED` |
| `LocalEnstrophyDangerShellDissipationClosed` | `False` | `False` | `OPEN_FAIL_CLOSED` |
| `TimeIntegratedToPointwiseConversionClosed` | `False` | `False` | `OPEN_FAIL_CLOSED` |
| `IndependentEpsilonCoefficientClosed` | `False` | `False` | `OPEN_FAIL_CLOSED` |
| `NoSelfUseOfAbsorptionClosed` | `True` | `True` | `CLOSED_RECORDED` |
| `PointwiseH1TailWithIndependentEpsilonCoefficientClosed` | `False` | `False` | `OPEN_FAIL_CLOSED` |
| `ClayNavierStokesPromoted` | `False` | `False` | `FALSE_NO_PROMOTION` |
| `NoPostulateTodoStubFutureProofLanguage` | `0` | `0` | `PASS` |

## Source Surfaces

- `S1` `DASHI/Physics/Closure/NSSprint89PointwiseH1TailCandidateMechanismReceipt.agda`: `PASS`, missing anchors `none`.
- `S2` `DASHI/Physics/Closure/NSSprint88DangerShellH1TailSmallnessDecisionReceipt.agda`: `PASS`, missing anchors `none`.
- `S3` `scripts/ns_sprint88_tail_source_classifier.py`: `PASS`, missing anchors `none`.

## Forbidden Terms

- none

## Open Obligations

- materialize the Sprint 89 NS pointwise H1-tail candidate mechanism receipt if missing
- record the Sprint 88 H1-tail decision boundary
- derive local enstrophy danger-shell dissipation non-circularly
- derive time-integrated to pointwise localization non-circularly
- derive an independent epsilon<1 coefficient
- keep pointwiseH1TailWithIndependentEpsilonCoefficientClosed false until both inputs close
- keep clayNavierStokesPromoted false
