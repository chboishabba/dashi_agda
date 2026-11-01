# NS Sprint 88 Tail Source Classifier

- Contract: `ns_sprint88_tail_source_classifier`
- Route: `NS_SPRINT88_TAIL_SOURCE_CLASSIFIER_OPEN`
- Sufficient for pointwise absorption: `False`
- Rule: sufficient iff one source supplies pointwise H1 tail and an independent epsilon coefficient

## Source Classification

| Source | Pointwise H1 tail | Independent epsilon | Sufficient | Classification |
| --- | --- | --- | --- | --- |
| `KStarL2Tail` | `False` | `False` | `False` | `INSUFFICIENT_L2_NOT_H1` |
| `LerayEnergyPointwise` | `False` | `False` | `False` | `INSUFFICIENT_ENERGY_LEVEL_ONLY` |
| `TimeIntegratedDissipation` | `False` | `False` | `False` | `INSUFFICIENT_TIME_INTEGRATED` |
| `DangerShellLocalMechanism` | `False` | `False` | `False` | `TARGET_NOT_SOURCE` |
| `CriticalCoefficientSmallness` | `False` | `False` | `False` | `INSUFFICIENT_COEFFICIENT_ONLY` |

## Gates

| Gate | Status | Next input |
| --- | --- | --- |
| `KStarL2Tail` | `FAIL_CLOSED_MISSING_TAIL_AND_EPSILON` | pointwise H1 tail upgrade independent of absorption |
| `LerayEnergyPointwise` | `FAIL_CLOSED_MISSING_TAIL_AND_EPSILON` | non-circular enstrophy/H1 tail localization theorem |
| `TimeIntegratedDissipation` | `FAIL_CLOSED_MISSING_TAIL_AND_EPSILON` | pointwise-in-time extraction with independent small coefficient |
| `DangerShellLocalMechanism` | `FAIL_CLOSED_MISSING_TAIL_AND_EPSILON` | prove local mechanism without reusing absorption conclusion |
| `CriticalCoefficientSmallness` | `FAIL_CLOSED_MISSING_TAIL_AND_EPSILON` | independent coefficient bound plus pointwise H1 tail source |
| `AnyCandidateSourceSufficient` | `FALSE_NO_CANDIDATE_SUPPLIES_BOTH_REQUIREMENTS` | single non-circular source supplying pointwise H1 tail and independent epsilon coefficient |

## Open Obligations

- derive pointwise H1 tail at the danger shell from non-circular NS inputs
- derive an independent epsilon<1 absorption coefficient
- verify the tail and coefficient are not obtained from the target absorption inequality
