# NS Sprint 87 Absorption Scaling Audit

- Contract: `ns_sprint87_absorption_scaling_audit`
- Route: `NS_SPRINT87_ABSORPTION_SCALING_OPEN`
- Scalar condition: `(K*)^-1/2 * H1Tail <= epsilon * nu`
- Unconditional absorption closed: `False`
- Clay Navier-Stokes promoted: `False`

## Scaling Laws

| Gate | Law | Required tail exponent | Status |
| --- | --- | --- | --- |
| `NuInverseAbsorptionLaw` | `nu^-1` | `> 1/2` | `RECORDED_CONDITIONAL` |
| `NuFourThirdsInverseAbsorptionLaw` | `nu^-4/3` | `> 1/3` | `RECORDED_CONDITIONAL` |
| `NuSquaredInverseAbsorptionLaw` | `nu^-2` | `> 0` | `RECORDED_CONDITIONAL` |
| `RequiredScalarAbsorptionCondition` | `(K*)^-1/2 * H1Tail <= epsilon * nu` | `` | `NAMED_OPEN` |
| `UnconditionalAbsorptionClosed` | `all recorded laws` | `` | `FALSE_FAIL_CLOSED` |
| `ClayNavierStokesPromoted` | `not promoted` | `` | `FALSE_NO_PROMOTION` |

## Open Obligations

- prove DangerShellH1TailSmallness without using H1/Serrin/BKM continuation
- check coefficient smallness at the critical exponent
- exclude deriving the H1 tail law from the same absorption inequality
