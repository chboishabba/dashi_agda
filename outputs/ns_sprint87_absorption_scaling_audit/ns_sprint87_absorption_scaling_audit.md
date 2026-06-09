# NS Sprint 87 Absorption Scaling Audit

- Contract: `ns_sprint87_absorption_scaling_audit`
- Route: `NS_SPRINT87_ABSORPTION_SCALING_CONDITIONAL_TAIL_SMALLNESS`
- Complete: `False`
- Condition: `(K*)^-1/2 * H1Tail <= epsilon * nu`
- Unconditional closure: `False`

## Scaling Rule

If K*(nu)=nu^-a and H1Tail<=C*nu^b, the left side is C*nu^(b+a/2); automatic absorption requires b+a/2>1, or b+a/2=1 plus non-circular C<=epsilon.

## Verdict

false: every passing case depends on an explicit tail-smallness law that must be supplied independently of the danger-shell absorption

## Scaling Table

| K* law | Tail law | b | b+a/2 | Automatic? | Verdict | Reason |
| --- | --- | ---: | ---: | --- | --- | --- |
| K*(nu) = nu^-1 | H1Tail <= C | 0 | 1/2 | False | FAIL_OPEN | exponent is below nu^1, so the absorption condition is not automatic |
| K*(nu) = nu^-1 | H1Tail <= epsilon * nu * sqrt(K*) | 1/2 | 1 | True | PASS_CONDITIONAL | critical exponent; automatic only with non-circular coefficient smallness |
| K*(nu) = nu^-1 | H1Tail <= C * nu | 1 | 3/2 | True | PASS_CONDITIONAL | exponent beats epsilon*nu scaling; still conditional on an independent tail law |
| K*(nu) = nu^-1 | H1Tail <= C * nu^1/2 | 1/2 | 1 | False | FAIL_OPEN | critical exponent; automatic only with non-circular coefficient smallness |
| K*(nu) = nu^-1 | H1Tail <= C * nu^7/12 | 7/12 | 13/12 | True | PASS_CONDITIONAL | exponent beats epsilon*nu scaling; still conditional on an independent tail law |
| K*(nu) = nu^-4/3 | H1Tail <= C | 0 | 2/3 | False | FAIL_OPEN | exponent is below nu^1, so the absorption condition is not automatic |
| K*(nu) = nu^-4/3 | H1Tail <= epsilon * nu * sqrt(K*) | 1/3 | 1 | True | PASS_CONDITIONAL | critical exponent; automatic only with non-circular coefficient smallness |
| K*(nu) = nu^-4/3 | H1Tail <= C * nu | 1 | 5/3 | True | PASS_CONDITIONAL | exponent beats epsilon*nu scaling; still conditional on an independent tail law |
| K*(nu) = nu^-4/3 | H1Tail <= C * nu^1/3 | 1/3 | 1 | False | FAIL_OPEN | critical exponent; automatic only with non-circular coefficient smallness |
| K*(nu) = nu^-4/3 | H1Tail <= C * nu^5/12 | 5/12 | 13/12 | True | PASS_CONDITIONAL | exponent beats epsilon*nu scaling; still conditional on an independent tail law |
| K*(nu) = nu^-2 | H1Tail <= C | 0 | 1 | False | FAIL_OPEN | critical exponent; automatic only with non-circular coefficient smallness |
| K*(nu) = nu^-2 | H1Tail <= epsilon * nu * sqrt(K*) | 0 | 1 | True | PASS_CONDITIONAL | critical exponent; automatic only with non-circular coefficient smallness |
| K*(nu) = nu^-2 | H1Tail <= C * nu | 1 | 2 | True | PASS_CONDITIONAL | exponent beats epsilon*nu scaling; still conditional on an independent tail law |
| K*(nu) = nu^-2 | H1Tail <= C * nu^0 | 0 | 1 | False | FAIL_OPEN | critical exponent; automatic only with non-circular coefficient smallness |
| K*(nu) = nu^-2 | H1Tail <= C * nu^1/12 | 1/12 | 13/12 | True | PASS_CONDITIONAL | exponent beats epsilon*nu scaling; still conditional on an independent tail law |

## Open Obligations

- prove a non-circular H1 tail-smallness law at the danger shell
- show its coefficient is <= epsilon in critical exponent cases
- exclude deriving the tail law from the same absorption inequality
