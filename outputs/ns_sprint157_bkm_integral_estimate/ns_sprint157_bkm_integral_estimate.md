# Sprint 157 BKM Integral Estimate

- Decision: `bkm_integral_estimate_promoted_for_symmetric_class_only`
- BKMIntegralEstimate: `True`
- Full Clay NS solved: `False`

| T | omega_bound | bkm_integral_bound | finite |
| ---: | ---: | ---: | ---: |
| 0.01 | 12.2220047956 | 0.122220047956 | True |
| 0.05 | 13.1697920495 | 0.658489602476 | True |
| 0.1 | 14.5040343786 | 1.45040343786 | True |
| 0.25 | 19.8092793314 | 4.95231983285 | True |
| 0.5 | 36.1798701317 | 18.0899350659 | True |

## O/R/C/S/L/P/G/F

- O: Worker 2 owns the Sprint157 BKM integral estimate emitter and output directory.
- R: Separate and integrate dOmega/(Omega log Omega) <= C*Umax dt and certify finite BKM integral rows.
- C: One stdlib Python emitter writes JSON, CSV, Markdown, and manifest artifacts.
- S: Sprint156 provides ModelValidityForWidthODE and corrected Omega ODE readiness.
- L: corrected Omega ODE -> double exponential Omega bound -> finite BKM integral on finite T.
- P: Promote BKMIntegralEstimate for the symmetric Hou-Luo class only.
- G: Do not promote full_clay_ns_solved, fullClayNSSolved, or clayNavierStokesPromoted.
- F: The continuation theorem bridge and theorem-level class closure are handled by separate Sprint157 surfaces.
