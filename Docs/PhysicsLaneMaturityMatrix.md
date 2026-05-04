# Physics Lane Maturity Matrix

This matrix records the current maturity of four physics-facing DASHI lanes:
Maxwell/gauge, Schrödinger, GR curvature, and empirical prediction. It is a
claim-control surface, not a promotion receipt.

The purpose is to replace the weaker question "are these present?" with the
more precise question "what closure obligations remain?"

## Maturity Scale

| Stage | Meaning |
|---|---|
| `present` | The repo/program contains named modules, diagrams, or coordination lanes for the topic. |
| `bridged` | The topic is connected to the canonical spine or bridge vocabulary by typed or documented carrier/consumer surfaces. |
| `packaged` | The topic is assembled into a consumer, request pack, diagnostic, or bounded interface with explicit gates. |
| `theorem-complete` | The repo contains the claimed final derivation theorem for the lane, with no remaining internal closure blocker for that claim. |
| `empirically-validated` | The lane has accepted external authority, calibration, and empirical adequacy receipts. |

## Current Matrix

| Lane | Owner / workstream | Present | Bridged | Packaged | Theorem-complete | Empirically-validated | Current reading |
|---|---|---:|---:|---:|---:|---:|---|
| Maxwell / gauge-field regime | `W-MAX` | yes | yes | partial | no | no | Gauge/matter and static-gauge surfaces exist; full field-equation recovery and empirical validation remain open. |
| Schrödinger evolution | `W-SCH` | yes | yes | yes | no | no | Schrödinger-facing consumers/packages exist as bounded dynamics surfaces; no end-to-end textbook Schrödinger derivation is claimed. |
| GR curvature / GR-QFT consumer | `W5` / `W-GR` | yes | yes | yes | no | no | Known-limits GR/QFT bridge and consumer surfaces exist; richer downstream GR/QFT closure and empirical validation remain blocked. |
| Predictions / empirical adequacy | `W-EMP` | yes | yes | yes | no | no | Empirical/calibration, provider-intake, HEPData residual, and authority-gate lanes exist; accepted empirical adequacy remains externally blocked. |

## Closure Obligations

| Lane | Next closure obligation |
|---|---|
| Maxwell / gauge-field regime | Promote from bounded/static or interpretable gauge surfaces to a finished field-equation theorem, or record a precise obstruction. |
| Schrödinger evolution | Replace bounded Euler/proxy packaging with an end-to-end derivation theorem, or keep the current consumer as explicitly theorem-thin. |
| GR curvature / GR-QFT consumer | Supply the richer downstream GR/QFT consumer receipts named by W5, including curvature/stress-energy/interaction closure and empirical validation. |
| Predictions / empirical adequacy | Supply accepted external authority, calibration/covariance, projection, comparison-law, and empirical adequacy receipts, starting with the HEPData residual observable-class receipt chain. |

## Publishable Claim Boundary

Defensible wording:

> DASHI already contains explicit Maxwell/gauge, Schrödinger, GR-curvature, and
> empirical-prediction lanes in its formal program. The remaining gap is closure:
> converting these bridged or packaged lanes into finished derivation theorems
> and accepted empirical adequacy results.

Non-defensible wording:

> DASHI has fully derived Maxwell, Schrödinger, GR, and empirical predictions.

That stronger claim remains blocked by the missing theorem-complete and
empirically-validated columns above.
