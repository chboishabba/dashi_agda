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

## Cross-Row Adapter Boundary Matrix

This table is the canonical non-promoting control surface for the six-row
physics adapter boundary. The paper draft may summarize it, but this file is
the repo-side claim-control source.

| Target role | DASHI derivation engine already present | Adapter still needed | Boundary gates |
|---|---|---|---|
| Maxwell / abelian gauge | Static finite gauge surfaces, recovered matter-field inputs, conditional cochain/curvature obligations, and Maxwell equation scope. Homogeneous/Bianchi side is expected to follow after a real exterior-derivative or discrete-curvature carrier exists. | `DiscreteCurvatureCarrier SFGC.GaugeField`, curvature-to-field-strength bridge, nontrivial matter-current extraction, Hodge/codifferential surface, sourced equation consumer. | metric, calibration |
| Yang-Mills / non-abelian gauge | Gauge/matter bundle and sector-restriction targets exist; current executable support is finite/static and abelian-like. | Lie algebra bracket and Jacobi witness, representation action, trace/Killing normalization, non-abelian connection with `F = dA + A wedge A`, covariant derivative, `D F = 0`, and `D * F = J`. | metric, representation, calibration |
| QFT commutator | Selected wave-function operator commutator, pointwise antisymmetry/Jacobi, filtered bracket compatibility, and a thin QFT adapter exist. | Local observable net, Hilbert/GNS representation, vacuum/state functional, CCR/CAR representation witness, statistics grading, and interaction/source law. | representation, statistics/vacuum, calibration |
| GR curvature | Known-limits GR bridge, first-order gravity scope, finite-r Bianchi sidecars, selected non-flat metric data, and flat Levi-Civita diagnostics exist. | Non-flat Levi-Civita/Christoffel law, curvature-as-connection defect, Ricci/scalar contraction, Einstein tensor law, physical stress-energy source, Newton/`8piG` normalization. | metric, calibration |
| Measurement / uncertainty | Projection/fibre vocabulary, measurement shell, `BornLike` weight interface, selected commutator algebra, and empirical projection rejection surfaces exist. | Born probability law, outcome sigma algebra, normalization, expectation/variance, uncertainty propagation, empirical observable map, and measurement-to-projection receipt. | Born rule, metric, calibration |
| Sector splitting / Standard Model | Nominal `SU3 x SU2 x U1` gauge label, abstract gauge/matter bundle, constant gauge-recovery packages, and U(1) sector-restriction obligations exist. | Typed coset `G/H` carrier, subgroup-preservation law, SM multiplet table, hypercharge assignments, Higgs representation, symmetry-breaking/Goldstone sector, and gauge/Yukawa coupling normalization. | representation, calibration |

Boundary gates are intentionally irreducible interfaces. They are not treated
as engineering debt: `metric` covers Hodge stars, contractions, Levi-Civita
selection, and physical stress-energy dimensions; `representation` covers
matter multiplets and source-current definitions; `statistics/vacuum` covers
CCR/CAR choice and GNS/vacuum selection; `Born rule` covers probability
semantics; `calibration` covers units, coupling constants, charge
normalization, and empirical authority.

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
