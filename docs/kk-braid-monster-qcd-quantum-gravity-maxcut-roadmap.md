# KK–C3 framed braid–YM/QCD–Monster/moonshine quantum-gravity max-cut

## Primary research focus
Keep 3=line, 6=two compatibly glued lines, 9=sheet, 18=two compatibly glued sheets and 27=3D ternary cube (or separately policy-typed 27-coordinate graph) distinct from numbers of physical states. The selected braid follows 12 time samples on the nine-position sheet with six-step mirror; the source already has a C3-labelled three-strand orbit, continuous clearance and framing information-loss counterexample.

## Current concrete owners
- KK: `KaluzaKleinGaugeShiftExact`, `check_kk_variable_radion_5d.py`, `check_kk_radion_reduced_action.py`; sibling #1238 has full 4+1 nonzero magnetic curvature fixture.
- Geometry: `C3NineSiteSixStepMirrorExact`, `C3ContinuousFramingObservationBoundaryExact`, `C3ReflectionCliffordPinBridgeExact`; full continuous Pin/O2 action and framed pants gluing still require genuine producers.
- YM/QCD: `DASHI/Physics/SFGC/NonAbelian/DepthQuotientIsoSU3.agda`, `DASHI/Physics/QFT/ColourFromNcThreeLanesReceipt.agda`, `DASHI/Physics/Closure/QCDRunningFromCarrierScaleReceipt.agda`; an SU3 finite matrix carrier does not prove measured QCD.
- GR/QFT: `DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda` already requires a common metric perturbation language and commuting GR/QFT stress pairings. Do not duplicate its same-action owner.
- Quantum gravity: `DASHI/Physics/Closure/QuantumGravityTheoryBoundary.agda` requires independent gauge quotient, dynamics, anomalies, semiclassical limits and empirical tests.
- Moonshine: actual `JInvariant369JointPhaseLevelBundleExact.agda`, modular/Fricke interfaces and Monster 3B tooling are present. Finite modular or representation identity is not a gravitational stress-energy source.

## Newly added proof interface
`DASHI/Unified/KKBraidMoonshineGaugeSameObjectCutExact.agda` carries:
1. a `SectorComparison` with explicit physicalField, representation, observation, and a *paid* observation-commuting equality;
2. a `KKYangMillsTransport` with curvature-equivariance and observable gauge invariance, and a **derived** `kkGaugeReadoutInvariant` proof;
3. an explicitly paid `MoonshinePhysicalPromotion` requiring a physical source and observation agreement, rather than a Boolean status or numerical coincidence.
It is **parametric**: it does not manufacture a physical inhabitant from a formal record.

## Pareto phases / stop conditions
**Phase A: analytic KK**. Combine variable phi with nonzero Maxwell F and curved g, prove R5 scalar decomposition in declared sign convention. Verify scalar, Einstein, Maxwell equations and consistent limits (including F²=0, phi constant). Full nonabelian compactification requires geometry beyond a 1D circle.

**Phase B: framed braid**. Specify continuous gamma_i, unit normal_i, unwrapped theta_i and two-sheet/three-sheet gluing. Construct the six-step reflection as an O(2) or Pin action with a proved commuting square; preserve integer framing separately from Z2 reversal and C3 strand permutation. Pay finite-to-continuous sampling error/isotopy certificate.

**Phase C: gauge/QCD physical same-object**. Reuse W3/M3 SU3, YM curvature/stress and flavour-vs-colour separation. Match an actual nonabelian gauge field and coupling, invariant metric, stress tensor, running coupling and physical observables. Avoid inferring colour confinement from finite S3 Weyl symmetry.

**Phase D: Monster/moonshine/QG constraints**. Supply an explicit representation or modular-form map into the *same* GR/QFT action and observable sector. Make it commute with common stress metric variation, gauge transformations and appropriate C3 symmetries. A genus-zero, Monster representation or j-function theorem alone cannot imply Einstein equations, asymptotic freedom or observed compactification.

**Phase E: independent physical discriminator**. Specify measurable predictions, normalisations, units, uncertainty and competing models before looking at new data. Candidate tests include KK radius-dependent corrections, higher-dimensional KK mode spectra, framed-braid twist/holonomy readout, and QCD beta-function/running coupling tests. Diamond sensor physics is a possible consumer but is not the organising research thread.

## Steelman / falsification
The strongest coherent theory candidate is not that '3,6,9 and Monster force all of physics'; it is a bundle-and-representation architecture in which ternary spatial charts observe topological braid classes, their continuous framed lifts carry spin/O2 connection data, nonabelian matrix algebras carry colour, and a common effective action relates QFT sources to curvature. Monster/moonshine could impose additional modular duality or spectral constraints.

This proposal fails as a physical unification if the crucial source→field→representation diagram cannot be inhabited by a common physical object, if the internal KK fibre does not reproduce observed couplings/spectrum, if gauge anomalies/positivity fail, if the numeric Monster-sector match is basis-dependent, or if the braid spin-lift is only a chosen parametrisation with no independent measurement.

## Acceptance
```sh
agda -i . -i /path/to/agda-stdlib DASHI/Unified/KKBraidMoonshineGaugeSameObjectCutExact.agda
python3 scripts/check_kk_variable_radion_5d.py
python3 scripts/check_c3_ninesite_borromean.py
python3 scripts/check_cl31_full_multivector_product.py
```
Agda has **not** been kernel-run on the current exact head. A source-written theorem and an uninhabited physical interface are not experimental confirmation.
