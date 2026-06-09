# Unified Routes And Lanes Plan

Declared surface level: `architecture` and `roadmap`.

This plan generalizes the stellar-composition simulator pattern across the
repo.  It does not promote any lane.  It defines how every route should move
from existing carrier language to executable receipts, then to blocked or
promoted Agda guards.

## Core Pattern

Every route should be readable as the same six-stage pipeline:

```text
lane object
  -> canonical parent / carrier grammar
  -> bounded observable or theorem target
  -> executable or formal receipt
  -> Agda guard with explicit promotion flags
  -> adapter path toward theorem, authority, or empirical validation
```

The canonical theorem spine remains owned by `Docs/ClosurePipeline.md`.
Simulator execution remains owned by `Docs/SimulatorRoadmap.md`.  Lane maturity
and adapter boundaries remain owned by `Docs/PhysicsLaneMaturityMatrix.md`.
This file is the joining plan: it tells future work how to make the lanes
commute without strengthening claims by analogy.

## Lane Families

| Family | Current role | Next bounded slice | Promotion blockers |
|---|---|---|---|
| Canonical closure spine | Theorem route from projection defect through quadratic, signature, Clifford, and closure. | Keep one canonical import/citation path and expose receipt-facing summaries for downstream lanes. | Parallel emergence routes, stale imports, heavy aggregate validation. |
| Cross-scale simulator | Unified facade and executable bounded diagnostics. | Repeat the stellar pattern for atom, molecule, chemistry, cell, organism, and stellar observables. | Missing real physical model authorities and empirical validation receipts. |
| Maxwell / gauge | Bridged and partially packaged field-equation surfaces. | Bounded gauge-field diagnostic: carrier table -> finite curvature/source proxy -> receipt. | Metric/Hodge authority, matter-current extraction, calibration. |
| Yang-Mills / non-abelian | Clay-facing KP/Balaban and field-equation receipt stack. | Bounded finite-gauge worker receipts that separate actual polymer activity from proxy rho. | Actual Wilson polymer activity, Balaban RG transfer, continuum gap, external acceptance. |
| Schrodinger / dynamics | Bounded dynamics consumers and Hamiltonian-facing scopes. | Deterministic finite-state Hamiltonian proxy receipt with explicit no-derivation guard. | Hilbert representation, self-adjoint Hamiltonian, Born rule, calibration. |
| GR / curvature | Known-limits GR bridge plus weak-field external baseline. | Extend weak-field baseline receipts into a curvature/stress-energy blocker index. | Non-flat Levi-Civita law, Ricci/Einstein contraction, physical stress-energy, `G` normalization. |
| Empirical prediction | Provider intake, HEPData residual, comparison-law, and authority gates. | Standard empirical receipt harness: source checksum -> projection -> comparison law -> authority decision. | Accepted provider authority, covariance, transform law, calibration, holdout validation. |
| Biology / DNA / brain | Typed observation and chemistry/channel carriers. | Domain-specific bounded observation receipts that keep subject, source, and clinical authority separate. | Wet-lab/clinical authority, measurement provenance, biological causation, intervention validation. |
| PNF / ITIR / language | Runtime/parser/residual carrier surfaces. | Runtime receipt intake: source artifact -> parser projection -> residual table -> Agda non-promotion guard. | Runtime provenance, external execution receipts, semantic adequacy validation. |
| Arithmetic / moonshine / Gate 3 | Hecke, j, CM/atom grammar, finite frame, and barrier targets. | Bounded finite-frame diagnostics with CM/Hecke partition fences and no continuum promotion. | Density, Mosco recovery, no spectral pollution, mass-shell bridge. |

## Full Unified Surface

The repo-facing completion map joins every lane through one receipt-gated
surface:

```text
carrier
  -> observable/theorem target
  -> receipt
  -> guard
  -> adapter
  -> validation
```

This is a completion and blocker map, not a new theorem claim. The canonical
closure spine remains the theorem owner for the existing projection-defect to
physics-closure route. Chemistry, biology, physics, Clay-facing lanes,
arithmetic/Gate 3, empirical prediction, and runtime/language lanes may cite
the same surface only to make their receipt state comparable.

The current completion map is:

| Surface | Carrier | Observable / theorem target | Receipt and guard state | Adapter and validation boundary |
|---|---|---|---|---|
| Canonical closure spine | Projection defect, quadratic form, signature, Clifford, and closure modules. | Canonical Stage C closure route. | Owned by `Docs/ClosurePipeline.md`; downstream lanes may summarize but not replace it. | Adapter work must cite canonical modules before alternative or experimental routes. |
| Chemistry / DNA / supervoxel | Atomic chemistry, DNA channel, checksum, supervoxel, and chemistry-sheet carriers. | Local chemistry laws, bounded packet/channel transport, and chemistry-facing handoff. | Locally strongest definitional and theorem-thin surface; non-promoting physical-semantics guards remain explicit. | Wet-lab chemistry, spectra, bonding, physical-chemistry calibration, and empirical validation remain external. |
| Biology / brain | Brain/fMRI, brain-body quotient, BrainDNA codec, representation, and chemistry-channel carriers. | Bounded observation, crossover, representation, and semantic-depth targets. | Structured and bridged through local owners, with subject/source/clinical authority kept separate. | Biological causation, intervention, clinical validity, and measurement provenance remain uninhabited validation gates. |
| Physics adapters | Maxwell/gauge, Schrodinger, GR, QFT/measurement, Standard Model sector, and cross-scale matter carriers. | Field equations, Hamiltonian dynamics, curvature/stress-energy, measurement semantics, and sector restrictions. | Strong theorem architecture and bounded packages exist; known-physics translation is adapter-blocked. | Metric/Hodge, representation, Born/statistics, source-current, constants, units, calibration, and accepted empirical authority remain required. |
| Navier-Stokes | Fluid/interface, theta, pressure, danger-shell, and regularity-tower carriers. | Clay-facing incompressible NS regularity route. | Priority analytic lane with fail-closed promotion guards. | Any success must translate into standard PDE language: weak/strong solution class, pressure reconstruction, energy inequality, regularity criterion, and physical fluid interpretation. |
| Yang-Mills | Non-abelian gauge, Wilson polymer, KP/Balaban, OS/Wightman, transfer, and mass-gap carriers. | Clay-facing continuum Yang-Mills existence and positive mass gap. | Priority analytic lane with finite diagnostics and many conditional receipts; Clay promotion remains false. | Any success must translate into QFT/gauge language: connection/curvature, action, Wilson observables, OS positivity, Wightman reconstruction, continuum limit, physical mass gap, and empirical cross-scale matter context. |
| Arithmetic / moonshine / Gate 3 | Hecke, CM, modular-j, Monster/moonshine, finite frame, PAWOTG, Mosco, and no-pollution carriers. | Finite-frame separation, density, continuum transfer, mass-shell, and barrier-route targets. | Bounded diagnostics and conditional reductions exist with explicit CM/Hecke partition fences. | Continuum transfer, Mosco recovery, no spectral pollution, mass-shell identification, and physics-facing translation remain open. |
| Empirical prediction | Provider-intake, HEPData residual, comparison-law, covariance, and authority carriers. | Source checksum, projection, residual, comparison, and authority decision. | Packaged as a fail-closed provider and residual-receipt lane. | Accepted source authority, transform law, unit/covariance calibration, holdout validation, and empirical adequacy remain required. |
| PNF / ITIR / language | Runtime parser, PredicatePNF, residual lattice, source artifact, and Hecke-fibre carriers. | Parser projection, residual table, replay, and semantic adequacy targets. | Runtime and interop receipt surfaces exist; missing-receipt diagnostics prevent promotion. | External execution provenance, parser/reducer version, source checksum, replayability, and semantic validation remain required. |

Chemistry is the strongest local-completion template because its current
completion is mostly definitional and local. Physics is the broadest
adapter-gated family because it must translate local carrier results into
standard equations, representation theory, measurement semantics, constants,
and empirical authority. NS and YM have the highest analytic proof priority,
but their receipts must still commute back into known PDE/QFT language before
any Clay-facing or physical claim can be promoted.

## Current Clay P0 Hardening Map

The current Navier-Stokes route is no longer the historical single-angle
zero-mode route.  The output-only finite calculation
`CascadeClosedZeroModeOutputWidth` is retained as a fail-closed historical
boundary, but the exact-strain harnesses showed it is too permissive.  The
live finite calculation is now `NSCascadeTransversalityCollapse` /
`PropagatedPolarizationCascadeClosedOutputWidth`, supported by
`NSTrueLerayTriadicDefectSymbol`,
`NSTrueLerayTriadicZeroModeClassificationBoundary`,
`NSCascadeClosedZeroModeOutputWidthBoundary`, and
`NSTriadicAngularDefectSheafLeakageBoundary`, with
`NSSignAntisymmetryExactIdentityBoundary` providing the exact true-triad
identity `(a . omega_c) + (b . omega_c) = 0` as the algebraic seed.  Its live
analytic calculation is `TriadicCompensatedLeakageIdentity`, supported by
`NSAbelTriadicDefectMeasureConstructionBoundary`,
`NSTriadicCompensatedLeakageIdentityBoundary`, and
`NSTriadicLeakageSquareFunctionCoercivityBoundary`.  Ordinary CZ/LP and
Coifman-Meyer estimates remain decomposition and boundedness tools only; the
strict residual depletion must come from a signed leakage square-function
identity for the true non-averaged Leray bilinear symbol.
The 2026-06-08 exact finite-symbol harness round is now recorded by
`NSExactStrainEigenbundleHarnessBoundary`: exact Biot-Savart/Leray/strain
bookkeeping passes locally, but the current Family-I/II zero-mode residual is
too permissive in that model.  Under the capped local probes, exact-strain
reports `800/800` single-depth and depth-2 output-width hits, `1000/1000`
depth-2 closure hits, and an A/B comparison of proxy `1` zero hit versus exact
`1200` zero hits.  The finite route must therefore strengthen the
cascade-closed propagated-polarization/coherence condition, or replace the
present output-width theorem target, before the analytic transfer can be
treated as the next NS closing step.
The angular S2 Biot-Savart/curl diagnostic is recorded by
`NSS2BiotSavartEigenbundleCascadeDiagnosticBoundary` and implemented in
`scripts/ns_s2_biot_savart_eigenbundle.py` plus
`scripts/ns_s2_cascade_width_harness.py`.  It uses the local `m11/m12`
angular eigenline and corrected lambda diagnostic instead of the output-built
tautology.  The capped run separates two notions that must not be conflated:
random first-valid depth-2 survival at threshold `0.01` is `932 / 2966`, while
best-of-120 existential survival is `2966 / 2966`.  This keeps
`CascadeDepth2DegreeComputation` / transversality as the live finite proof
target; finite sampling is not a proof of cascade-closed exclusion.
The corrected finite NS statistics now move the live route away from
coherent-triad domination and toward a kappa-bias PDE gate.  The governing
five-result finite/statistical normal-form receipts are
`NSSignAntisymmetryExactIdentityBoundary`,
`NSCascadeKappaArcsineLawBoundary`,
`NSCoherentStretchingExactFormulaBoundary`,
`NSFiniteCascadeStretchingNeutralityBoundary`, and
`NSBiotSavartStrainMeanSquareExactFormulaBoundary`.  They record true-triad
sign antisymmetry, the arcsine baseline, the exact stretching law
`omega . S omega = lambda(c)(2 kappa^2 - 1)`, conditional finite neutrality,
and `<lambda^2>_{S2} = 11/60`.  The next NS analytic target is therefore
`NSTypeIBlowupKappaBiasBound`: a Type-I/self-similar blowup profile must not
create persistent positive `lambda(c)(kappa^2 - 1/2)` bias in its Abel
triadic defect measure.  The finite harness
`scripts/ns_kappa_bias_variational_harness.py` is a proxy falsification tool
only; positive top-tail finite bias under weak proxies is not a PDE
counterexample, stationarity/LRT proxies do not prove the Type-I bias bound,
and Clay NS remains false.
The corrected Gaussian self-similar balance is the current bridge from this
finite kappa package to the PDE layer:
`2 int |grad omega|^2 G - 1/2 int |omega|^2 G =
4 Bias_G Omega_G + Drift_G Omega_G`, hence `1 <= 4 Bias_G + Drift_G` for a
nontrivial profile after OU Poincare.  The latest variational receipt makes
stationarity the decisive proxy constraint; LRT alone does not suppress
positive kappa-bias and is retained as the separate angular-collapse guard.
The next named gap is `AbelTriadicDefectMeasureConstruction` / CKN-scale
approximate stationarity: show Type-I or ancient blowup rescalings generate
Abel triadic defect measures approximately invariant under the true Leray
transfer operator.  Without that weak-limit/stationarity step, the kappa-bias
bound, compensated leakage identity, local monotonicity, and Clay NS all stay
unpromoted.
This rung is now typed explicitly by
`NSAbelTriadicStationarityConstructionBoundary`, which splits the proof into
A1 bounded mass, A2 observable recording, A3 approximate `T_NS` stationarity
with `delta_r -> 0`, and A4 LRT output-support transfer.  The paired
`scripts/ns_abel_triadic_stationarity_proxy_harness.py` and
`NSAbelTriadicStationarityProxyHarnessResult` are synthetic diagnostics only;
they measure a finite pushforward defect and the proxy
`delta * sqrt(11/60)` bound, but they do not prove PDE stationarity or Clay NS.
The next split refines those obligations into separate owner surfaces:
`NSBoundedAbelMassEstimateBoundary` records the A1
Type-I / `L^{3,infty}` -> Littlewood-Paley shell mass -> Abel finite-variation
target and its constant-tracking blockers;
`NSQuantitativeStationarityRateBoundary` records the A3.3
`W_r = U_r - U_infty` energy-ODE / Seregin-ESS compactness-rate route and the
still-open `delta_r -> 0` proof; `NSTriadicShellBernsteinHolderBoundary`
records the A2 tight dyadic shell estimate and rejects the naive `L4 x L4`
Bernstein shortcut as insufficient; and
`NSLeiRenTianOutputSupportTransferBoundary` records the A4 physical
vorticity-direction to Fourier triadic output-direction support transfer.
`NSLeiRenTianFourierOutputCouplingBoundary` now refines A4 into the exact
Whitney/frame coupling contract: physical angular measure, localized frame
packet, Fourier output pushforward, Whitney coupling inequality,
no-angular-collapse transfer, and scale/window compatibility.  The paired
`scripts/ns_lrt_fourier_output_coupling_proxy_harness.py` is manifest-routed
as a diagnostic only.
The A4 contract now has checked child receipts:
`NSPhysicalAngularMeasureConstructionBoundary`,
`NSLocalizedWhitneyFramePacketEstimateBoundary`,
`NSFourierOutputPushforwardBoundary`, and
`NSWhitneyCouplingInequalityBoundary`.  They normalize physical angular
measure construction, Whitney packet localization, the
`Phi(theta1,theta2)=normalize(theta1+theta2)` Fourier pushforward, and the
Whitney-overlap/no-collapse inequality.  The remaining Sard/Fubini coupling
proof, A4 theorem, A6 leakage transfer, NS Clay, and terminal promotion remain
false.
The Sard/Fubini residual now has four checked child receipts:
`NSAntipodalTubeNullMassBoundary`, `NSSardRegularValueSlicingBoundary`,
`NSWhitneyFubiniDisintegrationBoundary`, and
`NSPhiJacobianLowerBoundBoundary`.  They normalize antipodal-tube discard,
regular-value slicing, Whitney-packet Fubini disintegration, and
off-antipodal Jacobian lower-bound obligations without proving A4.
`NSA4SardFubiniCompositeBoundary` now composes those child receipts back into
the Whitney coupling consumer and A4 output-support route.  The next local
A4 transfer blockers are `NSOutputGreatCircleStripSlicingBoundary`,
`NSBonyLipschitzAngularPushforwardBoundary`, and
`NSLowVorticityExceptionalMassRoutingBoundary`, covering output strip
slicing, Bony/Lipschitz angular pushforward stability, and low-vorticity /
null-output exceptional mass routing.
`NSOutputStripPreimageMeasureEstimateBoundary`,
`NSA4ExceptionalMassCompositeBoundary`, and
`NSA4NoAngularCollapseTransferCompositeBoundary` now compose those local
blockers into the direct A4 output-support route: output strip preimage
measure, exceptional-mass log-window budget, and physical-measure to output
no-angular-collapse transfer.  They are still fail-closed theorem contracts;
the analytic estimates, A4 theorem, A6 transfer, NS Clay, and terminal
promotion remain false.
`NSA4CoareaStripPreimageCalculationBoundary` now isolates the scalar coarea
calculation for `f_n(theta1,theta2)=<normalize(theta1+theta2),n>`;
`NSA4GradientFormulaLocalChartBoundary` records the local-chart derivative
and rank/noncritical obligation; `NSA4UniformInNormalConstantsBoundary`
records the compactness/Whitney overlap route to a uniform `c_A4`;
`NSA4UniformErrorBudgetCompositeBoundary` records the `c eta` lower bound
minus log-window, antipodal, low-vorticity/null-output, and Bony perturbation
losses; `NSA4ResidualPositiveAfterErrorsBoundary` records the
`r < r0(eta,R,M)` positivity target; and `NSA4ToA6TransferLadderBoundary`
records the A4 -> A5 -> A6 -> A7 dependency ladder.  These are the current
NS analytic calculation surfaces, not theorem promotions.
`NSQuantitativeStationarityRateProxyHarnessResult` binds
`scripts/ns_stationarity_rate_proxy_harness.py` to a checked proxy receipt,
and `scripts/ns_bounded_abel_mass_proxy_harness.py` supplies the matching A1
bounded-mass diagnostic.  The hard A6 split is now isolated by
`NSPointwiseToAbelAveragingBoundary`, which records the diagonal,
off-diagonal, localization, pressure, and Abel LLN/mixing obligations needed
to replace pointwise stretching by the Abel/shell mean.  The child split is:
`NSDiagonalStretchingToAbelMeanBoundary` for localized diagonal
identification, `NSOffDiagonalShellAbsorptionBoundary` for non-diagonal
LP/Coifman-Meyer/epsilon-gradient absorption, and
`NSAbelShellMixingLLNBoundary` for Abel-window decorrelation and the
`O(N_eff^-1/2)` error target.  The fourth child,
`NSLocalizationPressureCommutatorBoundary`, records localization, Leray
pressure reconstruction, pressure commutators, cutoff/boundary annuli, and
pressure-tail absorption.  `NSPointwiseToAbelCompositeA6Boundary` now ties the
four children to the parent A6 boundary, while
`NSPointwiseToAbelAveragingProxyHarnessResult` records the existing proxy
harness.  The diagnostics
`scripts/ns_pointwise_to_abel_averaging_proxy_harness.py` and
`scripts/ns_localization_pressure_commutator_proxy_harness.py` now test the
same good/bad split locally.  `NSA6ErrorBudgetCompositeBoundary` records the
current seven-line A6 budget taxonomy and
`scripts/ns_a6_error_budget_proxy_harness.py` now tests synthetic aggregate
good/bad budget separation.  The pressure/localization child is now sharpened
by `NSPressureCommutatorEstimateContractBoundary`, which names the exact
`[P_j, phi] R_i R_l`, local Calderon-Zygmund, harmonic pressure-tail, annular
cutoff, epsilon-gradient absorption, and lower-order residual-routing
obligations.  The companion
`scripts/ns_pressure_tail_absorption_proxy_harness.py` and
`NSPressureTailAbsorptionProxyHarnessResult` separate compact/Schwartz/
localized good profiles from harmonic-tail, annular-plateau, and
nonabsorbed-gradient bad cases.  `NSA6TheoremLadderBoundary` records the
child-estimate -> budget -> pointwise-to-Abel -> leakage -> residual ->
monotonicity -> CKN/BKM ladder.  The cutoff/Riesz sub-lane is now backed by
`scripts/ns_cutoff_riesz_commutator_kernel_proxy_harness.py` and
`NSCutoffRieszCommutatorKernelProxyHarnessResult`, separating smooth compact,
separated-annulus, and shell-recentered good cases from rough cutoff,
no-cancellation, and touching-core bad cases.  The harmonic-tail sub-lane is
now recorded by `NSHarmonicPressureTailAbsorptionEstimateBoundary` and
`scripts/ns_harmonic_pressure_tail_decay_proxy_harness.py`, with
mean-subtraction, annular-separation, and moment-cancellation diagnostics.
`NSPressureLocalizationSubBudgetCompositeBoundary` normalizes the pressure
child stack into one sub-budget composite, and
`scripts/ns_pressure_localization_subbudget_proxy_harness.py` plus
`NSPressureLocalizationSubBudgetProxyHarnessResult` record the finite
aggregate diagnostic only.
`NSBiotSavartShellLocalizationBoundary` now isolates the A6.2 sub-lemma
needed by the diagonal side of pointwise-to-Abel: same-shell Biot-Savart
strain multiplier ownership, off-shell shell-tail decay, Calderon-Zygmund
kernel control, Type-I `L^{3,inf}` dependence, and diagonal-to-Abel
compatibility.  The paired diagnostic
`scripts/ns_biot_savart_shell_localization_proxy_harness.py` and
`NSBiotSavartShellLocalizationProxyHarnessResult` separate same-shell /
Abel-localized good profiles from separated-tail and nonlocal-plateau bad
profiles.  `NSBonyParaproductA6RepairBoundary` records the corrected A6.2
route after the naive whole-strain same-shell localization failure:
low-frequency Bony paraproduct ownership, finite near-diagonal resonant
shells, high-frequency subleading tail, and corrected Abel-window error
routing.  `scripts/ns_bony_paraproduct_a6_repair_proxy_harness.py` is
manifest-routed as a diagnostic split between naive O(1) off-shell failures
and corrected Bony profiles.  The next NS proof to calculate is now A4
Whitney/frame physical-to-Fourier coupling; the corrected A6.2 Bony estimates,
A6, residual depletion, local monotonicity, CKN/BKM closure, and Clay NS
remain unproved.

The current Yang-Mills route has two live calculations:
`HamiltonianDominatesDefectPlusHolonomy`, recorded by
`YMHamiltonianDominatesFiniteHodgeDefectBoundary`, and
`BruhatTitsToOSLatticeTransfer`, recorded by
`YMBruhatTitsToOSLatticeTransferBoundary`.  External 2026 OS/mass-gap
preprints are candidate authority inputs only.  They do not discharge the
DASHI BT-to-Wilson action comparison, reflection positivity, clustering,
observable inclusion, no spectral pollution, or Clay-promotion gates.
`YMAdmissibleBTBoundaryConventionBoundary` records the current finite-tree
boundary-convention precondition: induced finite-ball truncations can collapse
the tested BT gap signal, while full-degree / killing-style boundary
conventions are the current admissible candidate.  This condition must be
carried into the finite gauge quotient before any Hamiltonian domination or OS
transfer step can promote.
`YMFiniteGaugeQuotientHamiltonianPreconditionBoundary` now records that
carry-through as the first operator-theoretic checklist: full-degree/Killing
domain, finite gauge quotient carrier, self-adjoint finite Hamiltonian,
holonomy/action split, and
`H_d | Omega^perp >= c1 Delta_YM + c2 Hol - E_d`.  It is a precondition
receipt, not a Hamiltonian-domination proof or YM mass-gap proof.
`YMSelfAdjointFiniteHamiltonianBoundary` now separates the finite
self-adjointness theorem from that checklist: finite domain, symmetric form,
gauge-invariant subspace, quotient descent, finite self-adjoint
matrix/operator, and discrete spectrum remain open proof obligations before
Hamiltonian domination can use the finite operator.  The diagnostic
`scripts/ym_finite_selfadjoint_hamiltonian_proxy_harness.py` checks this
finite-operator shape against nonsymmetric and domain-unstable bad cases, and
`YMFiniteSelfAdjointHamiltonianProxyHarnessResult` binds it to Agda.  The
diagnostic `scripts/ym_hamiltonian_domination_proxy_harness.py` checks the
finite matrix inequality shape for `H >= c1 Delta + c2 Hol - E` against weak-H
and near-zero-sector failures; `YMHamiltonianDominationProxyHarnessResult` and
`YMHamiltonianDominationCompositeBoundary` bind that diagnostic and chain to
Agda.  `YMHamiltonianDominationErrorBudgetBoundary` now records the finite
self-adjoint, quotient-domain, holonomy/action, negative `E_d`,
spectral-margin, reflection-positive, and OS/continuum residual budgets.  These
diagnostics and budgets are not YM theorems.
`scripts/ym_domination_spectral_margin_proxy_harness.py` is the current finite
symmetric-matrix spectral-margin diagnostic for that budget and separates
dominated quotient / holonomy gap / stable `E_d` cases from weak kinetic,
missing-holonomy, and spectral-pollution bad cases.
`YMDominationSpectralMarginProxyHarnessResult` and
`YMSpectralMarginErrorBudgetCompositeBoundary` now bind that diagnostic and
its spectral-margin error budget directly into the YM operator chain.
`YMKillingBoundarySelfAdjointnessDomainContract` now records the first YM
finite-domain theorem contract after boundary sensitivity: full-degree /
Killing boundary convention, finite BT cell domain closure, boundary flux
cancellation, gauge-domain invariance, quotient descent, symmetric finite
matrix, and finite self-adjointness.  The paired
`scripts/ym_killing_boundary_self_adjointness_proxy_harness.py` is diagnostic
only and checks symmetry defect, gauge-null leakage, induced collapse,
nonorthogonal projection, and spectral margin.  Hamiltonian domination,
OS/continuum transfer, no spectral pollution, YM Clay, and terminal promotion
remain unproved.  `YMKillingBoundarySelfAdjointnessProxyHarnessResult` now
binds that diagnostic as an Agda receipt without promoting YM-1.
`YMKillingBoundaryFluxCancellationBoundary` records the YM-1 child obligation
for finite BT Killing/full-degree boundary flux cancellation, opposing face
pairing, gauge-domain preservation, induced-ball collapse exclusion, and
self-adjointness routing.  The flux-cancellation theorem, YM-1, Hamiltonian
domination, and OS/continuum transfer remain open.
`YMKillingBoundaryOppositeFaceInvolutionBoundary` now records the finite BT
opposite-face involution, Killing weight preservation, orientation-sign
cancellation, and gauge-compatibility prerequisites that must be discharged
before the flux-cancellation child can feed finite self-adjointness.
`YMKillingBoundaryWeightPreservationBoundary` splits out the
full-degree/Killing weight equality target under the opposite-face involution
before orientation-sign cancellation and finite flux cancellation can close.
`YMKillingBoundaryOrientationCancellationBoundary` and
`YMKillingBoundaryGaugeDomainPreservationBoundary` now isolate the remaining
YM-1 finite-boundary domain blockers: normal-orientation cancellation and
gauge-domain/quotient preservation.  YM-1, Hamiltonian domination,
OS/continuum transfer, YM Clay, and terminal promotion remain open.
`YMKillingBoundarySelfAdjointnessCompositeBoundary` now composes the YM-1
child routes into one finite self-adjointness boundary, while
`YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary` records the
finite gauge-quotient self-adjoint Hamiltonian target.
`YMBochnerWeitzenbockHamiltonianDominationBoundary` records the YM-5
Hamiltonian domination route over finite Hodge defect, the YM-1 composite,
holonomy, and error-budget support.  `YMUniformPositiveHolonomyActionBoundary`
records the non-vacuum holonomy/Wilson-action lower-bound obligation.  These
remain fail-closed.

The current unification route is the sheafified four-point path:
local defect sections plus gluing residual control must prove
`HierarchyConsistencyKillsFourPointDefect`.  The governing surfaces are
`DefectSheafGluingFourPointParallelogramBoundary`,
`DefectFourPointParallelogramLawBoundary`,
`DefectHierarchyParallelogramGeneralizationBoundary`, and
`GluingResidualForcesFourPointCancellationBoundary`.  The local numerical
counterexample lane showed that coarse two-homogeneous / monotone /
subadditive conditions are not enough; the missing proof is a
gluing/polarization residual theorem that kills the four-point defect.
`GluingOperatorLinearityOnDefectQuotientBoundary` now isolates U-1a before
that theorem: define the admissible defect quotient `V` and prove the gluing
operator `G` respects zero, addition, scalars, and quotient representatives.
`scripts/gluing_operator_linearity_proxy_harness.py` is the matching local
diagnostic: quotient-linear proxies pass, nonlinear representative-dependent
counterexamples fail, and promotion stays false.
`GluingOperatorLinearityProxyHarnessResult` binds that diagnostic to Agda
without proving the real admissible quotient theorem.
`scripts/unification_gluing_quotient_admissibility_proxy_harness.py` now tests
the next quotient-admissibility proxy split: representative-invariant linear
quotient gluing passes, while representative leakage, nonlinear gluing, and a
two-homogeneous norm-like near-miss fail.  It is diagnostic only.
`UnificationGluingQuotientAdmissibilityProxyHarnessResult` binds that
diagnostic to Agda without proving quotient admissibility.
`scripts/unification_quotient_four_point_stress_harness.py` adds a
manifest-routed four-point stress diagnostic for representative-shift,
nonlinear-gluing, p-norm, and asymmetric-cross-term near misses.  It is not a
four-point theorem.
`UnificationQuotientFourPointStressProxyHarnessResult` binds that diagnostic
to Agda, and `UnificationFourPointStressCompositeBoundary` records the
quotient-admissibility -> representative-invariance -> gluing-linearity ->
four-point-cancellation -> parallelogram -> quadratic-emergence ->
signature/Clifford chain with all theorem and promotion flags false.
`UnificationGluingCrossTermNullClassBoundary` now isolates the next U-1a
sub-obligation: the cross-term `G(s1+s2)-G(s1)-G(s2)` must lie in the null
class of the admissible defect quotient before gluing linearity can feed
four-point cancellation.
`UnificationCrossTermToFourPointCompositeBoundary` now composes that
cross-term-null target into the quotient-linearity, four-point cancellation,
parallelogram, quadratic-emergence, and signature/Clifford dependency chain
with all theorem and promotion flags held false.
`UnificationGluingCrossTermLinearityLiftBoundary` records the next lift from
cross-term-null vocabulary toward modulo-null quotient linearity and the
downstream four-point cancellation dependency.  Representative invariance,
null stability, cross-term nullity, true linearity, four-point cancellation,
parallelogram, quadratic emergence, and terminal promotion remain open.
`UnificationNullClassStabilityBoundary` records the operation and
gluing-stability prerequisites for the admissible null class, including
representative invariance, addition/scalar closure, `G`-stability, and
null-to-quotient equality transport.
`UnificationNullToQuotientEqualityTransportBoundary` records the transport
from null cross-term evidence to quotient equality and modulo-null gluing
linearity before the four-point functional can consume the U-1a result.
`UnificationGluingModuloNullLinearityCompositeBoundary` now composes
null-class stability, null-to-quotient equality transport, and the
cross-term-linearity lift into the current U-1a modulo-null gluing-linearity
route.
`UnificationCrossTermNullityTheoremBoundary` now names the actual U-1a target:
the gluing cross-term `G(s1+s2)-G(s1)-G(s2)` must lie in the null class before
modulo-null linearity can feed the four-point law.
`UnificationFourPointCancellationFromCrossTermNullityBoundary` records the
downstream four-point-cancellation route from cross-term nullity through
additive test functionals, representative invariance, and polarization.
Quadratic emergence, signature/Clifford consumers, terminal unification, and
Clay promotion remain blocked until that four-point law is actually proved.

## Known Constants And Laws Population

Known constants and textbook/domain law references are populated through
`DASHI.Constants.Registry`. They enter the unified surface as auditable input
slots, not as carrier-derived theorems. The registry distinguishes:

- exact SI defining constants, which can be recorded with fixed values;
- measured physical constants, which require current CODATA/PDG-style
  authority, uncertainty, unit, and version receipts before numerical use;
- physics law targets, which name standard equation forms and their required
  adapters;
- chemistry and biology law targets, which name model laws and validation
  gates without claiming wet-lab, clinical, or causal completion;
- empirical/runtime receipt laws, which govern provenance, checksums,
  projections, and replay.

The registry also exposes `knownConstantSlotCount`, `knownLawSlotCount`, and
`authoritySourceSlotCount`, plus boolean guard fields proving the population
is external-input-only:
`constantCarrierDerived=false`, `physicalLawDerived=false`,
`calibrationPromoted=false`, `empiricalAdequacyAccepted=false`, and
`externalInputOnly=true`.

The stable receipt is
`DASHI.Constants.Registry.canonicalKnownInputsPopulationReceipt`. It records
the registry, populated-slot counts, authority-source count, fail-closed field
names, adapter discipline, and the validation command
`agda -i . DASHI/Constants/Registry.agda`.
The per-use source-binding policy is
`DASHI.Constants.Registry.canonicalAuthorityConsumptionPolicyReceipt`; it
requires authority version, source checksum, access date, value uncertainty,
rounding policy, unit convention, validity regime, source URI, and provider
receipt id before measured numeric values, rounded exact expressions, or model
law slots can be used in a promoted consumer.
Current checked counts are 40 known constant slots, 33 known law slots, and 11
authority-source slots, witnessed by `canonicalKnownConstantSlotCountIs40`,
`canonicalKnownLawSlotCountIs33`, and
`canonicalAuthoritySourceSlotCountIs11`.
Measured-value consumers should also cite
`DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization`. It normalizes 18
authority-token rows across CODATA, PDG, CODATA/PDG, mass,
electromagnetic-vacuum, and particle/SM families, including `Z_0`, with seven
required metadata fields. Accepted authority tokens, value ingestion, and
numeric promotion remain false.
The payload-consumer validator is
`DASHI.Promotion.NumericAuthorityPayloadValidator`. It records 20 payload
schema fields, 3 authority-family coverage rows, 18 payload envelopes, and 0
accepted or loaded payloads. It is the current receipt surface for deciding
whether a measured-value authority artifact is ready for ingestion.

Physics-adapter consumers outside the quantum-only view should cite
`DASHI.Constants.Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt`.
It links exact physics/metrology reference inputs, measured CODATA/PDG authority
inputs, the populated physics law targets, Gate 3/Clay route targets, and the
repo physics adapter owner surfaces for Maxwell/gauge, GR, Standard Model,
Gate 3, Navier-Stokes, and Yang-Mills. Its positive promotion is only
`boundedPhysicsTargetsPopulated=true`. Maxwell field equations, GR field
equations, Standard Model promotion, Gate 3 closure, Navier-Stokes Clay,
Yang-Mills Clay, and known-physics translation completion remain false.
Standard Model consumers asking whether the repo derives the SM from first
principles should cite
`DASHI.Promotion.StandardModelFirstPrinciplesGapIndex` and the companion
nine-row `smFirstPrinciplesBoundarySummaries` layer in
`DASHI.Promotion.ObligationIndex`. The positive boundary is finite SM
gauge/representation/hypercharge/anomaly bookkeeping. The typed non-promoting
frontier is uniqueness, generation count, Higgs/Yukawa, CKM/PMNS, gauge
couplings/running, QFT observables, empirical authority, and prior-chat
context as metadata rather than theorem authority. The prototype-source intake
row additionally records `/home/c/Documents/code/dashiQ/naw.py` and
related `/home/c/Documents/code/dashiQ` Higgs/MSSM/HEPData/MDL surfaces plus
`/home/c/Documents/code/FRACDASH` as useful toy/proxy, covariance-analysis, and
bridge-local surfaces for future authority-backed consumers, not as Standard
Model promotion. `DASHI.Promotion.StandardModelHiggsHEPDataReceiptAdapter`
is the consumable Higgs/HEPData surface: it emits checksum-bound observed-shape,
pseudo-detectability, and adapter-summary JSON from `dashiQ/13tev.py` and
`dashiQ/pseudo_data_harness.py`. The paired
`DASHI.Promotion.StandardModelHiggsCovariantComparisonLaw` surface consumes the
observed-shape receipt and `tests/fixtures/sm_higgs_baseline_fixture.json` to
emit four covariance-aware comparison rows under
`outputs/sm_higgs_covariant_comparison/`. It checks square/symmetric/positive
definite fixture covariance and computes `(d - m)^T Sigma^-1 (d - m)`, while
keeping fixture baseline authority, raw provider vector binding, accepted
authority token, holdout, empirical validation, and Standard Model promotion
false.
Maxwell-facing consumers should cite
`DASHI.Promotion.MaxwellHodgeSourceConservationObligations` for the current
inhomogeneous-side gate. It records ten Hodge/source-current conservation
rows, including metric/Hodge authority, source current `J`, `d*F=J`, `dJ=0`,
`div J=0`, unit calibration, empirical observables, and false Maxwell
promotion.
For the finite exterior-chain route, also cite
`DASHI.Promotion.MaxwellFiniteExteriorChainStrengthening`. It records 13 chain
rows from `A`, `F=dA`, and `dF=0` through Hodge, source current, `d*F=J`,
`dJ=0`, `divJ=0`, unit calibration, empirical observables, and the Maxwell
promotion guard.
The corrected P0 Hodge/YM route should cite
`DASHI.Physics.Closure.FiniteGaugeHodgeAdjointCompatibility` before any
`d_A^*F=J` claim: the next exact finite proof is weighted adjoint/IBP
compatibility, not a raw `[d_A,*]` commutator identity.  YM gap consumers
should cite `DASHI.Physics.Closure.BTFiniteMetricGaugeCompatibilityKappaBoundary`
and `DASHI.Physics.Closure.YMWeightedBTAdjointKappaCalculation` for the
weighted `w/wDual = p^((n-2k)*d)` target and finite `kappa_p = (p-1)^2/p^2`
samples.  The remaining YM analytic boundary is
`DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientGapBoundary`: transfer
matrix, OS/reflection positivity, gauge quotient, self-adjoint domain,
spectral lift, and continuum transfer remain unproved.  NS consumers should
cite `DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol` for the corrected
true non-averaged Leray bilinear interaction symbol,
`DASHI.Physics.Closure.NSCascadeClosedZeroModeOutputWidthBoundary` for the
cascade-closed `pi_out(Z_NS^infty)` positive-width target,
`DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary` for the
Abel triadic interaction-defect sheaf and Lei-Ren-Tian output condition, and
`DASHI.Physics.Closure.NSTriadicLeakageSquareFunctionCoercivityBoundary` for
the final bilinear square-function/coercivity target.  The older
single-output-angle support surfaces remain useful but nonterminal:
`DASHI.Physics.Closure.NSRankOneProjectionCommutatorFormula` for the
checked rank-one algebra,
`DASHI.Physics.Closure.NSTransverseSigmaNeighborhoodGeometry` for the
transverse local-chart target,
`DASHI.Physics.Closure.NSNonRadialityQuantificationAverage` for the finite
non-radial averaging support,
`DASHI.Physics.Closure.NSSigmaNonRadialCommutatorLowerBoundTarget` for the
Sigma lower-bound target, and
`DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary` for the
remaining NS analytic gap: LP/semiclassical defect mass with pressure
bootstrap.  The older zero-mode refinement is
`DASHI.Physics.Closure.ProjectionNonlocalityDefectLaplacianZeroModeSheaf` plus
`DASHI.Physics.Closure.NSZeroModeSetClassificationBoundary`; it does not
replace the triadic interaction zero-mode sheaf.  Lei-Ren-Tian 2025
is recorded by
`DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary` and
`DASHI.Physics.Closure.NSLeiRenTianRadialZeroModeAuthorityBoundary` as an
external great-circle authority boundary for the radial zero-mode route.  The
follow-on trap/geometry targets are
`DASHI.Physics.Closure.NSGreatCircleZeroModeTrapExclusionBoundary` and
`DASHI.Physics.Closure.NSZeroModeGreatCircleGeometryTheorem`; they record the
fail-closed obligations to prove zero-mode level-set regularity, classify
which components miss great circles, transfer vorticity-direction information
to defect-measure support, and prove quantitative mass outside zero modes.
`DASHI.Physics.Closure.NSTangentialZeroModePressureStarvationBoundary` records
Buaria/Bodenschatz/Pumir as DNS evidence only, not a deterministic ancient
profile theorem.  The shared governance surface is
`DASHI.Physics.Closure.CompatibilityLeakageCoercivityTrichotomy`; the YM
spectral next theorem is
`DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary`, now
recorded as the strengthened target
`H_d | Omega^perp >= c Delta_YM,d + c' Hol_d - E_d`, with
`DASHI.Physics.Closure.YMGaugeZeroModeVacuumRigidityBoundary` naming the
finite gauge/Hodge zero-mode sheaf-rigidity and holonomy classification target
before any mass-gap promotion.  Level-zero/cuspidal and BT-building cohomology
inputs remain external-boundary rows, not proof authority.  The core
unification bottleneck is now normalized by
`DASHI.Physics.Closure.DefectHierarchyParallelogramGeneralizationBoundary` and
`DASHI.Physics.Closure.DefectFourPointParallelogramLawBoundary`.
Downloaded Hodge/YM/string context artifacts should cite
`DASHI.Promotion.DownloadedNewAdditionsReferenceIndex`. It indexes the 36 files
under `temp-DOWNLOADED/new additions`, with checksum-bound generated manifests
at `outputs/downloaded_new_additions_reference_index/`,
`outputs/downloaded_ym_hodge_artifact_summary/`, and
`outputs/downloaded_pdf_context_probe/`. The useful Hodge/YM boundary pulled
from these artifacts is concrete but non-promoting.  The repo already has
finite Route-B/current and pure zero-current `D * F = J` support, recorded by
`DASHI.Promotion.YMStrictHodgeVariationBlockerIndex` and consumed by
`DASHI.Promotion.UnificationCriticalPathReceipt`. The exact next YM calculation
is now checked in
`DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing`: selected zero
action variation equals selected zero Euler-Lagrange pairing plus selected zero
boundary term over the user-supplied variation/action carriers. The same
critical path now consumes
`DASHI.Physics.Closure.YMStrictSelectedHodgeAlgebraLaws`,
`DASHI.Physics.Closure.YMStrictSelectedBoundaryCancellationCriterion`,
`DASHI.Physics.Closure.YMStrictSelectedNonzeroActionVariation`,
`DASHI.Physics.Closure.YMStrictSelectedSourceCurrentCoupling`, and
`DASHI.Physics.Closure.YMFiniteSelectedPairingToRealCarrierBoundary`,
`DASHI.Physics.Closure.YMStrictSelectedMatterCurrentAuthorityBridge`,
`DASHI.Physics.Closure.YMMatterCurrentConservationAuthorityBoundary`,
`DASHI.Physics.Closure.YMRealSourcedDStarFEquationBoundary`,
`DASHI.Physics.Closure.YMConditionalMatterAuthorityToRealDStarF`,
`DASHI.Physics.Closure.YMSourcedEquationToHamiltonianQuotientBoundary`, and
`DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientRequirementNormalizer`.
These
check the selected finite Hodge algebra, zero-boundary IBP reduction, nonzero
finite action split, selected source-current carrier coupling, matter-current
authority/conservation boundary, real sourced `D * F = J` wrappers,
conditional real `D * F = J` target, and the Hamiltonian quotient requirement
normalizer. Physical matter/source authority, real sourced `D * F = J`,
`missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient`, continuum mass gap,
YM Clay, Maxwell field equations, and terminal unification remain false. The
clopen/BT finite-depth extension is now typed by
`DASHI.Physics.Closure.ClopenHolographicEffectiveFieldTheoryBoundary`,
`DASHI.Physics.Closure.BTFiniteHodgeStarObligation`,
`DASHI.Physics.Closure.BTFiniteHodgeEffectiveActionTheoremBoundary`,
`DASHI.Physics.Closure.BTFiniteBuildingYMGapTransferBoundary`,
`DASHI.Physics.Closure.BTNSBoundaryDefectLeakageTarget`,
`DASHI.Physics.Closure.FiniteDepthBoundaryObservablePromotionPipeline`, and
`DASHI.Physics.Closure.P0ClayFiniteHodgeNSTopologicalStackReceipt`. These
records make the finite-depth physics path explicit: BT/clopen scaffold,
weighted primal/dual Hodge target, finite selected effective action, YM
finite-building gap-transfer boundary, NS boundary-defect leakage target, and
SM/Higgs boundary-observable promotion pipeline. Sprint165 normalizes the P0
order: calculate `BTFiniteHodgeVariationTheorem` first for the finite
field-equation bridge; calculate `AngularDegeneracyPressureCommutatorGain`
first on the NS-only Clay lane. The current narrowed blockers are weighted
Hodge adjoint/IBP to real `D * F = J`, self-adjoint YM Hamiltonian quotient,
uniform finite-building mass-gap transfer, NS LP/semiclassical defect-mass
construction with pressure bootstrap, and accepted empirical authority/holdout
receipts. Maxwell, YM/Yang-Mills,
NS/Navier-Stokes, observable, continuum, Clay, and terminal promotions remain
false. The
Sprint166 projection/nonlocality boundary adds
`DASHI.Physics.Closure.ProjectionNonlocalityLeakagePrincipleBoundary` and
`DASHI.Physics.Closure.Sprint166ProjectionNonlocalityLeakagePrincipleReceipt`.
It records the shared commutator frontier: NS needs a matrix/eigenbundle
`[Pi_+, R_i R_j]` pressure nonlocality gain, not a scalar Fourier cutoff
commutator; YM/BT needs weighted finite Hodge adjoint/IBP compatibility, with
any `[d_A,*]` defect treated only as a compatibility diagnostic rather than the
field equation. Both remain theorem targets only, with local defect
monotonicity, finite Hodge variation closure, YM gap, Clay, and terminal
promotion false. The
downloaded Sprint 82/93 YM tables record
`q = 0.23178189475262734`, `eta4_q < 1`, `eta8_q > 1`,
`su3_first_safe_k = 11`, and a conditional Master WC3 route decision; they do
not accept YM Clay, continuum mass gap, Maxwell field equations, or terminal
unification.

Whole-unification consumers should cite
`DASHI.Promotion.UnificationCriticalPathReceipt`. It consumes the checked
contraction/quadratic/signature spine, the defect/quadratic dependency index,
`DASHI.Physics.Closure.DefectQuadraticParallelogramCriticalSeam`, the depth-9
Hodge variation receipt, the strict YM Hodge blocker index, the strict selected
YM finite calculations, the SM/Higgs covariant comparison law, finite chemistry
computation, finite quantum scope, exact known-input population, and the
downloaded context index. Its positive corrections are narrow: the internal
shift-carrier quadratic spine is checked, identity dynamics and identity
quotient/hierarchy premises are inhabited, a concrete m=4 shift reducer is
calculated, the identity composite and generalization obstruction are checked,
finite Hodge/current support exists, and the selected finite YM package is now
calculated through the Hamiltonian quotient requirement normalizer. The checked
`DASHI.Physics.Closure.UnificationNextAnalyticCalculationIndex` records the six
current calculations: matter-current coupling, real `D * F = J`, self-adjoint
YM Hamiltonian quotient, broad defect seam, Higgs authority replacement, and
metrology authority binding.
The broader theorem
from strict contraction plus defect monotonicity/admissibility/hierarchy to a
projection-defect/parallelogram package, physical matter/source YM authority,
real sourced `D * F = J`, empirical authority, measured metrology, and terminal
promotion remain open.

NS-facing consumers should cite
`DASHI.Physics.Closure.NSMigrationInitiationThresholdConstantsReceipt` for the
Sprint 147/149 migration-threshold constant gate. It records seven constants,
four inequality directions, five required estimates, and five fail-closed
flags. The source/viscosity/off-axis/log estimates are normalized, not proved.
The current Sprint 150 balance surface is
`DASHI.Physics.Closure.NSSprint150SourceViscosityBalanceReceipt`. It decomposes
the source/viscosity problem into source components, retained-viscosity
components, nine analytic lemmas, six inequality rows, and fail-closed Clay
guards. The paired executable ledger is
`scripts/ns_sprint150_source_viscosity_balance.py`.

Arithmetic, moonshine, and Gate 3 consumers should cite
`DASHI.Constants.Registry.canonicalArithmeticGate3KnownInputsReferenceReceipt`.
It links Hecke, CM, modular-j, Monster/moonshine, finite prime-lane, SSP,
PAWOTG, adelic localization, finite norm, pruned density, Mosco,
no-spectral-pollution, spectral-transfer, mass-shell, NS, and YM route
surfaces. Its positive promotions are only
`finiteArithmeticRoutePopulated=true` and `densityEvidencePromoted=true`.
Gate 3 closure, Mosco recovery promotion, no-spectral-pollution promotion,
continuum transfer, mass-shell bridge, and physics-claim promotion remain
false.

Quantum-facing consumers should cite
`DASHI.Constants.Registry.canonicalQuantumKnownInputsReferenceReceipt`. It
links the exact reference inputs `h`, `hbar`, `c`, and `e`; the measured
authority inputs `alpha`, `m_e`, `m_p`, `epsilon_0`, particle masses, CKM/PMNS,
Higgs, and couplings; and the law targets for Schrodinger, Born, Dirac,
Klein-Gordon, CCR/CAR, Hilbert/GNS, AQFT, DHR/DR, and Standard Model sector
work. Its promotion guards keep quantum dynamics, Born-rule semantics, QFT,
and quantum empirical adequacy false.
The finite-mode scope decision is now checked at
`DASHI.Promotion.FiniteQuantumPhysicalScopeDecision`. It records two finite
states, two normalized basis states, five accepted finite-mode computations,
seven general blockers, and eight finite-to-general lift obligations. The
positive boundary is finite Schrodinger/Born computation over the existing
finite carrier; infinite Hilbert completion, unbounded operators, Stone and
spectral theorems, general Born semantics, QFT, and terminal promotion remain
false.
The finite closure receipt is
`DASHI.Promotion.FiniteQuantumQFTScopedClosure`: two finite Hilbert rows, two
identity-evolution rows, one zero-Hamiltonian row, four observable-probability
rows, two Born-normalization rows, and hard-false guards for general quantum,
QFT, and terminal promotion.

Chemistry-facing consumers should cite
`DASHI.Constants.Registry.canonicalChemistryKnownInputsReferenceReceipt`. It
links exact chemistry reference inputs `N_A`, `k_B`, `R`, `e`, `F`, `h`,
`hbar`, and `c`; measured authority inputs for `alpha`, `m_e`, `m_p`,
`epsilon_0`, spectra, thermochemistry, `pKa`, rates, diffusion, binding, and
activity data; and the local chemistry/DNA/supervoxel owner surfaces. Its
positive promotion is only `localDefinitionalChemistryPopulated=true`.
Physical chemistry, spectroscopy, bonding interpretation, and wet-lab
validation remain false.
`DASHI.Promotion.ChemistryFiniteRuleTargets` now adds the finite computation
targets: first-ten-element Aufbau/Pauli/Hund shell rows, plus Rydberg and
Gibbs formula slots. These are finite/symbolic targets only; measured
constants, spectra, thermochemistry, physical chemistry promotion, and wet-lab
validation remain authority gated.
`DASHI.Promotion.ChemistryAuthorityBinding` now binds the next external
chemistry authority gate: three authority-token rows, three spectral-line
rows, four thermochemistry rows, two calibration rows, and four provenance
rows. NIST/CODATA/WebBook authority tokens, instrument calibration,
uncertainty/provenance acceptance, physical chemistry, spectroscopy, and
wet-lab promotion remain false.

Biology-facing consumers should cite
`DASHI.Constants.Registry.canonicalBiologyKnownInputsReferenceReceipt`. It
links exact biology reference inputs for molecule-count, thermodynamic,
electrochemical, spectroscopic, and photometric adapters; measured authority
inputs for assays, sequences, organisms, cell lines, tissues, neuroimaging,
connectomes, and clinical validity; and the law targets for central dogma,
Mendelian and population genetics, enzyme kinetics, diffusion, membrane
potentials, population dynamics, ecology, and binding/regulation. Its positive
promotion is only `structuredBiologyBridgePopulated=true`. Biology causation,
intervention, clinical validity, genome-to-connectome closure, and brain-state
recovery remain false.
`DASHI.Promotion.BiologyFiniteScopeClarification` now records the legitimate
finite biology surface: 4 DNA bases, 64 codons, 20 amino-acid symbols, 3 stop
signals, 23 protein target symbols, standard start/stop cases, supervoxel
carriers, streaming encoder surface, and checksum law. It also records six
external authority requirements. Causation, intervention, clinical validity,
connectome closure, and brain-state recovery remain false.

Empirical and runtime consumers should cite
`DASHI.Constants.Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt`.
It links provider/source/projection/comparison targets, HEPData/provider
authority inputs, PNF/ITIR runtime receipt inputs, and repo empirical/runtime
owner surfaces. Its positive promotion is only
`receiptInfrastructurePopulated=true`. Accepted provider authority,
comparison-law promotion, covariance/calibration, holdout validation, runtime
replay authority, semantic adequacy, and empirical adequacy remain false.
`DASHI.Promotion.EmpiricalReplayAcceptanceCriteria` now also exposes
`canonicalEmpiricalReplayInfrastructureTokenSummary`: six empirical/runtime
gate rows for provider authority, covariance-aware chi-square, covariance
calibration, holdout validation, runtime replay, and semantic adequacy. All
six infrastructures are populated; all six acceptance tokens remain false.

GR-facing consumers should cite
`DASHI.Promotion.GRBoundaryClarification` for the current scope decision. It
separates two bounded internal rows, Minkowski/flat recovery and flat tangent
bookkeeping, from six blocked continuum rows: non-flat Einstein equations,
Bianchi identity, stress-energy/source coupling, Schwarzschild, cosmology, and
continuum GR. GR field-equation promotion remains false.

YM-facing consumers should cite
`DASHI.Physics.Closure.YMCompletionBoundaryTightening`. It records nine
advanced YM lanes, including finite/support, small-field, lattice,
thermodynamic, OS, Wightman, continuum-transfer, and survival surfaces, plus
369/supervoxel support counts. This is an authority-conditional candidate
chain, not Clay promotion: external acceptance, all-provider derivation, Clay
statement discharge, and `clayYangMillsPromoted` remain false.
`DASHI.Physics.Closure.YMExternalAcceptancePacketNormalization` now records
the external-acceptance packet gate: six external authority tokens, five
reproducibility artifacts, eight packet components, and six false-promotion
guards. Internal packet readiness is not external Clay acceptance.

Standard-Model-facing consumers should cite
`DASHI.Promotion.StandardModelFiniteRepresentationNarrowing` for the narrowed
finite claim surface. It records three gauge rows, p2/p3/p5 surfaces, five
one-generation targets, five conductor hypercharge rows, and eight blockers.
Continuous gauge reconstruction, exact physical representation content,
PDG/empirical authority, and broad Standard Model promotion remain false.

Exact SI defining constants are already populated as reference-only slots:

| Constant | Symbol | Value | Unit | Consuming lanes |
|---|---|---:|---|---|
| Caesium-133 hyperfine transition frequency | `Delta nu Cs` | `9192631770` | `Hz` | time/frequency, measurement, runtime clock provenance |
| Speed of light in vacuum | `c` | `299792458` | `m s^-1` | Maxwell, relativity, GR, QFT, empirical calibration |
| Planck constant | `h` | `6.62607015e-34` | `J s` | Schrodinger, QFT, quantum measurement, chemistry spectra |
| Elementary charge | `e` | `1.602176634e-19` | `C` | Maxwell, electrochemistry, Standard Model sector, membrane biology |
| Boltzmann constant | `k_B` | `1.380649e-23` | `J K^-1` | thermodynamics, statistical mechanics, chemistry kinetics, biology energetics |
| Avogadro constant | `N_A` | `6.02214076e23` | `mol^-1` | chemistry stoichiometry, molecular biology, cross-scale simulator |
| Luminous efficacy at 540 THz | `K_cd` | `683` | `lm W^-1` | measurement, biology vision/retina observations |

Exact derived SI constant slots are also populated by expression, with rounding
left to consuming artifacts: `hbar = h / (2 pi)`, `R = N_A k_B`,
`F = N_A e`, `K_J = 2e/h`, `R_K = h/e^2`, `G_0 = 2e^2/h`,
`Phi_0 = h/(2e)`, `eV = e J`, `N_A h`, `c_1 = 2 pi h c^2`, and
`c_2 = h c / k_B`. Radiation constants are exact expression slots only;
blackbody-law applicability remains adapter-bound.

Measured constant slots are intentionally populated by name but not by frozen
numeric value in this repo-facing map. Current examples include `G`, `alpha`,
`m_e`, `m_p`, `epsilon_0`, `mu_0`, `Z_0`, `R_infinity`, `m_n`, `m_mu`,
`m_tau`, `m_p c^2`, `a_0`, `E_h`, `mu_B`, `mu_N`, Higgs/W/Z masses, quark
masses, CKM/PMNS parameters, `alpha_s`, and `G_F`. They must be consumed
through a source/version/uncertainty/unit authority receipt such as the W4
physical-unit and Candidate256 calibration surfaces before a physical
prediction can use them.

Authority source slots are populated for BIPM/NIST SI definitions, NIST
CODATA constants, PDG particle data, NIST Chemistry WebBook, clinical genetic
test validity framing, BIDS neuroimaging provenance, connectome dataset
authority candidates, FAIR provenance, HEPData/provider receipt authorities,
and PNF/ITIR runtime receipt authorities. These are source classes and URIs,
not accepted tokens by themselves.

Physics law slots are populated as adapter targets:

| Law target | Canonical form | Required adapters |
|---|---|---|
| Newtonian mechanics | `F = m a` plus frame assumptions | mass calibration, force/acceleration units, inertial frame, validity regime |
| Newtonian gravitation | `F = G m1 m2 / r^2` | `G` authority, mass/distance calibration, weak-field validity |
| Conservation and continuity laws | `d rho/dt + div J = source` | density/current carrier, source law, boundary conditions, units |
| Thermodynamic laws | energy conservation, entropy inequality, third-law reference behavior | state variables, temperature, entropy/free-energy carrier, validity regime |
| Klein-Gordon equation | `(Box + m^2) phi = 0` | Lorentzian metric, mass parameter, field representation, quantization boundary |
| Dirac equation | `(i gamma^mu partial_mu - m) psi = 0` | gamma matrices, spinor bundle, mass calibration, gauge coupling |
| Standard Model gauge and matter law | `SU(3)c x SU(2)L x U(1)Y` with Higgs/Yukawa/anomaly constraints | representation table, hypercharge normalization, Higgs/Yukawa couplings, CKM/PMNS inputs, empirical authority |
| Maxwell equations | `dF = 0; d * F = J` | curvature carrier, Hodge/metric, source-current extraction, unit calibration |
| Lorentz force law | `F = q (E + v x B)` | charge authority, velocity/metric carrier, matter representation |
| Schrodinger equation | `i hbar d psi/dt = H psi` | Hilbert representation, self-adjoint Hamiltonian, Born rule, calibration |
| Born probability rule | `P(outcome) = abs(amplitude)^2` | outcome sigma algebra, state normalization, empirical observable map |
| Einstein field equation | `G_mu_nu + Lambda g_mu_nu = 8 pi G T_mu_nu / c^4` | non-flat Levi-Civita, Ricci/scalar contraction, stress-energy, `G` calibration |
| Navier-Stokes equations | incompressible momentum, pressure, viscosity, divergence-free flow | weak/strong solution class, pressure reconstruction, energy inequality, regularity criterion |
| Yang-Mills equation and mass gap target | `D_A F_A = 0` plus continuum quantum mass-gap target | Lie algebra representation, Wilson action, OS positivity, Wightman reconstruction, continuum mass-shell |

Chemistry and biology law slots are populated as model or domain-reference
targets:

| Lane | Law target | Required adapters |
|---|---|---|
| Chemistry | stoichiometric conservation | element identity, charge state, reaction authority, Avogadro/mole unit |
| Chemistry / biology | law of mass action | activity/concentration carrier, temperature, rate constants, empirical calibration |
| Chemistry | ideal gas law | equation-of-state authority, temperature/pressure/volume units, validity regime |
| Chemistry / biology | Arrhenius law | activation energy, temperature, rate measurement, fit authority |
| Empirical chemistry / biology | Beer-Lambert law | optical path, molar absorptivity, concentration, instrument calibration |
| Electrochemistry / membrane biology | Nernst equation | temperature, charge number, activities, electrode/membrane authority |
| Chemistry / biology energetics | Gibbs free energy relation | enthalpy/entropy authority, temperature, activity model, standard-state convention |
| Chemistry / biology pH | Henderson-Hasselbalch equation | `pKa` authority, activity/concentration convention, temperature, buffer validity regime |
| Molecular biology | central dogma information flow | sequence provenance, transcription/translation context, organism/cell authority |
| Genetics | Mendelian inheritance | genotype/phenotype observation, pedigree/provenance, model validity |
| Population genetics | Hardy-Weinberg equilibrium | population sampling, random-mating/no-selection assumptions, statistical validation |
| Enzyme kinetics | Michaelis-Menten kinetics | enzyme/substrate measurement, steady-state assumptions, fit authority |
| Transport biology | Fick diffusion law | concentration field, diffusion coefficient, geometry/medium authority |
| Electrophysiology | Nernst membrane potential | ion concentrations, temperature, charge, membrane measurement authority |
| Electrophysiology | Goldman-Hodgkin-Katz membrane equation | ion concentrations, permeability ratios, temperature, membrane protocol authority |
| Population biology | logistic population growth | population observation, growth-rate fit, carrying-capacity fit, holdout validation |
| Ecology | Lotka-Volterra interaction model | species observation, interaction fit, sampling protocol, holdout validation |
| Biochemistry/regulation | Hill binding equation | ligand concentration, binding fit, cooperativity parameter, assay authority |

Required fail-closed reading for every populated slot:

```text
constantCarrierDerived = false
physicalLawDerived = false
calibrationPromoted = false
empiricalAdequacyAccepted = false
externalInputOnly = true
```

The point of this population is to eliminate empty adapter placeholders while
preserving the blocker map. Source presence alone does not prove Maxwell,
Schrodinger, GR, Standard Model, chemistry, biology, empirical, or clinical
adequacy.

## Promotion Ladder

Promotion maturity is separate from validation cost. The `S*` stages below
describe claim readiness; `L0/L1/L2` targets in
`Docs/AgdaValidationTargets.md` describe how expensive a check is.

The stable Agda owner is
`DASHI.Interop.CategoricalInterlinkLayer.canonicalCategoricalInterlinkReceipt`.
It cites the constants population, authority consumption policy, physics
adapter, arithmetic/Gate 3, quantum, chemistry, biology, and empirical/runtime
reference receipts and records 7 ladder rows, 12 lane objects, 16 lane morphisms, and 14
registry-lane bindings, witnessed by
`canonicalPromotionLadderCountIs7`, `canonicalLaneObjectCountIs12`,
`canonicalLaneMorphismCountIs16`, and
`canonicalRegistryBindingCountIs14`.

The sprint-facing promotion queue is
`DASHI.Promotion.ObligationIndex.canonicalUnifiedPromotionObligationIndex`.
It imports the six code-owner lanes for numeric/authority, classical fields,
quantum/QFT, chemistry/biology, Gate 3/Clay, and Standard Model/terminal
unification obligations. The aggregate records 6 lane summaries and 73 open
promotion obligations, witnessed by
`canonicalUnifiedPromotionLaneCountIs6` and
`canonicalUnifiedPromotionOpenObligationCountIs73`; terminal promotion remains
false by `canonicalUnifiedPromotionTerminalPromotionIsFalse`.
The same aggregate now also records 6 non-promoting adapter advancements via
`canonicalUnifiedPromotionAdapterAdvancementCountIs6`: measured authority
binding, Maxwell exterior calculus, finite Schrodinger/Born, chemistry
quantitative adapters, empirical/runtime replay, and the Gate 3/SM/Clay
evidence reducer.
It additionally records 6 token/reducer advancements by
`canonicalUnifiedPromotionTokenReducerAdvancementCountIs6`: numeric authority
token intake, Maxwell Hodge/source calibration, finite-to-general quantum
boundary, chemistry/spectroscopy authority intake, empirical replay
acceptance criteria, and Clay proof/translation reduction.

| Stage | Required evidence | Promotion reading |
|---|---|---|
| S0 carrier named | Lane has a named carrier, owner, and target vocabulary. | Not a theorem claim. |
| S1 bounded observable | Observable or theorem target is bounded enough to cite. | Target is inspectable but not validated. |
| S2 executable/formal receipt | Agda receipt, script output, or provider receipt exists. | Receipt exists but can still be non-promoting. |
| S3 fail-closed Agda guard | Claim guard is false by construction or impossible without a token. | Safe for repo-wide citation. |
| S4 adapter receipt consumed | Required adapter/source/version/checksum receipt is consumed. | Local adapter can be promoted, not the global theorem. |
| S5 proof/authority token inhabited | Needed proof object or accepted authority token exists. | Claim may be reviewed for promotion. |
| S6 claim surface updated after validation | Docs, Agda owner, validation target, and changelog agree. | Only this stage changes the user-facing claim. |

## Categorical Interlink Map

`DASHI.Interop.CategoricalInterlinkLayer` defines the categorical surface as a
typed documentation/receipt graph unless a cited owner module already provides
formal functor, naturality, identity, or composition laws. Edge kinds are
`owns`, `cites`, `consumes`, `blocks`, `validates`, and
`externalAuthorityRequired`.

The receipt promotes only bounded graph facts: exact reference inputs,
external authority slots, typed surfaces, finite categorical receipts, local
definitional chemistry population, conditional authority dependencies, and
route evidence. It keeps `theoremPromoted=false`,
`empiricalAdequacyAccepted=false`, `clayPromoted=false`,
`fullStandardModelPromoted=false`, and `terminalPromotion=false`.

| Lane object | Categorical promotion | Still blocked |
|---|---|---|
| Constants and SI metrology | Exact reference inputs and authority slots are populated and counted. | Carrier derivation, physical-law derivation, calibration, empirical adequacy. |
| Quantum / Schrodinger / measurement | Typed surface and exact quantum reference inputs are linked. | Hilbert representation, self-adjoint Hamiltonian, Born semantics, QFT, empirical adequacy. |
| QFT / DHR / Standard Model | Finite prime-lane categorical receipts and conditional DHR/SM status can be cited. | Full DHR/DR theorem, exact SM match, continuous gauge group, CKM/Higgs/lepton physical promotion. |
| Chemistry / DNA / supervoxel | Local definitional chemistry population is promoted. | Physical chemistry, spectroscopy, bonding interpretation, wet-lab validation. |
| Biology / genome / brain | Structured bridge and observation surfaces are typed and linked. | Causation, intervention, clinical validity, genome-to-connectome closure. |
| Maxwell / gauge | Standard law target and exact/metrology inputs are linked. | Metric/Hodge, source-current extraction, electromagnetic constant authority, calibration. |
| GR | `c` and `G` inputs plus Einstein-equation target are linked. | Non-flat curvature, stress-energy, `G` authority, GR empirical calibration. |
| Empirical / runtime | Provider, checksum, projection, comparison, and runtime receipt classes are linked. | Accepted authority tokens, covariance/comparison law, replay authority, semantic adequacy. |
| Gate 3 / arithmetic | Finite norm/density/Mosco route evidence is linked. | Gate 3 closure, no-pollution/Mosco recovery, continuum and mass-shell transfer. |
| Navier-Stokes | Law target and pressure/phase obstruction bookkeeping are linked. | Standard PDE regularity, nonlinear passage, pressure reconstruction, Clay promotion. |
| Yang-Mills | Law target and KP/Balaban/OS/Wightman route evidence are linked. | Continuum YM, OS/Wightman completion, positive mass gap, Clay promotion. |

## Priority Completion Ladder

| Priority | Lane | Current completion reading | Non-completion boundary |
|---|---|---|---|
| 1 | Chemistry | Locally strongest template: definitional chemistry, atomic, DNA, and supervoxel surfaces give the cleanest example of a local carrier-to-receipt path. | Not wet-lab complete, not spectroscopy or bonding complete, and not physical-chemistry calibrated. |
| 2 | Biology / DNA / brain | Structured and bridged: observation, codec, channel, representation, and chemistry handoff owners are present. | Not causation, intervention, clinical, or external measurement-authority complete. |
| 3 | Physics adapters | Strongest theorem architecture: canonical closure plus Maxwell, Schrodinger, GR, measurement, sector, and cross-scale surfaces define the broad target. | Adapter-blocked for known physics: metric, representation, Born/statistics, constants, source laws, and empirical calibration remain required. |
| 4 | Navier-Stokes and Yang-Mills | Highest proof priority: active Clay-facing analytic lanes with explicit fail-closed receipts. | Must translate into standard PDE/QFT, gauge/field equations, empirical prediction paths, and cross-scale matter context before promotion. |
| 5 | Arithmetic / moonshine / Gate 3 | Important transfer layer: Hecke/CM/moonshine and finite-frame surfaces feed density, Mosco, no-pollution, and mass-shell targets. | Gate 3 continuum transfer and physics-facing mass-shell translation remain open. |
| 6 | Empirical and runtime lanes | Packaged receipt infrastructure: provider intake, comparison, PNF/ITIR residual, parser, and provenance shapes are present. | External authority, source checksums, replayable runtime receipts, semantic adequacy, and accepted validation remain required. |

## Unified Maturity Matrix

This table extends the physics maturity vocabulary across the full unified
surface. `known-physics translation required` marks lanes whose current
carrier result must still be expressed in standard PDE, QFT, field-equation,
measurement, or physical-model language before it can support a physics-facing
claim.

| Lane | Present | Bridged | Packaged | Theorem-complete | Empirically-validated | Known-physics translation required | Current reading |
|---|---:|---:|---:|---:|---:|---:|---|
| Chemistry | yes | yes | yes | partial | no | yes | Strong local definitional template; physical chemistry, spectra, bonding, and wet-lab authority remain blocked. |
| Biology / DNA / brain | yes | yes | partial | no | no | yes | Structured observation, DNA, codec, and brain crossover surfaces exist; causation, intervention, clinical, and measurement validation remain blocked. |
| Cross-scale simulator | yes | yes | partial | no | no | yes | Unified matter facade and stellar-style proxy route exist; real-model authorities and empirical receipts remain missing. |
| Maxwell / gauge | yes | yes | partial | no | no | yes | Static/finite gauge and matter-field surfaces exist; field-equation recovery needs curvature, Hodge, source-current, metric, and calibration adapters. |
| Schrodinger | yes | yes | yes | no | no | yes | Bounded Hamiltonian/dynamics consumers exist; no self-adjoint Hilbert representation, Born rule, or calibrated textbook derivation is claimed. |
| GR | yes | yes | yes | no | no | yes | Known-limits and weak-field baseline surfaces exist; non-flat Levi-Civita, curvature contraction, stress-energy, and `G` normalization remain open. |
| Empirical | yes | yes | yes | no | no | yes | Provider, residual, projection, and comparison-law infrastructure exists; accepted authority, covariance, calibration, and holdout adequacy remain external. |
| Gate 3 | yes | yes | partial | no | no | yes | Hecke/CM/moonshine finite-frame and PAWOTG/Mosco/no-pollution targets exist; continuum and mass-shell transfer remain open. |
| Navier-Stokes | yes | yes | partial | no | no | yes | Clay-facing NS route is present as analytic receipts and blockers; standard PDE regularity closure and physical interpretation remain open. |
| Yang-Mills | yes | yes | partial | no | no | yes | KP/Balaban/OS/Wightman/mass-gap receipts are active but conditional; continuum QFT existence, positive mass gap, and Clay acceptance remain open. |
| Runtime / PNF / ITIR | yes | yes | partial | no | no | no | Parser, PNF, residual, Hecke-fibre, and provenance surfaces exist; replayable external runtime receipts and semantic adequacy remain missing. |

## Implementation Roadmap

1. Unify the receipt shape.
   - For each lane, create or identify one `...Receipt.agda` owner.
   - Each owner must expose status, artifact paths or formal inputs, blocker
     constructors, canonical receipt, and promotion guards.
   - Boolean guard names should follow the lane claim directly, for example
     `carrierInternalPrediction`, `stellarEvolutionPromoted`,
     `maxwellEquationPromoted`, or `empiricalAdequacyAccepted`.

2. Add bounded executable slices before real-model claims.
   - Prefer deterministic scripts in `scripts/` with JSON/CSV/Markdown outputs.
   - Every artifact must include `promotion_status = NO_PROMOTION` unless an
     accepted authority receipt is actually present.
   - Outputs should name both observed/proxy values and missing real-model
     receipts so the next step is mechanically visible.

3. Wire each lane into the unified facade.
   - Put shared parent objects under `DASHI.Unified` only when the lane can be
     described without importing heavy closure cones.
   - Keep theorem owners under their existing physics/ontology modules.
   - The unified facade may expose receipts, but it must not become the source
     of theorem promotion.

4. Build adapter packs by family.
   - Physics lanes need metric, representation, Born/statistics, and
     calibration adapters as named blockers.
   - Empirical lanes need source, checksum, transform, comparison-law,
     covariance, and authority adapters.
   - Biology/clinical lanes need subject/session provenance, measurement
     authority, causation boundaries, and intervention/clinical validation.
   - Runtime lanes need execution provenance, parser version, source checksum,
     residual policy, and replayability.

5. Promote only through explicit gates.
   - A bounded proxy can graduate to a real-model adapter only when it consumes
     named external or theorem receipts.
   - A real-model adapter can graduate to a promoted claim only when its Agda
     guard changes from false by construction to a consumed proof/authority
     token.
   - No lane may promote from another lane's analogy, naming overlap, or
     successful proxy diagnostic.

## Milestones

| Milestone | Deliverable | Validation |
|---|---|---|
| M0: Receipt schema discipline | One short checklist for new receipt modules and scripts. | `rg` check for required promotion fields in new artifacts. |
| M1: Physics bounded slices | Maxwell, Schrodinger, GR-curvature, and empirical diagnostics mirror the stellar slice. | Focused pytest plus targeted Agda receipt checks. |
| M2: Cross-scale matter ladder | Atom/molecule/cell/organism/stellar parent receipts share the same cross-scale surface. | `agda DASHI/Unified/CrossScaleMatterPhysics.agda`. |
| M3: Adapter blocker index | One queryable blocker index for metric, representation, Born/statistics, calibration, provenance, and validation gates. | Targeted Agda owner plus docs link checks. |
| M4: Empirical authority harness | Standard source-checksum/projection/comparison-law/authority runner. | Pytest with synthetic pass/fail fixtures. |
| M5: Route commutation audit | Maintain `DASHI.Interop.CategoricalInterlinkLayer`: each lane row names owner receipt, upstream registry/doc/module, downstream consumers, blocked adapters, promotion guard, and validation target. | `agda -i . DASHI/Interop/CategoricalInterlinkLayer.agda` plus repo audit and `Docs/AgdaValidationTargets.md` updates. |

## Claim Discipline

Defensible wording:

> DASHI lanes are being normalized into one receipt-gated architecture:
> carrier grammar, bounded observable, executable/formal receipt, explicit
> blocker set, and fail-closed promotion guard.

Non-defensible wording:

> DASHI has already derived all routes because the lanes share a vocabulary.

The route-unification work is successful only when it makes missing receipts
more visible, not when it hides them behind a larger facade.

## Immediate Next Work

Use the stellar slice as the template for the next three bounded lanes:

1. Maxwell/gauge finite curvature-source proxy.
2. Schrodinger finite Hamiltonian-evolution proxy.
3. Empirical authority harness for source checksum, transform, comparison law,
   and authority decision.

After those land, add the shared adapter blocker index and route commutation
audit so the rest of the biology, runtime, arithmetic, Gate 3, NS, and YM lanes
can join the same pattern without changing their current promotion status.
