# BH4 / 369 reactive-PNP: canonical exact maximum cut (2026-11-09)

## Latest execution and implementation receipts (2026-11-09)

- **Repository commits:** `scripts/reactive_pnp_369.py` and `scripts/test_reactive_pnp_369.py` are now present on this BH4 branch, explicitly labeled assistant-authored implementation assistance of prior PNP/SG methods on user-origin DASHI geometry; they are not physiology or Golden proof. Two additional regression declarations stress a purely synthetic 27×29/12 size analogue: `test_synthetic_29_species_12_reaction_instantaneous_dissipation` and `test_sg_per_edge_electrochemical_dissipation_sign`. Local execution of the same source/test bodies: **8/8 PNP tests passed**; 6 original plus 2 added. No original Rhea species or measured rates are used by those stress cases.
- **Local source adapter (not yet committed):** `bh4_original_reactive_pnp_adapter.py` validates the exact acquired 29×12/three-residual source via the existing original Rhea checker and pinned SHA, matches 29 species charges and 12 participants/kinetic axes, rejects invented or missing species, incorrect valence, NaN and unsupported conditions. It explicitly **rejects nonzero external exchange, reactive electrodes and multicompartments** rather than assigning hidden physics. Its four negative-control tests passed locally. No positive original-source execution exists without the real Rhea certificate. This local file is not part of the Golden import.
- **Local combined verification:** 12 tests passed: 8 PNP tests plus 4 adapter fail-closed tests. These are numerical/contract regressions, not independent empirical or Agda kernel receipts. Neither `original369PNPImplicitStepExistsAndPositive` nor `original369PNPDiscreteFreeEnergyDissipation` was proved for general 29-species source parameters.
- **Actual alpha frontier remains unchanged:** G0.01–04 exact-head Agda typecheck, S0.01 authentic original Rhea bytes, S0.02–04 source rate/thermodynamic alignment, then P0.01–08 constitutive proof and P1–P3 physical/empirical downstream. An isolated closed-system solver is not a source-paid open-system boundary model.


**Authority:** existing Agda Golden owners and real source evidence. Close a formal gate only after exact-head Agda 2.9 kernel acceptance; close an empirical gate only after independently verified original observations. No CI dependence.

## Attribution boundaries

- The original 3×3×3 ternary geometry, pants gluing, 369 construction, 27 storage locations, 54 native bonds, six exterior faces and DASHI/ITIR governance are user prior art; Vec 27 is a storage chart, never the semantic geometry.
- Reactive electrochemical and energetic PNP theory belongs to Xu, Eisenberg, Song & Huang, PRE 108 064413 (2023), doi:10.1103/PhysRevE.108.064413 and Herz & Knabner, arXiv:1605.07455 (2016). Scharfetter–Gummel, implicit Euler and numerical root solving are established external methods.
- Rhea/ChEBI/UniProt curate original biochemical identities; original experimental authors own their observations. The selected 29×12 finite panel is not the whole Kitzerow network or proof of measured disease mechanism; three MTOR non-finite reactions remain explicit residuals.
- Previous assistant-authored Python `reactive_pnp_369.py` is implementation assistance on the user's geometry using a **synthetic three-species** reaction, arbitrary parameters and blocking material / zero-Dirichlet potential boundaries. Its six locally re-run tests are numerical fixtures only, not source-calibrated biology, an originality claim, Agda acceptance, or independently measured rates.
- Scientific support, derivation, research priority, direct use/contact, implementation, citation and legal attribution remain separate axes. Contact is not use; shared identifiers are not proof of source priority; citation strings and SHA hashes alone do not verify measurements. No automatic ITIR/PNF promotion.

## Exact named terminal proof/evidence inventory

**existing** means present in repository source but not necessarily kernel checked; **proposed** is a declaration/receipt to implement, not a claim of code. Ordered by highest-alpha dependencies.

| Gate | Exact named lemma or receipt | Status and required acceptance |
|---|---|---|
| G0.01 | `original369LocalSignedContinuityExact` (existing, PR #1471) | Source-written/imported; original 54 bonds and six faces; **Agda kernel OPEN** |
| G0.02 | `original29x12SpatialReactionBalance` (existing conditional, PR #1454) | Five CHNOP invariants per original voxel; actual `SourceCertifiedOriginal29x12` missing; **Agda kernel OPEN** |
| G0.03 | `original29x12SpatialSignedChargeBalance` (existing conditional) | True signed molecular-charge cross-sum; source instance/kernel OPEN |
| G0.04 | `original29x12SpatialAllHistoryCHNOPBalance` and `original29x12SpatialAllHistorySignedChargeBalance` (existing conditional) | All valid histories, each reaction with available-reactant witness; kernel OPEN |
| S0.01 | `sourceOriginalRhea29x12ByteExact` (proposed) | Actual acquired source bytes, 29 indexed species, 12 finite columns, 3 separate nonfinite MTOR residuals, exact SHA/release and strict generated Agda root; OPEN |
| S0.02 | `sourcePaidKineticAndCompartmentParameters` (proposed) | Source-specific 29 valences, diffusion, chemical standard states, thermal/dielectric/permeability data, 12 forward/back rates, site/compartment assignment and uncertainty; OPEN |
| S0.03 | `originalStoichiometricElectroneutralityOrReservoirAccount` (proposed) | `nu z = 0` for each true bulk reaction or explicit electron/electrode/reservoir current for exceptions; OPEN |
| S0.04 | `originalMassActionDetailedBalanceCompatible` (proposed) | `ln(kf/kb) = -(nu·mu°)/(RT)` in the same units/activity reference; OPEN |
| P0.01 | `original369PNPPoissonBoundaryWellPosed` (proposed) | Original finite Poisson operator, positive epsilon, source fixed charge, selected Dirichlet/Neumann/gauge and uniqueness; OPEN |
| P0.02 | `original54BondScharfetterGummelFluxExact` (proposed) | Original 54-bond electrochemical flux, equilibrium-zero/current direction and positive edge mobility; OPEN |
| P0.03 | `original54BondFluxAntisymmetryAndDivergence` (proposed) | Exact internal edge cancellation, all 27 voxel currents, signed charge and actual boundary terms; OPEN |
| P0.04 | `original29x12MassActionReactionVectorExact` (proposed) | `S v(c)` from 12 actual original reversible columns, source rate constants and nonnegativity/charge admissibility; OPEN |
| P0.05 | `original369PNPImplicitStepExistsAndPositive` (proposed) | Actual 27×29 Poisson/transport/reaction implicit root exists and remains nonnegative for stated assumptions; numerical root success is not universal existence; OPEN |
| P0.06 | `original369PNPDiscreteFreeEnergyDissipation` (proposed) | Chemical + electrostatic energy, SG and detailed-balanced reaction dissipation; explicit exterior work when open; OPEN |
| P0.07 | `original369PNPBoundaryWorkAndChargeFluxExact` (proposed) | Six-face blocking/reactive boundary selection, electron and material reservoir accounting and stoichiometrically correct Butler–Volmer flux; OPEN |
| P0.08 | `sameSourcePhysicalReactionTransportStep` (proposed terminal) | Single source-identified 27×29 state satisfying S0.01–04 and P0.01–07, original physical law, calibrated rates and time-evolving boundary; OPEN |
| P1.01 | `physicalBH4StepCommutes` (proposed) | Same physical P0.08 state and original BH4 observation commute one step; existing `BH4PNPSamePhysicalHistoryBridgeExact` interface not instantiated; OPEN |
| P1.02 | `physicalPNPStepCommutesOriginal` (proposed) | Selected real original PNP projection agrees with actual physical step, not a separate toy state; OPEN |
| P1.03 | `physicalTissueOneStepRefinement` (proposed) | Original 369/pants-glued tissue and 54-bond readout refine same physical step; `BiologicalSourcePhysicalTissueSimulationExact.physicalOneStep` uninstantiated; OPEN |
| P2.01 | `physicalKernelLumpsUnderInterventions` (proposed) | Selected physical controlled stochastic kernel lumpable under all justified interventions; OPEN |
| P2.02 | `physicalFutureQuotientIsMinimal` (proposed) | Distinguishing future experiments for all inequivalent quotient classes; OPEN |
| P3.01 | `sourceCalibratedParametersAdmissible` (proposed) | Independent original rate/diffusion/boundary data, compartment and experimental identification, uncertainty; OPEN |
| P3.02 | `heldoutFuturePredictionsDiscriminate` (proposed) | Predeclared holdout predictions, uncertainties, independent alternatives and negative controls; OPEN |
| P3.03 | `originalBH4PNPGoldenITIRReconciled` (proposed) | Reconcile draft #1454/#1471; exact-head Agda + source/stochastic/ITIR referee receipts; OPEN |

## Phases, deliverables and acceptance

| D0 | Complete exact-head G0.01–04 Agda compilation and transitive imports | Kernel receipts pending |
| D1 | Recover independent Rhea 29×12 source and kinetic/boundary evidence | S0.01–04 pending |
| D2 | Original SG–PNP–mass-action positive, conservative, dissipation-certified physical step | P0.01–08 pending |
| D3 | Same-state BH4/PNP/tissue commuting squares | P1.01–03 pending |
| D4 | Physically controlled stochastic quotient/minimality | P2.01–02 pending |
| D5 | Source-calibrated prediction and blinded holdout | P3.01–02 pending |
| D6 | Reconciled Golden/ITIR with explicit attribution and evidence source | P3.03 pending |

**Local numerical baseline:** 6/6 synthetic `reactive_pnp_369.py` tests rerun successfully on 2026-11-09. That solver has 27 original voxels, 54 native bonds, only three synthetic species, closed blocking mass boundaries and grounded electrostatics. It has not been committed to the repo or accepted as a source-specific P0 constitutive law as of initial audit. Do not fill source gaps with simulated data.

**Next exact cut:** implement source-identity-gated 29-species numerical adapter on the same 54 bonds, add source attribution/negative controls, then run exact-head Agda check on G0.01–04. The P0.05–07 physical proofs remain open independently of numerical simulation.


## 2026-11-09 P0.03 exact-incidence continuation (assistant-authored verification)

**Implemented in this branch:** `scripts/check_bh4_native_incidence_exact.py` and
`scripts/test_bh4_native_incidence_exact.py`. The exact rational checker is a
native 27-site/54-edge linear-algebra certificate, not original-Rhea biological
data, not Agda kernel acceptance, and not an original PNP constitutive proof.
It uses the existing DASHI ternary geometric carrier and does not replace
pants-gluing semantics with a flat-vector ontology.

**Proved at the mathematical/algebraic level:** for the native oriented
incidence matrix `B`, each of its 54 columns has exactly one `-1` and one
`+1`, hence `1^T B = 0`. Therefore `1^T B J = 0` for every
54-by-n finite current matrix `J`, regardless of entries or rate laws.
For an n-by-r reaction matrix `S`, site reaction rates `v`,
valences `z`, and explicit exchange `X`, the exact identity is
`dQ/dt = sum_site z^T S v_site + sum_site z^T X_site`.
If `z^T S=0` and `X=0`, global charge is invariant; otherwise
the charged reaction or boundary term must remain visible. The implemented
checker evaluates the identities using Python `Fraction`, rather than
floating-point tolerances.

**Verification boundary:** the five committed unit tests cover the native
graph, arbitrary signed rational 29-species currents, nonzero boundary work,
a deliberately charge-violating reaction, and malformed dimensions. They were
source-written in this pass; execution of these exact GitHub files and Agda
kernel compilation has **not been verified** in this environment. A pure
algebraic proof does not imply the original 29x12 source satisfies `z^T S=0`.

**Refined proof obligations:**
- P0.03a `native369IncidenceColumnCancellationExact`: port the exact
  27x54 oriented-column cancellation into Agda, prove it at the selected
  geometry and obtain exact-head kernel receipt. OPEN (Python exact checker).
- P0.03b `native369AllSpeciesInternalFluxCancellationExact`: derive
  arbitrary-current all-species cancellation in Agda. OPEN (algebra
  established, kernel not run).
- P0.03c `original369ChargeContinuityWithExplicitExchangeExact`: weld
  original-source `z^T S` certificates, boundary currents, and the
  same physical state. OPEN; blocked by S0.01/S0.03 and P0.07.
- P0.02 native SG constitutive identification remains OPEN; incidence
  cancellation holds for currents independently of this identification.
- P0.05/06 full implicit positivity and energy dissipation remain OPEN.

**Next alpha:** obtain G0.01-04 exact-head kernel receipts; port P0.03a/b
to Agda using the native geometry owner; recover S0.01 source bytes and
S0.02-04 actual chemical/kinetic certificates; instantiate P0.03c and
P0.07 against the same source-specific state. Never promote these
conditional exact-arithmetic statements to physical P0.08 or P1-P3.


## 2026-11-09 original-PNP PR recheck and implemented cut

The canonical PNP physical source is PR #1454, not a newly introduced
third PNP stack. PR #1471 already carries the native 54-bond, six-face,
signed continuity and pants-seam proof owners. Their branches are still
distinct: do not claim an Agda import of #1471 from #1454 without a
compatible branch merge and kernel receipt.

**Source-written now on PR #1454:**

- `BH4PNPSamePhysicalHistoryBridgeExact`:
  `allBH4AndPNPControlledHistoriesSamePhysicalSource` pairs the BH4
  kinetic and PNP electrodiffusion commuting statements for precisely
  one source-selected physical history.
  `allSameSourceBH4PNPAndRoute` additionally carries the original
  source-permitted cumulative circulation route. Both are conditional
  on an inhabited `SameSourceBH4PNPModel`; neither constructs the
  source-verified physical kernel or original measured kinetics.
- `scripts/bh4_original_reactive_pnp_adapter.py`:
  newly committed fail-closed adapter to the **existing**
  `check_bh4_original_panel_spatial_events.check_certificate` and
  `reactive_pnp_369.Model`. Requires actual source certificate bytes
  with a pinned digest and **exact** original 29×12 matrix, all 29
  source-identified species, all 12 original reaction columns, 27
  explicitly selected voxel compartments, original ionic valences,
  each species diffusion and chemical reference, each reaction pair
  of forward/reverse rates, energy/dielectric/mesh parameters and
  explicit source-reference strings. No implicit zeros or synthetic
  biological parameter fill.
- The adapter reconstructs forward/back mass-action **gross**
  substrate and product matrices from exact Rhea participant sides,
  not the signed net `S` alone. This preserves species occurring on
  both sides (e.g. unchanged catalyst) and checks net
  `products - reactants = S.T` before passing to the original solver.
- It explicitly rejects non-blocking exchanges, reactive electrodes,
  multiple voxel compartments, unsupported boundary conditions,
  missing/extra species or rates, incorrect ionic charge, nonfinite
  parameters, and failed original detailed-balance checks.
  Input source references are syntactic only; receipt flags remain
  `parameter_sources_independently_authenticated=false`,
  `original_rates_independently_measured=false`,
  `physical_observer_commutation_proven=false`,
  `agda_kernel_checked=false`.
- `scripts/test_bh4_original_reactive_pnp_adapter.py` provides
  a synthetic-only matrix fixture with strict negative controls and
  original-gross-catalyst preservation regression. The fixture mocks
  only the source certificate validator; it is NOT an authentic Rhea
  acceptance, and no numerical tests have been run in this session.

**Revised remaining maximum cut:** S0.01 acquired original Rhea bytes
and actual 29×12/3 residual certificate; S0.02 physical parameters with
separate independent source authentication; S0.03 source-paid charge or
reservoir/electrode accounting; S0.04 detailed balance under actual units;
P0.01 actual Poisson boundary-value existence/uniqueness;
P0.02--04 source-selected original 54-bond SG and mass action;
P0.05 positivity/existence of implicit coupled root;
P0.06 rigorous dissipation with open-boundary work;
P0.07 genuine six-face open/reactive boundary conditions;
P0.08 physical reaction-transport state;
P1.01--03 cross-branch BH4/PNP/tissue same-state observer commutation;
P2 stochastic all-intervention lumpability and minimality;
P3 independent original assay/longitudinal comparison; G0 Agda
type-check and source-bound referee receipt. These remain OPEN.

**Validation:** Source-written and committed to the existing BH4
branch, *not kernel-checked or numerically executed in this session*.
The adapter is a candidate constitutive interface and deliberately
cannot complete the original physical law without authentic inputs.


## 2026-11-09 continuation: P0.01 grounded finite operator, and cross-PR reuse

Cross-PR geometry audit found that Biology PR #1471 already contains
`BiologicalFullCubeIncidenceExact.PositiveBond`,
`allPositiveBonds`, `completeBondCount`,
`BiologicalOriginal54BondSharedVectorExact.originalPointIndex`,
and `Biological369MixedNativeFaceSignedContinuityExact.original369LocalSignedContinuityExact`.
These must be imported/welded rather than recreated as competing source
definitions. The native 3x3x3 cube is user pre-existing prior art.

**New BH4 branch artifacts:**
- `scripts/check_bh4_grounded_poisson_exact.py`: exact rational
  A = (epsilon/h²)(B Bᵀ + 2M) with M counting boundary-face incidences.
  The 54 native edges and 54 exterior face incidences come from the
  27-point ternary cube. The exact quadratic identity
  vᵀAv = (epsilon/h²)[sum_edges(v_a-v_b)² + 2sum_i M_ii v_i²]
  proves strict positive definiteness for positive h,epsilon;
  the graph is connected and has boundary faces. The script also
  supplies exact rational LDL positivity and a rational Poisson solver.
- `scripts/test_bh4_grounded_poisson_exact.py`: four test methods
  on SPD, energy identity, exact rational residual and negative controls.
  These committed test bodies have not been executed here.
- Independent local reconstruction *was* executed: 54 bonds, 54 exterior
  face incidences, 27/27 strictly positive rational LDL pivots, constant
  unit-potential energy 108 for h=epsilon=1.

**Acceptance boundary:** This establishes the *finite grounded
Dirichlet specialization* of P0.01 at the mathematical level. There is
no Agda kernel acceptance, no original source-selected BC, no proof of
a general reactive-electrode/Neumann mixed boundary model, and no
source-specific Poisson right-hand-side receipt. No P0.08/P1/P2/P3
physical gate is closed.

**Refined named leaves and maximal-cut action:**
- P0.01a `native369GroundedPoissonQuadraticIdentityExact`:
  port the 54-bond quadratic identity to Agda from the *native*
  Biology #1471 `PositiveBond` and face owners (OPEN kernel).
- P0.01b `native369GroundedPoissonKernelTrivialExact`:
  use positive epsilon,h and boundary squares to deduce the zero
  kernel (OPEN kernel).
- P0.01c `original369PNPPoissonBoundaryWellPosed`: prove the
  **source-selected** Poisson equation with genuine boundary/gauge
  compatibility (OPEN and cannot inherit generic grounded conditions).
- G0.01–04: run Agda 2.9 exact-head checks on the existing modules,
  correct any real compiler failures, and bring the owner to one
  governed PR head before ITIR promotion (OPEN).
- S0.01–04 original certificate/kinetics/electrode source evidence
  remain an independent decisive physical cut (OPEN).
- The previous P0.03a/b exact rational checker remains committed,
  but its geometric cancellation is already substantially subsumed
  by #1471's native incidence/transfer constructions; no competing
  geometric Agda owner should be introduced.

**Attribution:** exact rational checker and tests are assistant-authored
verification assistance, not a claim of discovery of finite-volume
Poisson algebra. No unsupported physiology or original Rhea parameter
identity is implied.
