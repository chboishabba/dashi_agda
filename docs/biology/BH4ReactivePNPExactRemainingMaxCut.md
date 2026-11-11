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


### 2026-11-09 original CHNOP/charge candidate-step audit

`scripts/bh4_original_reactive_pnp_adapter.py` now also implements
`check_original_closed_inventory`. It reacquires the strict original
certificate validation path, checks a pinned certificate SHA, constructs
the original 29×5 CHNOP and 29-element signed-charge arrays from the
actual source formula/charge carrier, and audits the complete 27×29
before/after concentration chart. It fails closed on shape mismatch,
negative/nonfinite values, source digest mismatch, or a componentwise
inventory defect larger than the declared finite numerical tolerance.
This is a numerical **closed-system** diagnostic only: it does not
support source flux boundary work or prove the implicit PNP theorem.

`scripts/test_bh4_original_reactive_pnp_adapter.py` adds synthetic-only
positive spatial redistribution, material creation/charge defect,
wrong-source and malformed input controls. The synthetic checker mock
is never an authentic source-acquisition receipt; the runtime
`check_original_closed_inventory` invokes the strict acquired panel
checker in normal use.

**Current source-written result:** original 29×12 gross reactant/product
sides preserved; source-pinned candidate PNP parameters required; same
BH4/PNP/circulation physical-history induction composed; selected
27×29 candidate-step CHNOP/charge diagnostic added.

**Unpaid:** exact original panel bytes + actual independently sourced
rates/diffusion/compartments and source authentication; PNP nonlinear
implicit positive root existence; fully justified electrochemical
free-energy dissipation and six-face boundary work; original physical
one-step and tissue observer commuting square; exact-head Agda Golden
and production ITIR receipts; independent biological trajectory data.
The new Python tests are committed but NOT executed in this connector
session; therefore no test success is asserted.


### 2026-11-09 fail-closed constitutive admission hardening

`scripts/reactive_pnp_369.py.Model.__post_init__` no longer
uses Python `assert` for numerical-source admission: all
dimensions, finite coefficients, integer gross reaction orders,
nonnegative diffusion, positive reaction rates, finite electrostatic
scales and fixed charge now cause explicit `ValueError` rejection
when malformed. These checks remain active under optimized Python.
`scripts/test_reactive_pnp_369.py` adds malformed coefficient,
nonfinite and shape negative controls.

This closes the narrow programmatic input-guard issue, *not*
P0.05 (general existence/positivity), P0.06 (analytic energy
inequality) or P0.08 (measured original physical state). No test
execution or Agda kernel acceptance is claimed at this head.


## 2026-11-09 high-alpha pass: all-site stoichiometric left kernels and native bond-order weld

**New Agda proof owner:** `DASHI/Biology/Molecular/BH4PanelRateWeightedConservationExact.agda`
(commits `efa1fdfd`, `6e54c0c9` on BH4 PR #1454). All proof
declarations are source-written, **not kernel-accepted**. The module
imports the existing `BH4PanelStoichiometricMatrixExact` and consumes
the original-source certificate; it does not define a substitute panel.

The generic finite lemmas `allFiniteColumnsRateWeightedConserve` and
`allFiniteColumnsRateWeightedSignedConserve` extend per-column
left-kernel identities to arbitrary Nat-valued multiplicities. The
spatial lemmas `allSitesRateWeightedConserve` and
`allSitesRateWeightedSignedConserve` extend them to any finite number
of sites, retaining the signed cross-sum rather than falsely assuming
separate positive/negative charge conservation.

Original 29x12 and 27x29x12 specializations:
- `original29x12RateWeightedCHNOPBalance`
- `original29x12RateWeightedSignedChargeBalance`
- `original369x29x12SpatialRateCHNOPBalance`
- `original369x29x12SpatialRateSignedChargeBalance`

These establish **source-conditional linear batch stoichiometric
balance** for finite event multiplicities. They do not construct the
original 12 real-valued rates `v_r(c)`, a nonnegative physical state,
or the P0.04 mass-action constitutive map. P0.04 physical acceptance
therefore remains OPEN. A 2,000-case independent synthetic signed
cross-sum integer regression passed locally. The Agda module was
re-fetched from GitHub; parentheses balanced and no explicit holes
or postulates were found. Structural checks do not imply typechecking.

**New bond-index weld:** `scripts/check_bh4_original_bond_order_weld.py`
and `scripts/test_bh4_original_bond_order_weld.py`
(commits `b756ee77`, `c120f7ba`, test correction `f7246edc`).
The previous Python PNP numerical reference enumerates bonds in
lexicographic `(voxel,axis)` order. Biology PR #1471's native Agda
`BiologicalFullCubeIncidenceExact.allPositiveBonds` enumerates
`xBonds ++ yBonds ++ zBonds` by segment first. These **are not the
same indexed current vector**, even though both describe exactly the
same set of 54 positively oriented native bonds. The new bijection
maps indices in both directions without changing endpoints.

A local independent reconstruction passed 54/54 basis-vector exact
divergence identities, an arbitrary signed-rational-current identity,
a nonidentity order check and an unpermuted-current counterexample.
The committed Python test file has been source-written and re-fetched,
but not executed as such in this environment. Full 29-species and
physical-parameter identification remain separate. This closes the
finite combinatorial **permutation specification**, not Agda
acceptance of the correspondence or physical P1.03.

**New exact remaining gates:**
1. `original369NativeBondIndexPermutationExact`: Agda-bijective
   indexing map from #1471's 54 `PositiveBond` constructors to the
   numerical list; prove inversion and incidence preservation on
   the actual same geometry. OPEN; requires stacked branch import.
2. `original369x29x12RateBalanceKernelAccepted`: kernel-check the
   four new specializations and their generic dependencies under
   Agda 2.9 against the exact BH4 head. OPEN; requires toolchain.
3. `original29x12SourceMassActionRateVectorExact`: instantiate
   original chemically identified rate constants, reversible
   affinities and admissible concentrations to produce genuine
   27x12 **real** rates. OPEN; source S0.01/02/04 unpaid.
4. `original369SourceReactionTransportContinuityWeldExact`:
   combine source-certified reaction left kernels, genuine
   boundary exchange and correctly permuted native bond currents
   on one physical state. OPEN; depends on G0, S0 and P0.07.
5. The pre-existing P0.05–P0.08, P1–P3 remain OPEN and cannot
   be inferred from a Nat-weighted stoichiometry lemma or permutation.

**Canonical attribution:** the 369 geometry/pants gluing and source
chemical programme remain user prior work; original Rhea identities
and measurements remain source-owned; the Agda implementation and
index-weld scripts above are assistant-authored assistance. No claim
of exact-head compilation, calibrated physiology, or ITIR promotion.


## 2026-11-09 Golden reachability repair — current continuation

**Found acceptance defect:** the newly source-written
`BH4PanelRateWeightedConservationExact.agda` was neither imported by
`KitzerowBH4EvidenceEverything.agda` nor enumerated in
`scripts/check_bh4_spatial_golden.sh`. Consequently a successful
pre-existing Golden run could not have constituted a kernel receipt
for its four new 29x12/27x12 declarations.

**Repaired in BH4 PR #1454:** commit `42f94aa4` adds the new
module to the actual evidence Golden import DAG. Commit `31a8f5ec`
adds that module to the fail-closed escape checker and asserts the
presence of all four terminal declaration names. These are real
repository writes. The source has been fetched, but no local Agda
binary or working GitHub clone is available in this execution
environment; therefore no kernel acceptance is claimed.

**Next executable acceptance command on the exact BH4 head:**
`bash scripts/check_bh4_spatial_golden.sh`
(the repository script invokes
`bash scripts/run_agda29_parallel_check.sh DASHI/Biology/KitzerowBH4EvidenceEverything.agda`).
The result must be a terminal process exit code and a pinned head,
not merely a PR diff or structural source scan. Upon an Agda failure,
repair the first compiler-reported declaration and rerun; do not
change the source certificate requirements or admit unchecked
postulates/metas. Exact original 29x12 chemical source still needs
`BH4_REQUIRE_SOURCE_PAID=1`, a pinned genuine Rhea SHA, and all
independently required original parameter/candidate/assay receipts.

**Current alpha:** verification of the newly imported conditional
reaction lemmas is P0 highest value. The finite bond-order adapter,
grounded Dirichlet SPD checker, and original-source provenance gates
retain their distinct statuses. No physical P0.08/P1–P3 theorem is
closed by adding a Golden import.


### 2026-11-09 original-source same-step PNP composition and nonfinite audit

The existing `scripts/bh4_original_reactive_pnp_adapter.py`
now source-writes `source_bound_closed_implicit_step`:
one selected full-panel source certificate and digest, one
27×29 original positive concentration chart, source-provided
29-species/12-reaction parameters, the existing
`reactive_pnp_369.implicit_step`, and the original
`check_original_closed_inventory` are composed on the SAME
before/after candidate. The returned candidate receipt contains
the solver diagnostics and original CHNOP/charge source audit,
with all independent source authentication, clinical validation,
Agda and physical observation-commutation flags FALSE.

The native PNP solver now explicitly rejects nonfinite log roots,
unclipped residuals, potentials, concentrations, chemical or
electrostatic energies, charge defects, and instantaneous transport
or reaction power. The source-bound wrapper separately checks every
required diagnostic field for finiteness and required numerical
bounds. Earlier `NaN > tolerance` comparisons could silently
evaluate false; they are no longer admission criteria.

Synthetic-only regression functions
`test_source_bound_one_step_same_state_candidate` and
`test_same_step_receipt_rejects_nonfinite_or_missing_diagnostics`
exercise same-source candidate receipt composition and corrupt
diagnostics using a deliberately monkeypatched numerical operator.
This is a **contract-level** fixture, not execution of a real 783-variable
29-species implicit root nor a supplied original Rhea parameter set.

**Narrowest remaining cut:**

1. `originalRhea29x12ExactSourceParameterJoin`: independently
   authenticate source release, all participant sides and chemical
   charges, 12 reversible kinetic pairs, 29 diffusion/standard
   chemical potentials, 27 voxel compartments, six-face physical
   boundary data and organism/specimen/time correspondence.
2. `original369PNPImplicitStepExistsAndPositive`: construct a
   positive implicit root under explicitly stated finite
   constitutive assumptions and prove its uniqueness if claimed.
   Numeric solver convergence alone is a different statement.
3. `original369PNPDiscreteFreeEnergyDissipation`: same original
   discrete chemical+electric free energy, true SG transport and
   original detailed-balanced reaction term; pay the selected
   Dirichlet/Neumann/reactive boundary work rather than assuming zero.
4. `sameSourcePhysicalReactionTransportStep`: instantiate a genuine
   original physical carrier with the source-paid PNP solution and
   original 29×12 chemistry. Reject a synthetic three-species or
   unmeasured 29×12 parameter fixture as an inhabitant.
5. `physicalBH4StepCommutes`,
   `physicalPNPStepCommutesOriginal`,
   `physicalTissueOneStepRefinement`: reconcile PR #1454 and
   PR #1471 on the exact same specimen, physical state and action
   schedule; then consume their already-written all-history
   theorems.
6. Golden Agda exact-head kernel and PostgreSQL/ITIR referee receipts,
   independent longitudinal model discrimination and calibrated
   stochastic future quotient remain unpaid.

**Execution status:** committed and fetched back from GitHub;
no repository-local Python test or Agda kernel run in this session,
and no independent source-rate authentication occurred.


### 2026-11-09 source-bound candidate executable entrypoint

The original `scripts/bh4_original_reactive_pnp_adapter.py` CLI
now has an optional closed-source **physical candidate step** mode.
The three options `--initial-state`, `--dt`, and
`--state-output` are jointly mandatory in this mode.
The initial-state input must contain the complete original
positive finite 27×29 concentrations with the exact 29-source-species
ordering from the separately SHA-pinned full original certificate.
The model and source receipt must pass before calling the
existing `reactive_pnp_369.implicit_step`.
The accepted output is checked against the original CHNOP and
signed-charge chart before a candidate state and numerical receipt
are written. The entrypoint is deliberately located after the
source-bound function definitions to support actual CLI execution.

Example invocation (all files and time step must be independently supplied):

```bash
python3 scripts/bh4_original_reactive_pnp_adapter.py \
  --source original-rhea-certificate.json \
  --source-sha256 ORIGINAL_64_CHARACTER_HEX_DIGEST \
  --manifest original-physical-parameters.json \
  --initial-state original-27x29-concentrations.json \
  --dt 0.01 \
  --state-output candidate-next-state.json \
  --receipt candidate-pnp-receipt.json
```

The numeric `0.01` above is merely a command-form illustration,
not an original experimentally justified timestep. No source files,
physical parameters or original measurements are supplied by this
documentation. The CLI has **not** been executed at the updated head.
Its output, if accepted, remains a closed-boundary numerical
candidate, not `sameSourcePhysicalReactionTransportStep` in Agda.


## 2026-11-09 P0.06: exact convexity/remainder theorem for closed grounded PNP

**New source-written numerical theorem checker** (assistant-authored verification
assistance, not original BH4 physical evidence):
`scripts/bh4_closed_pnp_free_energy_remainder.py`.
The four-test suite `scripts/test_bh4_closed_pnp_free_energy_remainder.py`
has been wired into the native `check_bh4_spatial_golden.sh` preflight.

For the selected **closed, blocking-material, zero-Dirichlet grounded**
discretization with positive concentrations and fixed `mu0`, `RT`,
`h`, `F`, `epsilon`, write `F(c)` for the ideal chemical and
quadratic electrostatic free energy and `mu1` for its electrochemical
gradient at positive candidate `c1`. For any positive `c0,c1` and
positive timestep `dt`, define the actual implicit residual
`delta = c1-c0-dt*L(c1)`. Then the **exact mathematical identity** is

`F(c1)-F(c0) = dt*(P_transport(c1)+P_reaction(c1))
                + h^3*sum(mu1*delta) - K_chemical - K_electrostatic`,

where
`K_chemical = h^3*RT*sum(c0*log(c0/c1)-c0+c1) >= 0` and
`K_electrostatic = (h^3/2)*(rho0-rho1)^T*A^-1*(rho0-rho1) >= 0`.
`A = epsilon*L_grounded` is strictly positive definite by the
previous P0.01 grounded certificate. The transport/reaction powers
are computed from the **same state** and 54-bond solver operator.
For source-independent detailed balance and positive coefficients
both powers are nonpositive. Consequently an **exact** implicit root
obeys `F(c1)<=F(c0)`, conditional on the stated model.

For a numerical candidate the proof does **not** erase `delta`:
`F(c1)-F(c0) <= dt*(P_transport+P_reaction)
                  + h^3*sum(abs(mu1))*max(abs(delta))`.
The script now returns the exact decomposition diagnostics,
nonnegative Bregman gaps, residual work, absolute residual-work bound,
and total energy upper bound. It never marks root existence or Agda
kernel acceptance true. A local independent 27-site/3-species
positive-state reconstruction checked the convexity/remainder identity
to approximately `1.1e-14` residual; the committed four-test suite
has **not yet been executed in this environment**. The repository
Golden command is now configured to run it before Agda.

**New named acceptance leaves:**
- P0.06a `original369GroundedPNPConvexityRemainderExact`: formalize
  the displayed identity and nonnegative Bregman gaps in the pinned
  analytic/finite-matrix theory; no imported proof beyond mathematics
  and Python diagnostics. **OPEN Agda kernel**.
- P0.06b `original369GroundedPNPExactRootDissipates`: from a
  **witnessed exact implicit root**, the SG transport sign, reaction
  detailed balance and zero boundary work, infer `F1<=F0`.
  Analytical implication established, **OPEN Agda kernel/root witness**.
- P0.06c `original369PNPDiscreteFreeEnergyDissipation`:
  extend to original 29x12 source rates, genuinely selected boundary
  reactions/reservoir energy and independently source-supported
  parameters. **OPEN S0.01–04, P0.05 and P0.07**.

No physical step existence, independent measurements, original source
certificate, continuum/physiological identification or ITIR promotion
has been achieved by this conditional analytic implication.


### 2026-11-09 P0.01 **finite constant-permittivity grounded Poisson** exact coercivity cut

The original `scripts/reactive_pnp_369.py` now contains
`original_grounded_poisson_coercivity_certificate`. It uses only the
user's existing native 3×3×3 ternary Cartesian points, the 54
nearest-neighbour directed bonds and 54 outward half-faces (six exterior
faces times nine face cells). Unlike a numerical eigenvalue check, its
verification is an **exact 27×27 integer matrix identity**:

```text
2 L_1 = 6 I_27 +
        sum_{axis in {x,y,z}, cross in {-1,0,1}²}
          [(2 e_minus - e_zero)(2 e_minus - e_zero)^T
           +(2 e_plus  - e_zero)(2 e_plus  - e_zero)^T].
```

Here `L_1` is the source's **actual** `poisson_matrix(1)`.
There are 27 native 3-site axis lines and precisely 54 indicated
rank-one positive-semidefinite terms. Consequently for **all**
`h>0`, constant `epsilon>0`, and `x∈ℝ^27`,

```text
x^T (epsilon L_h) x
 = (3 epsilon/h²)||x||²
   +(epsilon/(2h²)) ∑_27_lines [(2x_-−x_0)²+(2x_+−x_0)²]
 >= (3 epsilon/h²)||x||².
```

The inequality is **sharp**: the nonzero 27-field
`u(x,y,z)=w(x)w(y)w(z)`, with `w(-1)=w(+1)=1`,
`w(0)=2`, obeys `L_h u=(3/h²)u`.
Thus the original selected **linear** grounded Poisson problem
`epsilon L_h phi = rho` has a unique solution for every
`rho∈ℝ²⁷`, and its `ℓ²` inverse satisfies
`||(epsilon L_h)^{-1}||_2 <= h²/(3 epsilon)`.

The exact integer sum-of-squares matrix equality and equality
eigenmode were independently checked by a separate local Python
calculation before committing. The committed regression
`test_original_grounded_poisson_sharp_integer_sos` and
`test_grounded_poisson_sharp_inverse_stability` protect the
implementation, but the updated repository tests have **not** been
executed in this session.

**Correct gate reclassification:** the original fixed-Dirichlet,
constant-dielectric **finite** P0.01 linear Poisson uniqueness/coercivity
mathematics is paid (source-written exact integer certificate);
Agda kernel acceptance is OPEN. General original physical P0.01
still requires source-paid dielectric spatial heterogeneity,
actual membrane/electrode faces and alternative potential boundary
conditions. This result does **not** solve the nonlinear implicit
reaction–transport PNP fixed point P0.05, entropy dissipation P0.06,
or open/reactive face work P0.07. The native 369/pants geometry is
preserved; flattening is only an integer matrix computation chart.


### 2026-11-09 P0.06 conditional CLOSED-BOUNDARY entropy theorem (exact derivation)

Under the existing selected positive and constant physical parameters,
**strictly positive** source concentrations, original 54 native
Scharfetter–Gummel bonds, **blocking ion boundary**, all-six-face
zero Dirichlet potential, source-provided charge-neutral gross
stoichiometric sides, strictly positive detailed-balanced reversible
rate pairs, and constant positive `epsilon, RT, F, h`, we can
discharge the mathematical **conditional** free-energy inequality
for every *positive EXACT* coupled backward-Euler root.

Let `A = epsilon L_h`; the exact native integer sum-of-squares
coercivity decomposition established above proves `A` is
symmetric positive definite, so `phi(c)=A^{-1}rho(c)` is
uniquely defined. Define

```text
G(c) = h³ [ RT∑_{v,s} c_vs(log c_vs−1)
            + ∑_{v,s} mu0_s c_vs
            + (1/2) rho(c)^T A^{-1} rho(c) ],
rho_v(c) = F∑_s z_s c_vs + rho_fixed.
```

The `h³` outside the electrostatic term agrees with the exact
`free_energy` implementation. Its gradient is
`∂G/∂c_vs=h³ (RT log c_vs+mu0_s+F z_s phi_v)=h³ mu_vs`.
The ideal chemical contribution has diagonal positive Hessian
`h³ RT/c_vs` and the electrostatic contribution has a
positive semidefinite Hessian. Therefore `G` is convex for
strictly positive `c`.

For a native face `a→b`, let
`u_s=z_s F(phi_b−phi_a)/RT`, `q_a=c_as B(u_s)>0`,
`q_b=c_bs B(−u_s)>0` and `B(u)=u/(exp(u)−1)`.
The exact identity `B(−u)=exp(u) B(u)` gives
`J_ab,s=(D_s/h)(q_a−q_b)` and
`mu_bs−mu_as=RT(log q_b−log q_a)`. Thus

```text
J_ab,s (mu_bs−mu_as)
 = −(D_s RT/h)(q_a−q_b)(log q_a−log q_b) <= 0.
```

For a real bulk reaction `r`, original gross substrate/product
exponents `alpha_r,beta_r` determine the strictly positive
forward/back activities `f_r,b_r` and net rate `v_r=f_r−b_r`.
Detailed balance
`log(kf_r/kb_r)=−(nu_r·mu0)/RT` together with source-paid
`nu_r·z=0` proves
`nu_r·mu=−RT(log f_r−log b_r)`, hence
`v_r(nu_r·mu)=−RT(f_r−b_r)(log f_r−log b_r)<=0`.

Summing the native finite-volume divergence and reaction terms,
using internal-bond antisymmetry and zero species boundary flux,
proves `<grad G(c),RHS(c)> <= 0` for every positive `c`.

If a positive `c1` satisfies the **exact** implicit Euler equation
`c1−c0 = dt RHS(c1)`, `dt>0`, convexity gives

```text
G(c1)−G(c0) <= <grad G(c1),c1−c0>
             = dt <grad G(c1),RHS(c1)> <= 0.
```

No additional small-timestep restriction is needed for this
**conditional inequality**. This does **not** establish existence
of a strictly positive exact root (`P0.05`); a floating-point
nonzero residual does not satisfy the exact equation. It also does
not cover nonzero boundary exchanges, reactive electrodes,
spatially varying dielectric without proof, arbitrary rate laws,
or concentration zeros requiring limit/subgradient treatment.

The original `scripts/reactive_pnp_369.py` now includes
`closed_pnp_entropy_factorization` with per-bond and
per-reaction numerical assays of the displayed exact algebraic
identities. Committed regressions check the 54 source-native bonds,
27 selected reaction instances, and explicit invalid activities.
**Neither the new Python suite nor Agda was run at this head.**

**Gate split:** P0.01 grounded-Dirichlet finite Poisson and P0.06
**exact-positive-root conditional closed free-energy inequality**
are mathematically established in this source derivation and
source-written numeric checks; their Agda kernel certificates are
OPEN. P0.05 root existence/positive continuation, original
source kinetics and P0.07 real open/reactive boundary work remain
OPEN. The proof should be ported into the existing appropriate
Agda Bishop/PNP owner using original certified real inequalities
rather than asserting an unconditional P0.06 closure.


### 2026-11-09 P0.05: quantitative **local positive implicit-root existence** (small timesteps)

The existing original 54-bond solver `scripts/reactive_pnp_369.py` now
implements `local_positive_implicit_contraction_bounds` for its
**actual** finite 27-cell, `n`-species closed reactive PNP vector field
`F(c)=vector_rhs(c,model,poisson(c,model))`.

For any selected finite, **strictly positive** `c0` and the admitted
constant-`epsilon`, constant-positive `h,RT,F`, finite nonnegative
species diffusion, nonnegative integer gross mass-action reaction
orders, strictly positive detailed-balanced rates, and source-neutral
bulk reaction charges, set

```text
r    = min_{v,s} c0_vs / 2 > 0
Q    = max_{v,s} c0_vs + r
Q*   = max(1,Q)
Cphi = h² sqrt(27)/(3 epsilon)
P    = Cphi (F Σ_s |z_s| Q + |rho_fixed|)
Kphi = Cphi F Σ_s |z_s|
U    = 2 max_s |z_s| F P / RT
Bs   = 1+U
Ku_s = 2 |z_s| F Kphi / RT
Ar   = Σ_s alpha_rs       (original GROSS substrate orders)
Br   = Σ_s beta_rs        (original GROSS product orders)
Er+  = kf_r (Q*)^Ar
Er-  = kb_r (Q*)^Br
nu_rs = beta_rs − alpha_rs
```

For each species `s`, the following conservative explicit bounds
hold on the closed infinity-norm ball `K=B∞(c0,r)`:

```text
M_s = 12 D_s Q Bs / h²
        + Σ_r |nu_rs|(Er+ + Er-)
L_s = 12 D_s (Bs + Q Ku_s) / h²
        + Σ_r |nu_rs|(Ar Er+ + Br Er-)
M = max_s M_s
L = max_s L_s.
```

Proof: the prior exact 27-cell Poisson SOS inequality gives
`||phi||∞ ≤ Cphi ||rho||∞` and
`Lip∞(phi)≤Kphi`. At any native bond,
`|u|≤U` and `Lip∞(u_s)≤Ku_s`.
The entire Bernoulli function obeys `0<B(u)≤1+|u|` and is
globally 1-Lipschitz (`−1≤B'(u)≤0`). Each 3D voxel has at
most six incident original bonds, so the corresponding two-end
SG flux differences yield the factors `12 D_s/h²`.
For each gross mass-action monomial, telescoping the factors on
`[0,Q]` gives the bounds `Er±` and
`Lip∞≤Ar Er+, Br Er-`, respectively.
Every original reaction contributes its *signed net* `nu_rs`
to the species RHS; the absolute coefficients give the displayed
global amplitude and Lipschitz majorants. Hence
`||F(c)||∞≤M` and
`||F(c)−F(d)||∞≤L ||c−d||∞` for all `c,d∈K`.

For any `dt>0` with `dt M≤r/2` and `dt L≤1/2`,
the actual original `T(c)=c0+dt F(c)` maps the complete
closed ball `K` into itself, is a strict contraction, and satisfies
`T(c)_{vs}≥min(c0)−r=r>0`.
The Banach fixed-point theorem therefore produces **one and only
one** strictly positive fixed point **within K**, solving
`c1−c0=dt F(c1)` exactly. The previously derived closed-system
convex free-energy inequality then applies to that exact positive
root, so `G(c1)≤G(c0)`.

**Accurate closure:** P0.05 has now a *local-in-time,
finite-dimensional mathematical existence/strict-positivity theorem*
with explicit conservative data-dependent conditions; the general
all-timestep existence/uniqueness theorem remains OPEN.
The constants are returned by floating-point calculation and are
**not outward-rounded interval certificates**, so numerical output
is a candidate timestep majorant until separately formally bounded.
No Agda kernel has checked the Banach, Bernoulli derivative,
reaction monomial or selected PNP root obligations. This is a
source-written mathematical derivation, not a discharged Agda theorem
or an independently calibrated original biological physical law.

`test_local_positive_implicit_contraction_bound_and_native_residual`
now exercises the selected native source RHS by Picard iteration on
a synthetic three-species model; its finite convergence observations
are only a regression of the implementation, never proof of Banach's
hypotheses. The updated repository tests have not been run in the
current session.

**Remaining decisive maximum cut:** rigorous kernel/interval
formalization of this local theorem; an original Rhea 29×12 source
parameter inhabitant and real initial state; unrestricted timestep
or physically scoped continuation if demanded; source-selected
six-face reactive boundary work; true BH4/PNP/54-bond same-object
physical observer commutation; Golden/ITIR and independent
longitudinal biological calibration.


### 2026-11-09 P0.05 stronger topological closure: ALL-timestep existence and strict positivity

For the **closed** original 27-voxel, 54-native-bond, six-face
**blocking-species** reactive PNP model with strictly positive
initial concentrations, constant positive dielectric/temperature/mesh,
finite source-real valences/diffusivities, and nonnegative-integer
**gross** mass-action reaction sides, the source-preserved CHNOP atom
inventory supplies a mathematically stronger P0.05 result.

**Additional required original-source hypothesis:** each selected
species has a strictly positive integer weight `w_s>0` (for
example the count of original CHNOP atoms), and for every original
finite reaction column `r`,
`sum_s w_s (beta_rs-alpha_rs) = 0` EXACTLY. The existing original
Rhea checker already checks source-level CHNOP conservation;
the new adapter independently checks this selected positive
aggregate before issuing a source-weighted existence contract.
If a species has no such weight or a reaction changes it, the
result does not apply without an explicit additional reservoir.

Let `W=sum_{v,s} w_s c0_vs>0`,
`Q=W/min_s w_s` and
`K={c in [0,infinity)^(27*n): sum_v,s w_s c_vs=W}`.
This is a nonempty compact convex finite-dimensional simplex;
every component of every state in `K` is at most `Q`.
The selected original grounded Poisson operator is invertible
by the exact SOS theorem. Hence the self-consistent potential
`phi(c)` and Bernoulli factors are bounded and continuous
on `K`. Write `Bmax=1+U`, where

```text
Cphi = h² sqrt(27)/(3 epsilon)
P = Cphi [ F (sum_s |z_s|) Q + |rho_fixed| ]
U = 2 F (max_s |z_s|) P / RT.
```

For any voxel and species, the original Scharfetter–Gummel
transport loss is at most `6 D_s Bmax c_vs/h²` (six native
incident bonds, with each gain nonnegative). For an original
reaction with net coefficient `nu_rs=beta_rs-alpha_rs<0`,
its forward consuming rate carries a factor `c_vs`,
bounded by `kf_r (Q*)^(sum alpha_r-1) c_vs`;
when `nu_rs>0`, its reverse consuming rate has the analogous
`kb_r (Q*)^(sum beta_r-1)c_vs`, where
`Q*=max(1,Q)`. Gains are nonnegative. Thus the exact
source closed-model RHS satisfies the *global linear loss bound*

```text
RHS_vs(c) >= -Kloss c_vs,  for all c in K,

Kloss = max_s [
  6 D_s (1+U)/h²
  + sum_{r: nu_rs<0} (-nu_rs) kf_r (Q*)^(sum alpha_r-1)
  + sum_{r: nu_rs>0} nu_rs kb_r (Q*)^(sum beta_r-1)
].
```

Internal native-face flux cancellation and
`sum_s w_s nu_rs=0` imply
`sum_v,s w_s RHS_vs(c)=0` for all states in `K`.
For **every** `dt>0` define the continuous map

```text
H_dt(c) = [ c0 + dt (RHS(c) + Kloss c) ] / (1+dt Kloss).
```

The linear loss bound gives
`H_dt(c)>=c0/(1+dt Kloss)>0` componentwise,
and exact conservation gives
`sum_v,s w_s H_dt(c)_vs=W`; hence
`H_dt:K -> K`. By the finite-dimensional
**Brouwer fixed-point theorem**, it has some `c1 in K`
with `H_dt(c1)=c1`. Cancelling the harmless
`Kloss c1` term yields the **original implicit PNP equation**

```text
c1-c0 = dt RHS(c1), with
c1_vs >= c0_vs/(1+dt Kloss) > 0.
```

This proves **existence and strict positivity for every positive
timestep**, mathematically, on the specified *closed,
weighted-conserved finite model*, with **no global uniqueness
claim**. The earlier positive-root conditional free-energy
derivation now applies to at least one existing exact positive
implicit root for every `dt>0` in this closed model.

**Implementation:** The existing
`scripts/reactive_pnp_369.py` now contains
`global_positive_implicit_brouwer_bounds` with the exact
conservation-weight and sign preconditions; the original source
adapter `scripts/bh4_original_reactive_pnp_adapter.py`
now contains `source_bound_closed_brouwer_existence`,
which uses actual Rhea formula CHNOP atom counts and checks their
29×12 signed-matrix conservation by **integer arithmetic**.
Synthetic-only positive and adversarial tests were added in
the existing two original test owners.

**Proof authority:** This is a complete mathematical derivation
under the above hypotheses; the numerical code reports candidate
floating majorants that are NOT outward interval certified. It is
not an Agda/Bishop kernel-accepted theorem, an executable exact
numerical root, a globally unique implicit solution, a convergence
proof of SciPy's nonlinear root finder, or evidence of authentic
measured BH4 29×12 rates. The PR code/tests have not been
run at this head in the present session.

**Revised decisive cut:** P0.05 finite **closed**
all-timestep *existence+positivity* is mathematically paid under
strictly positive conserved source weights. The remaining original
gates are (i) Agda 2.9/Bishop/Brouwer trusted formalization of
this theorem, (ii) source-authenticated original 29×12 source
and physical parameter inhabitant, (iii) actual reactive boundary/
reservoir/variable-compartment extension (where the invariant
simplex argument may not apply), (iv) physical BH4/PNP/tissue
same-object step and longitudinal empirical validation,
(v) numerical root computation/verified residual rather than
existence alone, and (vi) Golden/ITIR trusted referee receipts.


### 2026-11-09 exact integer conservation repair / formal acceptance frontier

The all-timestep Brouwer existence CONTRACT is conditional on a
true, positive, exactly conserved molecular weighting. Previously,
`global_positive_implicit_brouwer_bounds` checked
`(products-reactants)@weights==0` after converting those numbers
to binary floats. This is **not** a valid exact conservation
certificate: for example, `float(2**53)==float(2**53+1)` although
the two original integer counts differ.

The original PNP numerical owner now defines
`exact_positive_conservation_weights`. It requires genuine
Python integers (not integer-valued floats or booleans) for every
gross Rhea substrate/product stoichiometric count and each strictly
positive molecular weight; for each reaction it evaluates
`sum_s (beta_rs-alpha_rs)*w_s` with exact integer arithmetic
and rejects every nonzero remainder. The `global_positive_implicit_brouwer_bounds`
consumer now invokes this exact admission gate **before** using
floating-point envelopes for `Kloss`, so a rounded false
conservation relation cannot enable the existence receipt.
Synthetic regressions include the 2**53 precision boundary,
wrong weights, nonintegral sides and Boolean coordinates.

**Precise status:**

- Original chemical **exact integer conservation precondition**:
  implemented as a fail-closed check, independent of float64
  equality (repository test execution still pending).
- Original closed finite PNP **all-timestep Brouwer mathematical
  implication**: source-written under positivity, stoichiometric
  conservation, 54 native bonds, blocking mass boundary, finite
  positive material scales; not Agda kernel-proved.
- Reported `Kloss` and positivity lower bounds are computed
  with floating-point arithmetic **without directed rounding**.
  They are NOT formally certified numerical bounds. To pay
  numeric safety, build exact rational or outward-rounded
  interval majorants at the original selected source parameters.
- The repository contains no identified trustworthy
  **constructive finite Brouwer proof** that can be reused
  immediately as an Agda theorem. Do not use an unrelated
  conditional/contraction receipt as if it discharged Brouwer.
  The remaining exact lemmas are
  `original369ClosedWeightedSimplexCompact`,
  `original369BrouwerMapContinuous`,
  `original369BrouwerMapPreservesSimplex`,
  `original369BrouwerFixedPointExists`,
  `original369ImplicitFixedPointIsPositiveRoot` and
  `original369ClosedRootFreeEnergyDecreases`. These are
  proposed proof contracts, not existing Agda declarations.
- Full selected BH4 physiology still needs actual original
  Rhea/parameter source authentication, a matched spatial
  tissue readout and physical time, reactive/open boundary
  extensions, exact-head Agda verification, and independent
  longitudinal evidence.


## 2026-11-09 P0.06 chronological energy-budget composition (new source-written owner)

**Owner:** `DASHI/Biology/BH4PNPEnergyBudgetCompositionExact.agda` is now imported by `DASHI/Biology/KitzerowBH4EvidenceEverything.agda` on BH4 PR #1454. These are assistant-authored *proof-source* additions; **Agda 2.9 kernel acceptance is still OPEN**. No source-specific Rhea/PNP parameter or measurement was supplied.

**Exact mathematical scope:** `EnergyBudgetStep initial final` holds nonnegative Nat-valued `loss` and `credit` together with a proof `final + loss ≡ initial + credit`. `composeEnergyBudget` proves exact telescoping for two receipts sharing the **same indexed intermediate energy**. `EnergyBudgetHistory` represents a nonempty chronological sequence, and `allStepsEnergyBudgetExact` collapses any such history to a single exact receipt with accumulated losses/credits. `zeroCreditHistoryHasExactLossWitness` gives `final + loss ≡ initial` whenever cumulative credit is independently proven zero. The arguments use only Nat associativity/commutativity and transitivity; there is no postulate, hole or source physics assertion in the new owner.

**Important limitation:** a Nat-valued budget is an **abstract additive certificate**; it is NOT the real-valued chemical entropy and electrostatic Bregman energy of the original 27 × 29 system. To instantiate it with physical or numerical data, first provide a same-source compatible order-preserving encoding with certified rounding/error bounds. In particular, `credit` may include exterior work and residual error only if independently justified; no actual kinetic dissipation, positive implicit root, Dirichlet time-dependent work, or detailed balance was established by the composition lemma. The next higher-alpha cut is the physical one-step receipt, *then* its repeated-time composition.

**Remaining gates explicitly unchanged:** G0.01–04 Agda receipts; S0.01–04 original source and thermodynamic data; P0.01–05 source well-posedness, SG transport, conserved reaction and positivity; P0.06 physical chemical-plus-electrostatic free-energy link; P0.07 physical boundary work; P0.08 original same-state step; P1–P3 empirical and quotient consequences. Do not promote `allStepsEnergyBudgetExact` to any of these source-gated declarations without a same-source model proof.

**Required verification:** `scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4PNPEnergyBudgetCompositionExact.agda` and `scripts/run_agda29_parallel_check.sh DASHI/Biology/KitzerowBH4EvidenceEverything.agda`. These commands are prescribed, not execution receipts.


### 2026-11-09 existing simplex search and original CHNOP weighted-simplex reuse

Repository search located several distinct existing simplex owners:

- `DASHI.Visualisation.FiveClassSimplexColourExact`:
  five nonnegative normalized *rational/numerator display weights*
  and an exact finite denominator-ten closure, **not** the
  original 783-coordinate concentration carrier.
- `DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact`:
  finite normalized rational probability atoms, including exact
  joint/deviation mass factorization, **not** source-paid
  electrochemical/stoichiometric geometry.
- `DASHI.Physics.YangMills.BalabanP33DuhamelOrderedSimplexMeasureExact`:
  exact rational integration on the **ordered two-time simplex**,
  not a probability or CHNOP concentration simplex.
- `DASHI.GameTheory.FiniteMixedNashProductCorrectionExact`,
  `GameTheoryIntrospectiveCompletionCutExact` and
  `Nash1950CorrectedExistenceAlignmentExact` explicitly state
  that the genuine finite probability simplex/fixed-point
  realisation is **still a transcription/proof debt**. Nash
  existence receipts are not Brouwer inhabitants.

The **correct source-reuse owner** for our original PNP
mass invariant is actually
`DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact`
and `DASHI.Biology.Molecular.BH4PanelRateWeightedConservationExact`.
These already prove each original CHNOP coordinate is
preserved by arbitrary finite natural reaction multiplicities
at each of the **27 original voxels**, using the same
`SourceCertifiedOriginal29x12` and real gross 29×12 reaction
sides. This is substantially closer to the physical weighted
simplex than importing a 5-class colour/probability carrier.

**New source-written Agda consumer, registered in existing BH4
evidence Golden root:**
`DASHI.Biology.Molecular.BH4OriginalCHNOPFiveAxisSimplexBridgeExact`.
It provides:

- `original369x29x12FiveAxisSpatialBalance`: the five
  source-conditional CHNOP invariants together for **one**
  27-site source reaction-multiplicity history, not five
  unrelated examples.
- `panelWeightedAddWeights`: proves the linearity of
  the **original** `Panel.panelWeighted` under the **original**
  `Panel.panelAdd` on weights.
- `combineOriginalLeftKernel`: combines any two certified
  source stoichiometric left-kernel weights exactly.
- `totalCHNOPSourceWeights`: the single 29-component
  `C+H+N+O+P` atomic weight chart, derived from the
  certified original per-element vectors.
- `sourceTotalCHNOPLeftKernel`: proves that combined
  chart annihilates **each** of the 12 original finite
  source reaction columns.
- `original369x29x12AggregateCHNOPBalance`: reuses the
  existing all-27-site rate-weighted conservation theorem
  for that aggregate weight with arbitrary natural reaction
  multiplicities.

**Critical distinction:** the source certificate itself is an
explicit *input*; the file does not invent it. A separate
strict-positive-weight witness is still required for every
source species; an atomic sum can be zero for an electron or
a missing/unsupported source species. These are exact **Nat**
stoichiometric event invariants, not continuous `ℝ^(27×29)`
compactness, measured concentrations, source-approved noninteger
mass-action rates or a verified Brouwer theorem.

Therefore the maximum cut is narrower:
the algebraic 29×12 aggregate conserved left-kernel is now
**source-written as an Agda theorem composition**,
while `original369ClosedWeightedSimplexCompact`,
`original369BrouwerMapContinuous`,
`original369BrouwerMapPreservesSimplex`,
`original369BrouwerFixedPointExists`,
`original369ImplicitFixedPointIsPositiveRoot`
and `original369ClosedRootFreeEnergyDecreases`
remain unverified **real/analytic kernel** obligations.
No Agda kernel execution was obtained in this session.


## 2026-11-09 P0.06 second cut — order bounds and separately accounted credits

**New source-written commits on BH4 PR #1454:** `BH4PNPEnergyBudgetCompositionExact.agda` now adds `initialBelowInitialPlus`, `stepFinalBoundedByInitialAndCredit`, `allStepsFinalBoundedByInitialAndCredit`, `zeroCreditHistoryNonincreasing`, and the positive-credit counterexample `positiveCreditCanIncreaseEnergy`. New owner `DASHI/Biology/BH4PNPSeparatedEnergyLedgerExact.agda` is imported into the same BH4 Golden root.

**Separated exact accounting:** `SeparatedEnergyStep` records four distinct Nat-valued nonnegative accounting categories: `transportAndReactionDissipation`, `convexityRemainder`, `numericalResidualAllowance`, `exteriorWorkAllowance`. Its exact equation is `final + (dissipation + convexity) ≡ initial + (residual + exterior)`. `toEnergyBudget` recovers the existing generic receipt, `pairRegroup` is a four-term exact additive regrouping lemma, and `composeSeparatedEnergy` proves chronological two-step composition preserving each category separately. `SeparatedEnergyHistory` / `allSeparatedStepsExact` generalize to arbitrary nonempty histories. `allSeparatedStepsFinalBound` proves `final ≤ initial + (sum residual + sum exterior)`; `noResidualNoExteriorWorkHistoryNonincreasing` requires **separate explicit zero witnesses** for both credit categories before concluding `final ≤ initial`. `positiveExteriorWorkCanIncreaseEnergy` is the deliberate open-system negative control.

**Critical scope restriction:** these are algebraic proofs over `Nat`, not a real-valued electrochemical energy functional. The separate field called `numericalResidualAllowance` does *not* automatically bound the real residual-work term; the original chemical/electrical operator must provide a certified bound, an order-preserving encoding and rounding guarantee, and its independently measured/selected exterior-work receipts. Physical P0.06, P0.07, S0.04, P0.05 and P0.08 remain open. In particular no actual positive original implicit root, SG flux entropy production, full 29x12 detailed-balanced rate law, or chemical/electrostatic free-energy proof is implied by these synthetic-free pure algebra lemmas.

**Verification:** committed source and Golden import are present; Agda 2.9 executable unavailable here. *Source-written* is not *kernel-accepted*. Needed commands:
```bash
scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4PNPEnergyBudgetCompositionExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4PNPSeparatedEnergyLedgerExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Biology/KitzerowBH4EvidenceEverything.agda
```
Existing user geometry and prior PNP/SG thermodynamic sources retain attribution; these additions are assistant implementation assistance in exact additive proof bookkeeping.

**Next highest-alpha:** attach original physical positive-entropy/Poisson one-step derivations to an *ordered real energy* accounting receipt; source-pay boundary work, residual bound, and Rhea detailed balance; then kernel check physical owner at a reconciled #1454/#1471 head. No K0 or generic deduplication detour.


### 2026-11-10 P0 source-positive CHNOP weighted-simplex admission seam

In the existing original `BH4OriginalCHNOPFiveAxisSimplexBridgeExact.agda`
owner (not a competing simplex), the next proof contract is
now source-written:

- `SourcePositiveAggregateCHNOP certificate`: for **every**
  `Fin 29` species, supplies an actual predecessor
  `k : Nat` and exact equality
  `lookup (totalCHNOPSourceWeights certificate) species ≡ suc k`.
  This is exact strict positivity, not a float threshold.
- `Original369PositiveWeightedSimplexAdmission`: pairs the
  original `Panel.SourceCertifiedOriginal29x12` with its
  per-species positive CHNOP witness, preserving source identity.
- `original369SimplexWeightAndLeftKernel`: consumes that same
  admission and gives both the selected species' positive
  weight and each selected original reaction column's aggregate
  conservation equality.
- `original369PositiveSimplexAllSitesCHNOPInvariant`:
  recovers the existing original 27×12 all-site weighted
  conservation result for precisely that admitted source.
- `zeroCHNOPWeightBlocksPositiveSource`: exact proof that
  an original species whose combined CHNOP weight is zero
  cannot inhabit `SourcePositiveAggregateCHNOP`.

These are an actual logical source-admission and no-go seam,
but **not an inhabitant** of the admission record and **not**
a proof of compactness in the original 27×29 real concentration
space. Generated original byte-pinned full panel source paths
`artifacts/biology/rhea-kitzerow-bh4-reactions.json`,
`artifacts/biology/bh4-stoichiometric-matrix.json`,
and `DASHI/Biology/Molecular/BH4Original29x12GeneratedSourceExact.agda`
were explicitly checked on the current PR branch and not found.
Thus an unconditional `sourceWeightPositive` for the real
29 species cannot be asserted or fabricated. If any selected
species is atom-free or an unresolved exchange carrier, a
different finite compactness/invariant carrier is required.

**Remaining highest-alpha P0 exact leaves:**
(1) authenticate and generate the original source;
(2) inhabit `SourcePositiveAggregateCHNOP` or establish
the exact species-specific obstruction;
(3) embed the Nat source CHNOP algebra into a single
real-valued 783-coordinate conserved mass functional;
(4) prove Poisson–SG–mass-action continuity, weighted-simplex
preservation and finite compactness there;
(5) supply a genuine Brouwer fixed-point producer and
convert it to a positive implicit root; (6) kernel-check
exact-head with Agda and its transitive imports.
Original measured kinetics, open physical boundaries,
biological same-state observation and independent held-out
empirical validation remain separate.

**Validation boundary:** commit/write/readback is not Agda
kernel checking. No Agda or Nix executable is available in
the current runtime; this module remains source-written only.


## 2026-11-10 P0.06 highest-alpha ordered-energy ledger (nonzero residuals)

**New Agda owner, Golden-imported:** `DASHI/Biology/BH4PNPOrderedEnergyHistoryExact.agda`. It replaces the earlier Nat-only limitation at the *abstract ordered-additive carrier* layer without inventing any real-number or original BH4 physical instance.

`OrderedEnergyCarrier` explicitly packages a carrier, zero, addition, order, additive associativity/commutativity/right unit, transitivity, monotonicity, addition-reflecting order cancellation, and nonnegative sums. `EnergyLaws` supplies `EnergyStep`, `compose`, `EnergyHistory`, `historyLedger`, `oneStepUpperBound`, `historyUpperBound`, and `zeroCreditHistoryNonincreasing`. Importantly, its stronger `creditPaidByLoss` theorem proves **final ≤ initial whenever credit ≤ loss, even with nonzero credit**; `paidCreditsCompose` proves closure under sequential composition. `PaidEnergyHistory`, `paidHistoryReceipt`, and `allPaidEnergyHistoriesNonincreasing` extend that implication to arbitrary finite nonempty chronological histories using the SAME indexed intermediate energies.

**Exact scope:** symbolic equality and order algebra only. No concrete ordered-real instance, real-valued mixing entropy, fixed-Poisson electrostatics, SG positivity, detailed balance or six-face boundary-energy certificate has been built. Source assumptions must be inhabited by original physical data and independently certified bounds. Do not replace the original real energy with Nat accounting, promote a synthetic PNP reference, or claim that invoking the abstract record constructs physical energy. This is assistant implementation assistance, not an original PNP law. Agda 2.9 *kernel acceptance remains open*; files and imports have been written, not compiled.

**Why this is the next reusable seam:** The exact P0.06 convexity/SG/reaction decomposition may be inserted as an `EnergyStep` on a real ordered carrier when its full identity and nonnegative dissipation are proved, and numerical residual plus boundary work are paid as `credit`. The generic theorem then shows that a solver can dissipate even with nonzero residuals whenever independently certified losses dominate that credit. This avoids the incorrect requirement that the numerical residual vanish identically.

**Next high-alpha original leaves:** (1) kernel check the new owner and the native G0 imports with `scripts/run_agda29_parallel_check.sh`; (2) instantiate the ordered carrier from verified Bishop/real inequalities and source-matched physical energy; (3) formalize SG and detailed-balanced reaction power plus Poisson boundary terms as a single source-paid one-step receipt; (4) prove outward residual/work bounds; (5) reconcile #1454/#1471, source Rhea 29x12 and all remaining P0.05–P3 physical/empirical gates. No CI is required as proof authority.


## 2026-11-10 original BH4–PNP paid-energy same-physical-state bridge

**Reuse audit:** `DASHI.Energy.Core` and `DASHI.Analysis.DissipationPathMonotonicity` already carry an abstract preorder/energy space and finite-path dissipation theorem. These are pre-existing prior art. Additional general telescope lemmas must not be mistaken for original physical P0.06 closure. The decisive consumer is the *same physical transition* used by original BH4 and PNP observers.

**New source-written owner:** `DASHI/Biology/BH4PNPSameSourcePaidEnergyExact.agda`, imported by `DASHI/Biology/KitzerowBH4EvidenceEverything.agda`. `SameSourcePaidEnergyModel` extends exactly the pre-existing `SameSourceBH4PNPModel`, provides a single physical-state energy observable on an ordered additive carrier, and *requires* for each existing `physicalStep` an exact same-state energy receipt and independently supplied credit ≤ loss. It does not construct source kinetics/physical receipts from fields alone.

**New deductions:** `onePhysicalStepPaidEnergy` uses the ordered-ledger credit-paid-by-loss theorem. `allSameSourceControlledHistoriesEnergyNonincreasing` proves descent over arbitrary original Bool control histories. `allSameSourceBH4PNPWithPaidEnergy` returns both existing BH4 and original PNP controlled-history commuting squares together with the energy bound for the very same `physicalRun`. This excludes the earlier mistake of proving a bound for a separate synthetic physical trajectory and then promoting it to the original history.

**Actual evidence frontier remains:** provide a concrete source-authenticated `SameSourceBH4PNPModel`; source-paid, physically dimensioned 29×12 original `physicalStep` and SG/reaction/electrostatic energy identities; rigorously nonnegative loss and bounded residual/electrode credit; actual native 54-bond/6-face PR #1471 shared geometry; and kernel-accepted genuine ordered-real/Bishop instance. Neither the abstract record nor same-source history inference manufactures those receipts. One-step physical P0.05–08 and P1–P3 source/empirical gates remain OPEN. Agda 2.9 was unavailable here; the newly written modules have not been kernel-checked.

**Verification command:** `scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4PNPSameSourcePaidEnergyExact.agda` followed by `scripts/run_agda29_parallel_check.sh DASHI/Biology/KitzerowBH4EvidenceEverything.agda`.


### 2026-11-10 highest-alpha P0 source-positive simplex: proof-producing decision and generated original certificate

The existing **original** `BH4OriginalCHNOPFiveAxisSimplexBridgeExact.agda`
now contains the constructive, total finite-vector decision lemmas:

- `positiveNatOrZero`: for any literal `Nat` weight,
  produces `Σ predecessor. weight ≡ suc predecessor` **or**
  the definitional equality `weight ≡ 0`.
- `allPositiveOrZeroIndex`: for any `Vec Nat n`, either
  constructs a dependent positive witness for **every** `Fin n`
  index or identifies a concrete zero-weight `Fin n` coordinate.
- `decideOriginal369SourcePositiveCHNOP`: applies this
  actual decision to the original 29-coordinate aggregate source
  CHNOP vector. No hypothesis that all weights are positive.
- `decideOriginal369WeightedSimplexAdmission`: in its
  successful branch, inhabits the **already-existing**
  `Original369PositiveWeightedSimplexAdmission` on the
  same original `SourceCertifiedOriginal29x12` carrier;
  in the other branch returns the exact species obstruction.

The canonical original certificate generator
`scripts/generate_bh4_original29x12_agda.py` is now extended
rather than duplicated. On genuine separately SHA-pinned acquired
29×12 Rhea/ChEBI bytes:

1. Its existing `check_certificate(full_panel=True)`
   validates original finite reaction/gross participants and
   CHNOP/charge equality.
2. The new `rendered_source_simplex_admission` computes
   the CHNOP sum for **each** of the 29 source-ordered
   species using exact Python integers.
3. If all counts are positive, it emits **29 literal indexed
   Agda clauses**, each
   `generatedCHNOPPositiveAt (selected Fin index)
      = (exact predecessor , refl)`.
   It also emits `generatedPositiveCHNOP` and
   `generatedPositiveSimplexAdmission`, both consuming
   `generatedSourceCertifiedOriginal29x12`. The proof
   does not rely on source labels or an asserted Boolean.
4. If any source weight is zero, it emits the **concrete**
   `generatedZeroCHNOPSpecies`,
   `generatedZeroCHNOPWeight = refl` and
   `generatedPositiveSimplexObstructed` using the
   existing no-go theorem. It explicitly does **not**
   emit a positive-simplex admission.
5. The generator's JSON receipt now records the exact
   source positivity result, zero-species indices,
   which Agda proof branch was emitted and
   `source_CHNOP_positivity_agda_kernel_checked: false`.

New test owner:
`scripts/test_generate_bh4_original29x12_simplex.py`
contains synthetic-only positive 29-index coverage, four
zero-position negative controls and rejection of invalid
atomic counts/shape. The generator also has new built-in
synthetic self-test controls. Neither test suite nor native
Agda was executed in this session.

**Exact closure:** The *generic finite decidability and
source-emission implementation* is source-written and committed.
The actual original 29-species positivity **outcome** remains
unknown until the independently byte-pinned original input is
available. Generated literal `refl` clauses must pass Agda
2.9 kernel. This does not prove the classical real-weighted
simplex compactness/Brouwer fixed point inside constructive
Bishop analysis, physical kinetic calibration, reactive
boundary work, or same-source tissue observation.

**Revised next cut:** acquire source bytes → generate and
Agda-kernel check original source + literal positivity/zero
obstruction; then bridge those exact `Nat` CHNOP invariants
to the selected real-valued 27×29 PNP state, prove
SG/mass-action conservation and map self-preservation,
and import/construct a trustworthy finite-dimensional
Brouwer theorem for the intended real foundation. Do not
replace Brouwer with an arbitrary normalized probability
law or a conditional record.


## 2026-11-10 P0.06 source-level type repair and native Energy.Core reuse

**Concrete defect fixed:** `SameSourcePaidEnergyModel` holds two fields with types themselves in `Set₁` (`SameSourceBH4PNPModel` and `OrderedEnergyCarrier`), and therefore its record must inhabit `Set₂`. The previous `Set₁` declaration could not be accepted by Agda's universe checker; it has been repaired to `record SameSourcePaidEnergyModel : Set₂`. This is a source-level universe correction, not a kernel receipt.

**Existing prior art reused:** `DASHI.Energy.Core` provides `Preorder` and `EnergySpace`; `DASHI.Analysis.DissipationPathMonotonicity` already covers ordinary zero-credit finite-path descent, so no duplicate path monotonicity infrastructure is required. `BH4PNPSameSourcePaidEnergyExact` now defines `toExistingEnergyPreorder` using the exact existing `Preorder` interface and `sameSourceEnergySpace` with the *same* `energyOf` and `PhysicalState`. `allSameSourceHistoriesDescendInExistingEnergySpace` exposes the previous nonzero-paid-residual descent conclusion directly via `DASHI.Energy.Core.EnergySpace.P`, without constructing an unrelated observation space or narrowing physical energies to Nat.

**Important prior-art seam:** `DissipationPathMonotonicity.OrderedAdditiveEnergy.zeroLower` demands `zero ≤ value` for **every** energy value. This is not automatically valid for a signed physical free-energy carrier; also the prior zero-credit theorem does not directly pay numerical residual or exterior-work credits. Reuse its existing `Preorder` and `EnergySpace` now; supply an actual scoped dissipative transition only with properly inhabited domain and zero/paid work evidence. In particular, do not assert an unconditional ordered-real instance from Bishop analysis or artificially require all original free energies nonnegative.

**Current proof status:** new owners and Golden import are source-written; the available runtime has neither Agda nor Nix, so kernel checking at the exact head remains OPEN. No physical S0.01–04, P0.05–08, or P1–P3 source gate is discharged by the abstract bridge.

**Acceptance commands:** `scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4PNPSameSourcePaidEnergyExact.agda`, `scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4PNPOrderedEnergyHistoryExact.agda`, `scripts/run_agda29_parallel_check.sh DASHI/Biology/KitzerowBH4EvidenceEverything.agda`.


## 2026-11-11 highest-alpha P1 native-route/energy source identity weld

**Source-written owner:** `DASHI/Biology/BH4PNPSameSourcePaidEnergyExact.agda` now contains `allSameSourceBH4PNPRouteAndPaidEnergy`. This composes the **existing** `BH4PNPSamePhysicalHistoryBridgeExact.physicalTrajectoryHasSourcePermittedRoute` with the exact same controlled-history BH4 projection, PNP projection and conditional energy-order certificate. The four conclusions use one selected `SameSourceBH4PNPModel.physicalRun`, not a separate toy state or an invented graph. The route type is the actual `BH4SpatialConnectivityCirculationExact.FlowPath` of source-permitted forward connections. It does not prove membranes are passable or rates measured. It adds no new evidence inhabitant.

**Verification boundary:** the source was committed and re-fetched from the BH4 branch; Agda and Nix executables are absent in the current runtime, so no exact-head kernel check was performed. Neither import presence nor absence of holes implies type acceptance. Original 29×12 source and rates, six-face work, positive physical-step proof, genuine Bishop real energy instantiation, #1471 native geometry reconciliation and empirical P2/P3 remain OPEN.

**Next actual cut:** run the Agda root in a Nix/Agda 2.9 environment, fix first type error rather than adding another abstract ledger; then instantiate `SameSourcePaidEnergyModel` against an original source-paid 27×29 chemical/SG/Poisson state with certified nonzero boundary/residual work. The existing CHNOP five-axis simplex bridge is accounting only and must not be mistaken for Brouwer compactness.


### 2026-11-11 exact-source refutation + signed-charge parser reconciliation

The existing `DASHI.Biology.Molecular.BH4OriginalCHNOPFiveAxisSimplexBridgeExact`
has two further **source-written** generic Agda lemmas:

- `decideOriginal369SourcePositiveCHNOPWithRefutation`
  consumes the existing `decideOriginal369SourcePositiveCHNOP`
  and `zeroCHNOPWeightBlocksPositiveSource`, returning
  `SourcePositiveAggregateCHNOP certificate ⊎
    (SourcePositiveAggregateCHNOP certificate → ⊥)`.
  The negative branch is a real contradiction for the SAME
  original source, not a zero-index display.
- `positiveOriginalSourceExcludesEveryZeroCoordinate`
  shows a chosen original positive witness and an exact zero
  at any `Fin 29` species cannot coexist.

This completes a **constructive decidability/refutation layer**
for every inhabited `Panel.SourceCertifiedOriginal29x12`;
it does **not** inhabit the original source certificate,
prove positivity for the missing actual source bytes,
or import a real-valued Brouwer fixed-point theorem.

The original checker `scripts/check_bh4_original_panel_spatial_events.py`
now uses the existing authoritative
`run_bh4_reaction_network._integer` for each source
participant charge rather than a secondary `int(...)`
conversion. Upstream `audit_reaction` already rejected
nonintegral source charges, so this hardening removes an
**inconsistent local coercion**, not an independently
demonstrated bypass of the upstream full-panel audit.
The canonical strict parser accepts genuine decimal integer
text such as `-2` and rejects Boolean/fractional/exponential
values. A focused negative-control test was committed to
`scripts/test_generate_bh4_original29x12_simplex.py`.

**Verification:** New code is GitHub-committed and readback
eligible. No native Agda 2.9 kernel acceptance, pytest run
or actual original byte-pinned Rhea source generation
occurred in this session. P0 original source positivity
outcome, 27×29 real concentration embedding, analytic
Poisson–SG preservation/continuity, genuine finite Brouwer,
root transfer, physical kinetics and open-boundary
laws remain OPEN.


### 2026-11-11 highest-alpha source exact rational semidiscrete accounting

**New testable cross-model bridge**:
`scripts/bh4_original_reactive_pnp_adapter.py` now defines
`original_closed_rational_semidiscrete_conservation`. It obtains
the **same** full-panel original 29×12 signed stoichiometric
matrix and 29 source formula/charge weights from
`check_certificate(full_panel=True)`, pins the original
Rhea bytes by SHA-256, and consumes 54×29 **arbitrary
signed rational** internal native-bond fluxes plus 27×12
**arbitrary rational** original reaction-rate coordinates.
It constructs all 783 entries of the selected closed
semidiscrete source RHS by exact `fractions.Fraction`:

```text
RHS_{v,s}
 = sum_{native incident bonds} ± J_{edge,s}
   + sum_{r=1}^{12} S_{s,r} rate_{v,r}.
```

Every original 54-bond term appears with opposite signs at
its two incident voxels. The separately source-checked
exact integer 29×12 left-kernel inequalities yield

```text
Σ_{v,s} C_s RHS_{v,s} = 0,
Σ_{v,s} H_s RHS_{v,s} = 0,
Σ_{v,s} N_s RHS_{v,s} = 0,
Σ_{v,s} O_s RHS_{v,s} = 0,
Σ_{v,s} P_s RHS_{v,s} = 0,
Σ_{v,s} z_s RHS_{v,s} = 0.
```

The adapter checks those six exact rational equalities and
returns the complete rational RHS, source digest and
fail-closed non-promotion flags. It rejects binary floating
inputs so a `0.5` float is not misrepresented as an
original exact rational proof term. Regression controls
`test_original_54_bond_27x29x12_exact_rational_rhs_conservation`
and `test_original_rational_continuity_rejects_binary_floats_and_bad_source`
exercise a nontrivial `1/3` bond flux and `2/7`
reaction, a corrupted source column and fractional precision
rejection. These are synthetic-only monkeypatched checks,
NOT real source acquisition.

This is substantive **exact-rational semidiscrete continuity**
and a reusable proof-algebra interface. It does not yet
give a kernel-accepted `ℚ→Bishop ℝ` embedding, prove
the transcendental real SG Bernoulli flux or original
rate laws meet all positivity/continuity hypotheses, add
physical boundary work, prove existence/uniqueness of
a real root in Agda, or validate a tissue observable.

The same pass strengthens `SourcePositiveAggregateCHNOP`
to an actual constructive yes/no proposition via
`decideOriginal369SourcePositiveCHNOPWithRefutation`
and `positiveOriginalSourceExcludesEveryZeroCoordinate`
in the already imported Agda CHNOP bridge. The checker
now reuses upstream strict `_integer` to reject source
charge coercions at both layers. These are source-written
and not Agda/pytest executed in this runtime.

**Remaining P0 critical path:** byte-pin authentic
source; check generated Agda 29-weight positivity/no-go;
embed source-certified integral left-kernel into the
selected Bishop real species and the same original
SG/mass-action field; pay finite real compactness,
self-map continuity, source-real positivity/loss bound,
Brouwer producer and fixed-point-to-root proof in the
pinned Agda kernel. **P1:** original opened six-face
boundary work and BH4/PNP/tissue same physical carrier.
**P2:** independent physical longitudinal validation,
Golden kernel and ITIR artifact provenance.


### 2026-11-11 additional original-source shape firewall

`check_bh4_original_panel_spatial_events.check_certificate`
formerly used Python `assert` for its 29×12 matrix
row/dimension preliminary checks. They have been replaced
with explicit `ValueError` rejection, plus an exact
Python-integer requirement for all signed matrix entries
(rejecting float and Bool). Those are enforced even under
`python -O`, avoiding accidental source admission without
shape/type verification. Added focused malformed row,
float coefficient and Boolean coefficient negative
controls in the original BH4/PNP adapter test owner.

This hardening does not authenticate a genuine Rhea release,
change the approved 12 finite reactions, or prove measured
PNP kinetics. It ensures the existing source proof-algebra
and new exact rational continuum-chart computation cannot
receive an unvetted original finite matrix by bypassing
ordinary Python assertions.


### 2026-11-11 original rational semidiscrete **local** maximum cut

The original-source rational bridge now exposes all 27×6=**162**
exact **per-voxel** continuity laws, not merely six globally
vanishing conserved sums. Using the same 54 original native
bonds and source-selected full 29×12 Rhea signed matrix, it
constructs separate `Fraction` matrices:

```text
divergence[v,s] = sum_{edges leaving v} J[edge,s]
                  - sum_{edges entering v} J[edge,s]
source[v,s] = sum_r S[s,r]*rate[v,r]
RHS[v,s] = source[v,s]-divergence[v,s].
```

For each original weight coordinate
`a∈{C,H,N,O,P,signed_charge}` and EACH actual site `v`:

```text
Σ_s a[s]*RHS[v,s]
 + Σ_s a[s]*divergence[v,s]
 = Σ_s a[s]*source[v,s] = 0.
```

This is **local continuity**, not a claim that local
weighted concentration remains constant when matter
flows between neighbours. Across all 27 sites,
each native bond appears once with each sign, so the
weighted divergences globally sum to zero. Combined
with the per-original-reaction exact left kernel, the
six original global inventory derivatives vanish.

The bridge returns `exact_local_weighted_divergence`,
`exact_local_weighted_reaction_source`,
`exact_local_continuity_residual`, and the count
`local_CHNOP_signed_charge_equations_checked=162`.
Its consumer convention is explicit:
`signed_native_flux_units` are **per-voxel normalized
transport rates**; physically dimensioned Scharfetter–
Gummel edge flux densities from the numerical solver
must be divided by mesh length `h` before being passed
as these semidiscrete RHS terms. The exact rational
inputs are a symbolic/algebraic chart, not proof that
arbitrary real SG values or original measured rates
have rational representations.

Source validation is further tightened: the original
checker now rejects zero/negative/fractional/Boolean
gross participant coefficients and unsupported sides
using the canonical strict integer parser before accepting
its 29×12 source identity. Focused synthetic tests check
nonzero `1/3` flux, `2/7` original reaction,
six local equations at each voxel, a reversed signed
flux on original bond 53, malformed gross coefficients,
and no promotion to physical interpretation.

**Updated cut accounting:**
- P0 exact full 27×29 rational source RHS and its
  162 local six-coordinate continuity equalities:
  implemented by direct exact `Fraction` calculation;
  regression code committed, not run at this head.
- P0 original Nat five-axis CHNOP left-kernel composition
  and decidable positivity/refutation: source-written
  Agda, kernel verification NOT obtained.
- P0 authentic source/real PNP: strict source certificate,
  29 source-positive weights, independent physical rates,
  actual original 27×29 concentration state and the
  canonical semidiscrete SG constitutive refinement
  remain unpaid.
- P0 Bishop-real / finite dimensional compact positive
  weighted simplex and a TRUSTED Brouwer fixed-point
  producer, implicit-root identity, strict positivity,
  convex free-energy dissipation: still kernel OPEN.
- P1 original reactive face work, physical tissue
  same-source/time step, and independent longitudinal
  test: still OPEN.
No continuous real theorem is inferred from
exactness of the rational source accounting alone.


### 2026-11-11 P0 exact rational-to-Bishop-real finite continuity lift

**New source-written owner:** `DASHI/Biology/Molecular/BH4RationalToBishopFiniteContinuityExact.agda` is now imported into `KitzerowBH4EvidenceEverything.agda` on existing BH4 PR #1454. It reuses the actual pinned `Real` / `RealProperties` Bishop real setoid, `BishopExponentialSeriesConvergenceExact.embed`, and rational `Data.Rational.Unnormalised` operations. The key finite results are `rationalFiniteSumEmbeds`, `weightedRowEmbeds`, `spatialWeightedEmbeds`, `original369RationalZeroDefectImpliesBishopZero`, and `original369SixRationalConservationLiftsToBishop`. Generic indexed proofs recurse on arbitrary row count; their terminal source chart is exactly `Vec (Vec ℚᵘ 29) 27` and exactly six separately supplied weights (C,H,N,O,P,z).

**Mathematical acceptance contract:** a SAME-SOURCE rational `rhs : Vec (Vec ℚᵘ 29) 27` and `weights : Vec (Vec ℚᵘ 29) 6` must be supplied, together with all six `Q._≃_ (sourceSpatialWeighted ... rhs) Q.0ℚᵘ` witnesses. Rational setoid equivalence is used rather than propositional equality of unnormalised fraction representatives. Existing Bishop `⋆-distrib-+`, `⋆-distrib-*`, `⋆-cong`, `+-cong` and `≃-trans` derive the finite Bishop real conserved sum. This is a **finite algebraic conservation transport** and not a proof the genuine real Scharfetter–Gummel flux and mass-action field is the embedding of an arbitrary rational RHS.

**Highest-alpha missing seam:** build the Agda-side source-identity-gated `Q.ℚᵘ` incarnation of the existing exact Python `Fraction` semidiscrete 54-bond / 29×12 RHS, with explicit same-order vector/source certificate and exact six rational zero-sum witnesses; then instantiate this module. The executable Python producer must not be mistaken for an Agda proof inhabitant. Real PNP RHS includes log/exp/Bernoulli transcendental values that need independent finite flux-cancellation/left-kernel proofs and operator continuity; no rational-density claim discharges those by itself.

**Kernel and physical boundary:** source-written, GitHub-readback only; no Agda 2.9 acceptance. The original byte-pinned 29×12 Rhea certificate, positive 29-weight source instance, genuine Bishop-real weighted-simplex compactness, Brouwer fixed point, positive implicit root, measured/source rates, six-face reactive work and physical BH4/PNP/tissue refinement remain OPEN. Reuse existing Bishop sum lemmas instead of introducing independent real axioms. Acceptance:
```sh
scripts/run_agda29_parallel_check.sh DASHI/Biology/Molecular/BH4RationalToBishopFiniteContinuityExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Biology/KitzerowBH4EvidenceEverything.agda
```


## 2026-11-11 highest-alpha P0 Agda rational semidiscrete operator producer

**New source-written, Golden-imported owner:** `DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact`. It constructs a fully dimension-indexed rational finite-volume RHS, not just a proposition about an arbitrarily selected RHS. Inputs:
- `Matrix 27 54` signed site-by-native-bond incidence, whose orientation must be identified with the original geometry;
- `Matrix 54 29` signed native-bond/species currents;
- `Matrix 29 12` finite stoichiometric coefficients, to be identified with the authentic original Rhea source;
- `Matrix 27 12` site-by-reaction net rates.

The `rationalDot` and `rationalColumn` functions construct the internal-bond and reaction contributions, `rational369SemidiscreteRHS` tabulates **all 783** site/species values, and `rational369SemidiscreteAt` shows lookup is definitionally the two-term finite RHS. This is an Agda source program using exact `Data.Rational.Unnormalised` arithmetic, not NumPy, float or an invented rate constant.

**Same-computed-RHS Bishop consumer:** `computedRationalRHSConservationLiftsToBishop` invokes the preceding `original369SixRationalConservationLiftsToBishop` on exactly `rational369SemidiscreteRHS inputs` and the six source-weight rows. Its premises are the **six rational zero-defect proofs** for this computed RHS. It does **not** derive those proofs from arbitrary matrix values, and it does not presume the arbitrary typed matrices are the authenticated original Rhea/incidence matrices. A 29×12 coefficient array of the right shape is not itself source provenance.

**New exact remaining lemmas (source and physical):**
- `original369NativeIncidenceRationalColumnZero`: weld the native original 54 endpoint pairs from #1471 to each of these 54 rational incidence columns with a source-verified orientation, then prove `Σ_v B_{v,e} ≃ 0`.
- `original29x12CertifiedRationalLeftKernel`: transport each original signed-Nat gross reactant/product conservation proof (CHNOP and signed charge) into `Q._≃_ (Σ_s a_{axis,s} S_{s,r}) 0` for all 12 original columns. **Authentic generated source certificate still required**.
- `original369SemidiscreteSixZeroDefects`: using finite distributivity/interchange, derive the six computed rational RHS defects from the previous two theorems for arbitrary rational bond currents/reaction rates.
- `original369SemidiscreteBishopSixZeroDefects`: instantiate `computedRationalRHSConservationLiftsToBishop` with those *derived*, same-source defects, not fabricated proofs.
- `original369RealSGMassActionMatchesConservativeOperator`: independently prove that selected real Scharfetter–Gummel currents and source-paid mass-action reaction rates satisfy the same real-valued finite operator and all source-specific boundary terms. The rational finite model is an accounting implementation only.
- The existing real weighted-simplex compactness, continuity, genuine Brouwer producer and positive original implicit-root acceptance, source-paid kinetics/open boundaries, same-physical-state tissue refinement and empirical held-out validation remain OPEN.

**Verification boundary:** new code is GitHub-committed and readback-checkable; there is no Agda/Nix executable in this runtime and no Agda kernel receipt. No original source certificate, Agda accepted rational left-kernel proof, real PNP identification or data-backed biology claim was promoted. Run `scripts/run_agda29_parallel_check.sh DASHI/Biology/Molecular/BH4OriginalRationalSemidiscreteOperatorExact.agda` and then the existing BH4 Golden root in the actual Nix/Agda environment. Source-written definitions are not typechecking receipts.


**2026-11-11 symbolic-index proof repair:** `rational369SemidiscreteAt` no longer attempts to close both symbolic `Vec.lookup (Vec.tabulate ...)` reductions by bare `refl`. New `lookupTabulateExact` proves lookup/tabulate correspondence by Fin induction, and the RHS coordinate proof explicitly composes two such equalities using `cong` and `trans`. This addresses a specific likely Agda elaboration defect; it is still source-written and requires kernel execution. The operator's exact 27×29 dimension and missing original-geometry/source proofs are unchanged.


### 2026-11-11 producer-side 54-bond + rational rate algebra and same-source generated Agda CHNOP/z column proof

The **existing** original operator owner
`DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact`
was found in the current PR branch, already Golden-imported:
it defines typed rational matrices
`orientedNativeIncidence : Matrix 27 54`,
`signedNativeBondFluxes : Matrix 54 29`,
`originalFiniteStoichiometry : Matrix 29 12`,
`originalFiniteReactionRates : Matrix 27 12`, and computes
`rational369SemidiscreteRHS : Matrix 27 29`.
Its consumer theorem currently **assumes** six rational global
zero-defect proofs. Do not duplicate that 783-coordinate operator.

New **proof-source** owners, imported into
`KitzerowBH4EvidenceEverything`:

1. `BH4RationalNativeBondCancellationExact` proves
   `pairedSpeciesContributionCancels`,
   `pairedBondWeightedSumCancels`,
   `pairedNativeBondCollectionCancels`,
   `original54x29PairedNativeFluxCancels`, and
   `original54x29PairedNativeFluxBishopZero`.
   For any 29 rational weights and 54×29 rational signed
   fluxes, the opposite endpoint contributions cancel
   as rational equivalence and under the existing Bishop
   embedding. The proof does not yet identify the paired
   expression with the actual 27×54 incidence matrix.
2. `BH4RationalRateWeightedSourceConservationExact`
   proves `rationalAllColumnsRateBalanced` and
   `rationalAllSitesRateBalanced`; for *any* 27×12
   rational rate field, source-column rational weighted
   balance suffices for the exact reaction totals to
   balance. It specializes to
   `original369x29x12RationalRatesPreserveKernel`
   and its Bishop-real image.
3. `BH4RationalNativeSourceCompositionExact` combines
   these same 54×29 fluxes, 27×12 rates and 12×29 gross
   reaction sides for each of the same **six** supplied
   source-weight vectors. Its one/six-axis rational and
   Bishop theorem need only **columnwise** rational
   balance—not an already-given global zero-defect
   hypothesis.

The **existing SHA-256 pinned original Rhea source generator**
`scripts/generate_bh4_original29x12_agda.py` has been
extended: it now emits
`generatedRationalReactants`,
`generatedRationalProducts` and
`generatedRationalAxes` **as Agda expressions of the SAME**
`generatedColumns`, `generatedElementWeights`, and
signed `generatedPositiveCharges / generatedNegativeCharges`.
It never separately hand-codes another 29×12 matrix.
It additionally emits all 72 closed, original-source
`generatedRationalColumnsBalance` cases
(6 coordinates × 12 columns) as rational setoid
`QP.≃-reflexive refl` proof candidates, plus
`generatedOriginalSixAxisRationalProducer` and
`generatedOriginalSixAxisBishopProducer` for arbitrary
27×12 rational rates and 54×29 rational flux fields.
**None is an original measured flux/rate.**

The generator's receipt exposes
`source_rational_column_balance_proof_clauses_emitted=72`,
`source_rational_producer_definitionally_uses_generated_Nat_columns=true`
and
`source_rational_producer_agda_kernel_checked=false`.
Synthetic-only test owner
`scripts/test_generate_bh4_original29x12_simplex.py`
now checks 72 distinct clauses, exact source Nat dependency,
correct six axes and arbitrary rate/flux dimensions, rejection
of missing source fields, and both rational/Bishop output paths.

**Highest-alpha remaining exact chain** (none implicitly
discharged by the new algebra):

P0.A: obtain independent authentic Rhea full-panel bytes,
pin SHA256, generate the 29×12 original Nat + rational
owner and **Agda 2.9 kernel-check** the 72 `refl` cases
and all three new Agda module transitive imports.
A source-written term is not an accepted proof.

P0.B: prove that the current `Matrix 27 54`
`orientedNativeIncidence` in
`BH4OriginalRationalSemidiscreteOperatorExact`
is exactly the original native geometric 54-bond
endpoint incidence and that its 783-coordinate RHS's
six weighted global sums agree (under rational setoid
equivalence) with the now-derived paired native/source
sums. This is the decisive
`original369RationalRHSFromSameSourceProducer`
left unresolved. **Do not** substitute paired
cancellation for the actual 27×54 identification.

P0.C: use P0.B to supply the **computed**
`rational369SemidiscreteRHS inputs` six zero-defect
proofs *without* taking them as unrelated input
fields; consume the already-present
`computedRationalRHSConservationLiftsToBishop`.

P0.D: identify the genuine original Bishop-real
Scharfetter–Gummel + detailed-balanced mass-action
operator as the source-selected 27×29 semidiscrete
operator, pay weighted simplex compactness,
continuity, a genuine Brouwer fixed-point producer,
strict-positive implicit root and free-energy theorem
in Agda. Source-selected open boundary, original
kinetic parameters, tissue same-state observation and
empirical/ITIR validation remain further P1/P2 gates.

Verification in this session: GitHub commits and
readbacks of source files; **no local Agda, Nix or
repository pytest execution**. Generated source is
absent until actual original bytes are supplied.


### 2026-11-11 follow-on P0: literal native 27×54 incidence and same-source 783-coordinate rational RHS

The source-writing continuation located and reused
`DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact`
(the existing 27×54/54×29/29×12/27×12 typed matrix operator).
The prior P0 producer composition did not yet inhabit that
specific `Rational369SemidiscreteInputs` record.

**New original-native finite geometry owner**
`DASHI.Biology.Molecular.BH4OriginalNative369IncidenceExact`
now provides:

- `sourceNative54Endpoints`: the exact 54 oriented
  native bonds of the selected 3×3×3 lexicographic 27-cell
  chart, with the same ordering as
  `scripts/reactive_pnp_369.py`.
- `sourceIncidenceCoefficient`: −1 at each bond's
  outgoing site, +1 at its target, zero at every
  other original site, all in unnormalised rational
  form.
- `sourceNativeIncidence : Operator.Matrix 27 54`.
- `sourceNativeColumnZero`: 54 enumerated, closed
  `QP.≃-reflexive refl` proof candidates that each
  native incidence column sums to zero at all 27 sites.
- `originalNativeRationalInputs`: constructs the
  pre-existing typed original RHS input from that
  selected incidence and arbitrary provided 54×29
  flux, 29×12 stoichiometric and 27×12 rate matrices.

Independent exact-integer Python execution outside
the checkout confirms 27 sites, 54 distinct oriented
bonds, one +1/−1 per bond, all 54 zero column sums,
and the selected first/last endpoint order. This is
**not** an Agda kernel receipt and not an authenticated
tissue compartment topology.

The existing SHA-pinned original Rhea generator now
also emits `generatedRationalStoichiometry : Matrix 29 12`
by **definitionally subtracting** its own
`generatedRationalReactants` from its own
`generatedRationalProducts`; it is not a second
handwritten matrix. It emits:

- `generatedOriginalRationalInputs`: combines
  source-derived stoichiometry with the native
  incidence and arbitrary source-indexed rational
  fluxes/rates;
- `generatedOriginalRationalRHS`: directly calls
  `Operator.rational369SemidiscreteRHS`, producing
  all original 783 coordinate entries;
- `generatedOriginalRationalRHSAt`: reuses
  `Operator.rational369SemidiscreteAt` to identify
  each selected RHS coordinate with its actual
  signed bond and original reaction contribution.

This is a **new typed source/geometry constructor**
on the intended RHS owner, distinct from and stronger
than a detached six-axis accounting receipt.

**Critical last P0 finite-seam obligation:** establish
`originalComputedRHSWeightedSumAgreesWithPairedSource`
as a genuine rational setoid theorem. It must
prove that the six global
`Lift.sourceSpatialWeighted sourceAxes
  (Operator.rational369SemidiscreteRHS inputs)`
are equal to the corresponding paired-native-bond
plus gross-source net expression already controlled
by `BH4RationalNativeSourceCompositionExact`.
The proof requires finite-sum linearity/Fubini
across 27 sites, 29 species, 54 edges, 12 columns,
and source incidence signs. The already-committed
54 zero-column witnesses and 72 source-column
rational balance clauses are precisely its
preconditions; **they are not by themselves
the RHS zero-defect proof**.

Then invoke the existing
`computedRationalRHSConservationLiftsToBishop`
with **derived** six zero-defect witnesses, rather
than assuming global conservation. Beyond that
remain original physical Rhea source bytes,
Agda 2.9 kernel acceptance, actual Bishop-real
SG/mass-action correspondence, compact conserved
simplex, Brouwer, strictly positive implicit root,
closed free-energy proof, source-paid reactive
boundary work, same-state tissue observer and
independent empirical/ITIR validation.

All source modules and generator tests are GitHub
committed/readback; **no native repo pytest or
Agda typechecking** was executed here. The
generated original source module still requires
authentic separately byte-pinned input.


### 2026-11-11 native incidence exact-owner regression

Added `scripts/test_bh4_original_native369_incidence.py`.
It parses the **actual Agda term** `sourceNative54Endpoints`
as a strict recursive grammar of `V._∷_`,
`F.zero`, `F.suc`, and endpoint pairs,
then compares all 54 decoded `Fin 27` pairs
against the pre-existing numerical PNP
`reactive_pnp_369.BONDS` ordering.
The test checks 27 source points, all 54
distinct nearest-neighbour bonds and
rejects missing/duplicated source declarations
or an incorrectly reversed endpoint list.
This is a source-identity regression, NOT
a proof of a measured tissue adjacency,
an Agda kernel receipt or an empirical
kinetic calibration. The new repository
pytest was not executed in this session.


### 2026-11-11 P0 finite weighted bilinearity of the computed 27×29 RHS

**New assistant-authored proof source on #1454:** `DASHI.Biology.Molecular.BH4RationalSemidiscreteBilinearityExact`, Golden-imported. This owner adds finite rational `rationalZipAdd`, `rationalWeightedAdditive`, `rationalSpatialZipAdd`, `original369SpatialWeightedAdditive`, `original369RHSIsBondPlusReaction`, and `original369ComputedRHSWeightedSplit`. It uses existing `Lift.sourceWeightedRow`, `Lift.sourceSpatialWeighted`, and the **actual** `Operator.rational369SemidiscreteRHS`, with rational setoid equivalence. Inductive proofs use the repository's existing `NonReflectiveQ` solver for finite ring distributivity and reassociation.

**Achieved source-level statement:** for any typed rational 27×54 incidence, 54×29 currents, 29×12 signed stoichiometry, 27×12 rates and 29 rational weights, the weighted spatial sum of the computed full 783-coordinate RHS splits into the spatial weighted **bond contribution plus reaction contribution**. No six global zero-defect premise is required for this algebraic split. This moves from two separate synthetic-free source producers toward the missing RHS-to-paired-source identity, but does not prove the requisite finite 27/54/29/12 Fubini interchange, original source incidence equality or gross-column rational source match.

**Exact remaining equality:** identify the split bond sum with `Native.pairedNativeBondCollection weights fluxes` (zero for arbitrary original signed flux) and the split signed reaction sum with `Rates.spatialRateWeightedTotal weights products rates - Rates.spatialRateWeightedTotal weights reactants rates`, using the source-generated original stoichiometry and rational finite interchange. Then the existing 54 native column and 72 original reaction-column witnesses produce the actual computed six zero defects for `Operator.rational369SemidiscreteRHS`. Only after that may the `computedRationalRHSConservationLiftsToBishop` consumer be instantiated without an independent conservation premise.

**Verification:** GitHub source/Golden commits are not Agda 2.9 kernel receipts; local runtime lacks Agda/Nix and the original source certificate is not authenticated. Real SG/mass-action, Poisson, open electrode work, weighted-simplex/Brouwer, physical same-source step, tissue and independent empirical validation remain OPEN. Run:
```sh
scripts/run_agda29_parallel_check.sh DASHI/Biology/Molecular/BH4RationalSemidiscreteBilinearityExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Biology/KitzerowBH4EvidenceEverything.agda
```


### 2026-11-11 P0 exact unnormalised-rational finite and weighted Fubini

Added `DASHI.Biology.Molecular.BH4RationalFiniteFubiniExact.agda`
to the existing BH4 Golden import tree. This is a reusable
finite-algebraic lemma donor **in the identical ℚᵘ setoid**
as `BH4OriginalRationalSemidiscreteOperatorExact` and
`BH4RationalToBishopFiniteContinuityExact`:

- `qFiniteSum`, `qFiniteSumCong`,
  `qSumZipAdd`, `qSumReplicateZero`.
- `qColumnTotals`: fold arbitrary finite site/species
  rational matrices columnwise using actual `Q._+_`.
- `qFiniteFubini`, `original27x29RationalFubini`:
  transpose finite double sums without creating a new
  physical state or changing rational equality to
  propositional equality.
- `qMulZero`, `qMulDistributes`,
  `qWeightedRowAdd`, `qWeightedZeroRow`.
- `qWeightedFiniteFubini`,
  `original27x29WeightedFubini`: for arbitrary original
  29-vectors `weights` and arbitrary 27×29 rational
  rows, prove equality (under ℚᵘ rational equivalence)
  of the canonical original `Lift.sourceSpatialWeighted`
  and the same weighted row applied after columnwise
  27-site totals.
- `qWeightedDotCong`,
  `qWeightedColumnZeroImpliesSpatialZero`:
  a derived weighted-global-zero theorem from a
  **per-species 27-site zero proof**, not from a
  six-axis arbitrary global-zero certificate.

The important exact *remaining* P0 dependency is to
prove for each original species, using the actual
`sourceNativeIncidence : Matrix 27 54`,
that the 27-site total of the selected operator's
**transport** sub-RHS is zero, while the original
29×12 reaction sub-RHS has zero in each of the six
weighted coordinates from the generated source
72 column cases and arbitrary 27×12 rational rates.
Then use weighted row splitting and these finite
Fubini identities to derive all six
`Lift.sourceSpatialWeighted ... computedRHS ≃ 0`
without any global conservation input.

This finite algebra construction does not imply
Bishop-real SG constitutive identity, actual
biological rate calibration, compactness, Brouwer
or source-paid tissue boundary conditions.
**New Agda source is committed, not kernel checked**;
the current container has no `agda` or `nix`
executable.


### 2026-11-11 P0 six computed RHS defects derived from separately source-paid local owners

**New assistant-authored Agda owner:** `DASHI.Biology.Molecular.BH4ComputedRationalSixDefectCompositionExact`, imported by the original BH4 Golden root. This is a **consequence theorem for the actual** `Operator.rational369SemidiscreteRHS inputs` rather than a constructor that assumes six global conservation defects.

**Exact source split:** `OriginalSourceLocalConservation inputs weights` requires *only* (i) a proof that the native transport-only 27-site column total vanishes for each of 29 species, and (ii) proof that the reaction-only 27×29 RHS weighted sum vanishes for each of the six original CHNOP/charge axes. Both refer to the SAME `Rational369SemidiscreteInputs` and `Matrix 6 29` owner. `originalComputedRHSSixZeroDefects` composes the new source-written `Linear.original369ComputedRHSWeightedSplit` and the pre-existing current-head `Fubini.qWeightedColumnZeroImpliesSpatialZero` to **derive all six rational zero defects**. `originalComputedRHSSixBishopConservation` immediately invokes `Operator.computedRationalRHSConservationLiftsToBishop` with those derived witnesses; no global zero-defect proof is admitted independently.

**Do not overpromote:** the record is an explicit uninhabited obligation until actual original 54-column incidence cancellation and 29×12 signed source-kernel theorems are transferred to the specific transport/reaction `Operator` terms. It cannot be filled with fake zero matrices or unknown measured rates. The finite Fubini and source column cancellation donors already exist on this fast-moving branch; their same-expression weld remains **OPEN**. Neither this structural proof nor prior donor source has an Agda 2.9 kernel receipt. The byte-pinned Rhea generated source and real SG/mass-action physics remain separately OPEN.

**Exact next maximum cut:** discharge the two *local* receipt fields from (a) `Native.sourceNativeIncidence` with `Native.sourceNativeColumnZero`, transporting arbitrary rational native flux columns across finite sums; (b) generated original 12-column gross reactant/product source kernel, proving arbitrary 27-site rational reaction RHS weighted zero with correct subtraction signs. Then construct a single genuine `OriginalSourceLocalConservation` inhabitant for the generated source. Real ordered PNP, Brouwer, boundary work, tissue and empirical validation remain independent.

**Verification:** committed source + root source readback; no Agda/Nix at runtime. Exact-head:
```sh
scripts/run_agda29_parallel_check.sh DASHI/Biology/Molecular/BH4ComputedRationalSixDefectCompositionExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Biology/KitzerowBH4EvidenceEverything.agda
```


### 2026-11-11 P0 computed 783-coordinate RHS decomposition: local producer instead of six assumed global zeros

The **existing** original semidiscrete operator
`BH4OriginalRationalSemidiscreteOperatorExact` was
retained unchanged as the authority for
`rational369SemidiscreteRHS : Matrix 27 29`.
Two new source-written Agda owners are now imported
under the existing BH4 Golden root:

**1. `BH4RationalFiniteFubiniExact.agda`**:
- generic `ℚᵘ` row-sum congruence, addition,
  zero-vector identity and finite matrix Fubini;
- generic source-row weighted addition and
  `qWeightedFiniteFubini`;
- `original27x29WeightedFubini`, identifying the
  exact same `Lift.sourceSpatialWeighted` with
  weighted 27-site column totals;
- `qWeightedColumnZeroImpliesSpatialZero`,
  making **29 per-species 27-site zero witnesses**
  sufficient for *any* rational weight vector,
  rather than postulating six global weighted zeros.

**2. `BH4OriginalComputedRationalRHSSplitExact.agda`**:
- `originalBondRows` and `originalReactionRows`
  use the same original operator's own
  `bondContribution` and `reactionContribution`;
- `originalBondAt`, `originalReactionAt`,
  `lookupZipWith`, `lookupMatrixAddAt`,
  `originalRHSSplitLookup` explicitly respect
  SYMBOLIC `Fin 27` and `Fin 29` indices.
  A first tempting `refl` shortcut was rejected
  because `lookup (tabulate f) i` need not
  definitionally reduce for an arbitrary symbolic
  `i`; the source now uses the original
  `Operator.lookupTabulateExact` proof and
  explicit `zipWith` lookup induction.
- `qSpatialWeightedCong` and
  `qSpatialWeightedAdd` prove weighted
  sum congruence and RHS splitting.
- `originalComputedRHSWeightedSplits` proves
  the canonical original 27×29 RHS's spatial
  weighted sum equals the sum of its transport
  and reaction weighted totals.
- `originalComputedSixAxisZeroFromLocal`
  derives the six source-axis rational
  global zero defects from exactly two
  **local structural inputs**:
  (a) one transport zero over all 27 sites
  for EACH of the 29 species,
  (b) one weighted reaction source zero
  for EACH of six original CHNOP/z axes.
  No arbitrary six-global-zero hypothesis
  occurs in this theorem.
- `originalComputedSixAxisBishopFromLocal`
  immediately consumes the derived zeros in
  the **already-existing**
  `Operator.computedRationalRHSConservationLiftsToBishop`.

The new owners are proof SOURCE, not Agda
typechecking receipts. They do **not**
manufacture original Rhea 29×12 source bytes,
measured fluxes/rates or original tissue calibration.

**Remaining exact P0 algebraic cut (now narrower):**
(1) prove for each of 29 species, on the
literal `sourceNativeIncidence` 27×54 matrix,
that its transport-only original
`qColumnTotals (originalBondRows inputs)`
is zero, by using the previously emitted
54 `sourceNativeColumnZero` witnesses
and rational finite weighted Fubini;
(2) prove each of six original CHNOP/z
weights annihilates the 27-site
`originalReactionRows`, using the 72
generated source 12-column rational
balance cases and arbitrary 27×12 rates;
(3) instantiate `originalComputedSixAxisBishopFromLocal`
with *these derived, same-source* witnesses
to obtain the actual computed 783-coordinate
Bishop continuity theorem without supplying
a global conservation receipt.
Source generation and Agda 2.9 acceptance
must precede any claim of physical source
certification.

**P0 real/analytic then remains:** genuine
Bishop-real SG/mass-action operator
identification; compact conserved positive
simplex, true fixed-point theorem, positive
implicit root and free-energy inequality.
**P1/P2:** original six-face boundary work,
BH4/PNP/tissue same-object refinement,
original kinetic evidence, longitudinal
validation and Golden/ITIR promotion.
