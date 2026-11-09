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
