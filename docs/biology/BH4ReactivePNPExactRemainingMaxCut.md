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
