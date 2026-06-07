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

Physics-adapter consumers outside the quantum-only view should cite
`DASHI.Constants.Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt`.
It links exact physics/metrology reference inputs, measured CODATA/PDG authority
inputs, the populated physics law targets, Gate 3/Clay route targets, and the
repo physics adapter owner surfaces for Maxwell/gauge, GR, Standard Model,
Gate 3, Navier-Stokes, and Yang-Mills. Its positive promotion is only
`boundedPhysicsTargetsPopulated=true`. Maxwell field equations, GR field
equations, Standard Model promotion, Gate 3 closure, Navier-Stokes Clay,
Yang-Mills Clay, and known-physics translation completion remain false.

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

Chemistry-facing consumers should cite
`DASHI.Constants.Registry.canonicalChemistryKnownInputsReferenceReceipt`. It
links exact chemistry reference inputs `N_A`, `k_B`, `R`, `e`, `F`, `h`,
`hbar`, and `c`; measured authority inputs for `alpha`, `m_e`, `m_p`,
`epsilon_0`, spectra, thermochemistry, `pKa`, rates, diffusion, binding, and
activity data; and the local chemistry/DNA/supervoxel owner surfaces. Its
positive promotion is only `localDefinitionalChemistryPopulated=true`.
Physical chemistry, spectroscopy, bonding interpretation, and wet-lab
validation remain false.

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

Empirical and runtime consumers should cite
`DASHI.Constants.Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt`.
It links provider/source/projection/comparison targets, HEPData/provider
authority inputs, PNF/ITIR runtime receipt inputs, and repo empirical/runtime
owner surfaces. Its positive promotion is only
`receiptInfrastructurePopulated=true`. Accepted provider authority,
comparison-law promotion, covariance/calibration, holdout validation, runtime
replay authority, semantic adequacy, and empirical adequacy remain false.

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
