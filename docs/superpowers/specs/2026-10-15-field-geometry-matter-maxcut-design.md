# Field–Geometry–Matter Max-Cut Design

Date: 2026-10-15
Status: design specification pending user review before implementation planning
Scope: DASHI physics programme integrating quantum materials, programmable thermodynamics, fusion/reactor physics, propulsion/MHD, extreme-material qualification, exotic stress-energy, anomalous-force discrimination, and causal transport/FTL consumers.

## 1. Intent

The programme goal is to compile controllable physical structure into observable behaviour while preserving exact evidence, same-object identity, mechanism, authority and promotion boundaries.

The common scientific spine is:

matter / geometry / topology / fields
→ Hamiltonian / constitutive law / stress-energy
→ state
→ entropy / stress / momentum / transport
→ device observable
→ calibrated experiment
→ residual / competing explanation
→ inverse design / next experiment.

The programme must support ambitious hypotheses without allowing analogy, simulation, company claims, fiction, historical association, or cross-domain mathematical similarity to manufacture empirical authority.

## 2. Non-goals

This tranche must not:

1. create a giant universal `PhysicalSystem` record duplicating existing domain owners;
2. identify twistronics, magnetocalorics, fusion plasma, hypersonic MHD, chemical rockets, superconductors, gravity and warp metrics as the same mechanism;
3. promote mathematical exotic matter to laboratory exotic matter;
4. promote effective negative mass to gravitational negative mass;
5. promote quantum teleportation, quantum-energy teleportation or analogue spacetime to FTL signalling or matter transport;
6. promote missing-scientist technical relevance to targeting, suppression, collaboration or cause of death;
7. transfer empirical values across systems merely because theorem shape is reusable;
8. claim kernel-green status, physical validation or novelty without a corresponding receipt.

## 3. Existing repo machinery to reuse

The implementation must reuse the existing generic reduction/refinement and evidence machinery rather than replacing it. Relevant owners include:

- `DASHI.Core.ReopenableConsumerInterventionKernelExact`
- `DASHI.Core.ConsumerDescentMinimalObserverExact`
- `DASHI.Core.ConsumerObserverJoinResidualExact`
- `DASHI.Core.ConsumerGuidedReopenableRefinementExact`
- `DASHI.Core.KernelConsumerDescentFactorisationCrosswalkExact`
- `DASHI.Core.ConsumerRelativeReductionCanonicalBridgeExact`
- `DASHI.Reasoning.TypedHyperfabricConsumerReductionBridgeExact`
- `DASHI.Physics.Laws.PhysicalLawAtlas`
- `DASHI.Promotion.ClassicalFieldObligations`
- existing GR stress-energy / W4 closure interfaces;
- existing quantum-vacuum/Casimir stack;
- existing GR energy-condition shell owners;
- existing twistronics/flat-band/QTM-related owners;
- existing MAGNOTHERM magnetocaloric vertical slice;
- existing fusion-propulsion/FRC max-cut;
- existing Rocketdyne qualification/survivability max-cut;
- existing exotic-gravity/Ning-Li and missing-scientists promotion firewalls.

The new layer is therefore a thin cross-domain conservation/control composition surface.

## 4. Attribution and authority rules

### 4.1 Source-bounded payment

External sources may pay only the facts they directly establish: measured values, source-described apparatus, source-described theory, source-described simulations, or explicitly identified claims.

### 4.2 DASHI synthesis ownership

Cross-domain theorem shapes, consumer reductions, conserved-ledger composition, inverse-design architecture and promotion grammar are DASHI constructions unless a specific external source actually establishes the same result.

### 4.3 Typed evidence classes

At minimum distinguish:

- measured observation;
- calibrated measurement;
- simulation-to-experiment comparison;
- analytic/theoretical result;
- fitted model;
- planned measurement;
- company/vendor claim;
- historical narrative/source claim;
- speculative consumer;
- repository theorem.

Only evidence classes explicitly accepted by a consumer may pay that consumer.

### 4.4 Cross-pollination boundary

Cross-pollination may transfer mathematical form, experimental-design grammar, observer/refinement structure or proof pattern. It must not silently transfer:

- physical mechanism;
- material identity;
- empirical parameter values;
- calibration;
- causal attribution;
- engineering qualification;
- gravitational interpretation;
- historical intent/motive.

## 5. Core architectural choice

Use a conservation/factorisation spine rather than a universal physical ontology.

Each domain keeps its native state and equations. New generic records express only what is shared across consumers.

Conceptual transition:

`X_t --u_t--> X_(t+Δt)`

with optional same-object observations of relevant quantities:

- energy;
- momentum;
- entropy;
- charge/current;
- boundary flux;
- stress-energy;
- force/torque;
- work/heat.

Proposed owners:

### 5.1 `DASHI.Physics.Foundations.SameObjectConservationLedgerExact`

Responsibilities:

- type same-object intervals and apparatus identity;
- represent admitted channels, boundary fluxes and source terms;
- keep energy, momentum, entropy and charge ledgers separate;
- define residuals only relative to an explicit admitted-channel set;
- prove bookkeeping identities for finite exact fixtures;
- expose refinement hooks into `ConsumerDescent` when a coarse observer erases a consumer-relevant channel.

It must not assert that a domain obeys a conservation law automatically. Domain adapters supply the physical law and identification receipts.

### 5.2 `DASHI.Physics.Foundations.PhysicalResidualPromotionExact`

Responsibilities:

- separate nonzero measured residual from anomalous-physics promotion;
- type nuisance-channel completeness status;
- require repetition/scaling/apparatus-change/independent-replication evidence for stronger promotion classes;
- forbid direct `residual -> antigravity`, `residual -> reactionless`, or `residual -> new physics` constructors.

### 5.3 `DASHI.Physics.Foundations.ControlledPhysicalTransitionExact`

Responsibilities:

- type control coordinates independently of state variables;
- permit domain-specific controls such as twist, strain, magnetic field, gate field, plasma coil currents, flow actuation and boundary conditions;
- support path/cycle consumers without claiming reversibility or equilibrium.

## 6. First implementation tranche: four concrete consumers

The first code tranche must instantiate four physically different consumers because together they test whether the generic layer is truly mechanism-neutral.

### 6.1 MATBG / quantum-material consumer

Goal:

literal geometry/symmetry/Hamiltonian state → spectral / degeneracy / entropy observations.

The adapter must not duplicate the MATBG owner. It should consume existing or planned MATBG outputs and connect only the relevant energy/state/entropy/control coordinates.

Required boundaries:

- valley/C3 analogy is not physical identification until the literal representation theorem exists;
- band similarity is not mechanism identity;
- quantum geometry is not by itself a caloric cycle;
- entropy measurement is not direct proof of a practical refrigerator.

### 6.2 MAGNOTHERM / programmable-thermodynamics consumer

Goal:

field/material state → entropy/work/heat accounting over a cycle.

The existing magnetocaloric vertical remains authoritative for its own device/material facts. The generic consumer only exposes control-path, entropy, work, loss and cycle accounting.

Future generalisation may admit magnetocaloric, electrocaloric, elastocaloric, barocaloric and geometry/moiré-caloric candidates as distinct inhabitants.

### 6.3 FRC / magnetic-nozzle / hypersonic-MHD consumer

Goal:

field/plasma state → electromagnetic body force / field work / boundary momentum flux → thrust or flow-control observable.

Shared physically meaningful intermediate:

`f_EM = rho_e E + J × B`

but domain adapters must preserve the distinction between:

- confined fusion plasma;
- magnetic nozzle exhaust;
- partially ionised hypersonic external/internal flow;
- conventional electromagnetic actuation.

No common body-force form may create common mechanism or common engineering efficiency.

### 6.4 Precision thrust / exotic-gravity consumer

Goal:

measured force/displacement → ordinary-accounting residual → promotion boundary.

The nuisance fibre must be able to include at least:

- thermal expansion/strain;
- pressure/buoyancy;
- outgassing;
- vibration;
- supports/cables;
- electrostatic coupling;
- magnetic/Lorentz coupling;
- radiation pressure;
- convection;
- facility coupling;
- sensor drift.

A surviving residual creates only an anomalous-momentum candidate. Gravity modification requires an independent gravity/metric consumer.

## 7. Rocketdyne qualification transfer

Rocketdyne is a reusable experimental-design and qualification grammar, not a universal materials mechanism.

Reusable shape:

`environment × material/coating × process history × geometry/load × exposure × inspection -> outcome -> qualification`.

This grammar may guide:

- rocket hot sections;
- fusion first walls/plasma-facing components;
- HTS/cryogenic coils;
- hypersonic leading edges;
- caloric regenerators.

Historical Rocketdyne values, failure causes and qualification decisions must not transfer numerically or causally into these consumers without same-object evidence.

## 8. Fusion reactor design vertical

Fusion reactor design remains a first-class programme rather than a propulsion appendix.

Required state chain:

fuel → formation → confinement → heating → stability → burn → product distribution → extraction → materials → engineering Q.

The existing FRC propulsion max-cut already carries time-dependent formation, coupled circuit/kinetic state, validation coordinates, instability/root-pole structure, D-He3/p-B11 burn carriers, nozzle obligations and vehicle closure. The new programme must compose with these owners rather than reimplement them.

Required explicit separations:

- `Q_plasma` vs `Q_engineering`;
- measured fusion performance vs planned target;
- company claim vs calibration;
- charged-product distribution vs solved direct-conversion/nozzle performance;
- confinement architecture vs propulsion architecture.

Future comparison consumers should support FRC, tokamak, stellarator and other architectures on common engineering metrics without erasing architecture-specific physics.

## 9. Quantum stress-energy engineering bridge

The repo already contains substantial Casimir and GR energy-condition machinery, so this phase is a bridge, not a restart.

Proposed owner:

`DASHI.Physics.Foundations.QuantumStressEnergyEngineeringBridgeExact`

Responsibilities:

1. distinguish experimentally supported Casimir-force/configuration facts from model-derived renormalized stress-energy;
2. type candidate quantum states/boundary conditions producing sub-vacuum or negative local expectation values;
3. connect a source-backed or theorem-backed `<T_mu_nu>_ren` object to existing GR stress-energy interfaces;
4. evaluate classical energy-condition status separately from quantum admissibility;
5. keep quantum-energy-inequality / averaged-condition obligations explicit;
6. compute or expose the GR backreaction/metric-perturbation consumer without implying engineering significance.

Promotion ladder:

mathematical exotic `T_mu_nu`
→ QFT-realizable expectation value
→ quantum-inequality/averaged-condition admissible
→ experimentally producible configuration
→ controllably shaped/maintained
→ gravitationally significant
→ warp/wormhole capable.

No constructor may skip stages.

Initial flagship is deliberately modest:

measured/source-backed Casimir configuration
→ attributed renormalized stress-energy model
→ GR-predicted metric perturbation / magnitude bound.

## 10. Exotic stress-energy and gravity atlas

The exotic-matter layer must classify rather than promote.

Objects may include:

- ordinary classical matter;
- quantum negative-energy/sub-vacuum states;
- phantom scalar models;
- effective negative-mass media;
- negative-index/metamaterial analogues;
- superconducting/analogue-gravity correspondences;
- wormhole-supporting model sources;
- warp-metric source requirements;
- modified-gravity source objects.

Mandatory firewall:

`effective negative mass != negative gravitational mass`.

Mandatory distinction:

`energy-condition violation != unphysical` and `energy-condition violation != engineering realizability`.

Energy-condition assumptions are recorded as assumptions/tests, not universal axioms.

## 11. Causal transport / FTL hierarchy

FTL is a terminal consumer hierarchy, not an assumption.

Proposed owner family:

- `SuperluminalityObserverBoundaryExact`
- `QuantumTeleportationCausalityBoundaryExact`
- `AnalogueSpacetimeNonPromotionExact`
- `WarpMetricStressEnergyObligationsExact`
- `TraversableWormholeEngineeringObligationsExact`
- `CausalSuperluminalTransportPromotionExact`

### 11.1 FTL-0: apparent superluminality

Distinguish:

- phase velocity;
- group velocity;
- pulse peak reshaping;
- tunnelling/interference times;
- signal/front velocity.

No `v_peak > c -> FTL signalling` constructor.

### 11.2 FTL-1: quantum teleportation

Distinguish:

- state teleportation;
- gate teleportation;
- quantum-energy teleportation;
- carrier/matter transport;
- causal signalling.

Classical-communication dependence remains explicit.

### 11.3 FTL-2: analogue/effective spacetime

Analogue horizons, metamaterials, superconducting/spacetime correspondences, synthetic dimensions and quantum simulations may model mathematical structures but cannot promote to literal spacetime engineering without independent spacetime observables.

### 11.4 FTL-3: traversable wormholes

A candidate must carry at least:

- literal metric/topology;
- throat/traversability conditions;
- stress-energy source;
- energy-condition and quantum-admissibility status;
- tidal constraints;
- stability/backreaction;
- causal/chronology status.

### 11.5 FTL-4: warp metrics

A candidate must carry ADM/metric data sufficient to derive:

- required stress-energy;
- local/averaged energy-condition status;
- horizons;
- tidal fields;
- stability/backreaction;
- chronology/closed-timelike-curve exposure.

Subluminal warp-like geometries must remain distinct from superluminal transport.

### 11.6 FTL-5: causal superluminal transport

The strongest promotion requires:

- controllable information or matter transport between spacelike-separated endpoints;
- independent light-cone/clock/endpoint timing evidence;
- metric/causal-structure receipt;
- source/stress-energy receipt if metric engineering is claimed;
- chronology status;
- replication.

The type name should express the stronger target: `CausalSuperluminalTransport`, not merely `FasterThanLightTransport`.

## 12. Sci-fi as consumer generator

Science fiction may generate candidate consumers, never evidence.

Typed consumer mappings:

- replicator → atomics/chemistry/reaction/inverse-design compiler;
- transporter → state acquisition + encoding + causal transmission + matter reconstruction;
- tractor beam → field stress tensor + boundary momentum flux;
- force field → controlled EM/plasma/material boundary response;
- inertial damper → conventional acceleration/load redistribution first, modified inertia only after residual;
- artificial gravity → rotation/acceleration first, literal metric engineering as stronger consumer;
- holodeck → wave-field inverse design + haptics + programmable matter;
- self-healing spacecraft → adaptive materials + damage observer + qualification loop;
- stargate → traversable-wormhole engineering obligations;
- warp drive → warp-metric obligations;
- reactionless drive → anomalous-momentum residual protocol.

All sci-fi promotion fields default false.

## 13. Scientist-frontier and historical evidence graph

The scientist audit maintains two graphs that cannot automatically discharge one another.

Scientific graph:

scientist → papers/patents/projects → equations/apparatus/materials → strongest demonstrated result → unresolved frontier → DASHI consumer.

Historical graph:

scientist → institution/funding/programme/collaborator → event/archive/record.

No implication:

interesting research → targeting/suppression/death causation.

The historical graph may generate acquisition targets only. Physical claims require independent scientific evidence.

## 14. Inverse design

The long-term inverse compiler starts from a consumer output and works backward through only licensed arrows.

Examples:

- desired spectral/topological property → admissible quantum geometry/symmetry → Hamiltonian → material candidates;
- desired entropy/work cycle → admissible free-energy landscape → controls/materials;
- desired reactor metric → confinement/burn/power/material requirements;
- desired thrust/flow control → momentum/field/plasma requirements;
- desired spacetime metric → Einstein tensor/stress-energy requirement → candidate physical source class.

Each inverse step must be marked as one of:

- theoremically sufficient;
- theoremically necessary;
- empirical;
- fitted/model-dependent;
- conjectural;
- unpaid.

No inverse search may convert a necessary condition into a sufficient design recipe.

## 15. Experimental design and Pareto selection

When multiple models fit current evidence, use existing experimental-coordinate / investigative-Pareto machinery to rank experiments by expected discriminatory value subject to cost/risk.

Required outputs:

- candidate models;
- unresolved coordinates/nuisance variables;
- candidate measurements;
- predicted observer separation;
- acquisition/calibration requirements;
- same-object identity requirements;
- expected information gain or finite proxy;
- cost/risk/feasibility score;
- terminal stopping rule.

This applies equally to MATBG, calorics, FRC, hypersonic MHD, materials qualification, precision thrust and exotic-gravity tests.

## 16. Validation strategy

Implementation is RED-first and must include negative regressions.

### 16.1 Core fixtures

- exact finite energy-ledger arithmetic;
- exact finite momentum-ledger arithmetic;
- explicit boundary-flux accounting;
- residual changes when a nuisance channel is added;
- same-object/time-interval mismatch rejected;
- absent channel cannot be silently treated as zero.

### 16.2 Consumer-descent regressions

Construct explicit collisions in which a coarse observer identifies two fine worlds while the target consumer separates them.

Examples:

- same measured thrust signal, different thermal-strain state;
- same coarse temperature, different material/process state;
- same band-energy observation, different wavefunction/quantum-geometry state;
- same density observation, different FRC morphology/stability state.

### 16.3 Attribution regressions

Tests/static contracts must reject:

- paper/source fact promoted to DASHI generic theorem ownership;
- company claim accepted as calibration;
- historical technical association accepted as collaboration/intent;
- sci-fi consumer accepted as empirical producer;
- analogue/simulation promoted to literal spacetime engineering.

### 16.4 Exotic/FTL regressions

Reject:

- local negative energy → macroscopic warp capability;
- energy-condition violation → impossibility;
- effective negative mass → gravitational negative mass;
- quantum teleportation → FTL signalling;
- wormhole simulation → physical wormhole;
- nonzero force residual → antigravity;
- subluminal warp metric → FTL travel.

## 17. Implementation sequencing

After this design is approved, write the detailed implementation plan and execute in the following order:

1. conservation/factorisation kernel and promotion boundary;
2. negative regression suite and attribution firewall;
3. adapters for existing Rocketdyne + fusion/MHD + precision-thrust/exotic-gravity owners;
4. MATBG/MAGNOTHERM adapters where existing owners expose sufficient state;
5. quantum-stress-energy bridge using existing Casimir + GR energy-condition machinery;
6. exotic-stress-energy classification/promotion ladder;
7. FTL/teleportation/analogue/wormhole/warp consumer hierarchy;
8. scientist-frontier acquisition crosswalk;
9. inverse-design + experimental-Pareto integration;
10. rollup/status owner declaring paid vs conditional vs external-acquisition leaves.

## 18. Terminal status / stopping rules

The implementation must end with a terminal owner that prevents additional abstraction from masquerading as progress.

Remaining leaves must be classified into at least:

- theorem/proof obligation;
- source-acquisition obligation;
- same-object experimental-data obligation;
- calibration obligation;
- material/apparatus identity obligation;
- numerical/execution obligation;
- external replication obligation;
- engineering-realizability obligation.

Examples of legitimate terminal external frontiers:

- literal MATBG same-sample spectral/entropy/calibration inputs not currently available;
- FRC/nozzle direct-conversion data not measured;
- hypersonic MHD same-run full field/plasma/force calibration absent;
- precision anomalous-thrust experiment not independently replicated;
- quantum negative-energy stress tensor not scalable to gravitational significance;
- warp/wormhole required stress-energy not shown to be physically realizable;
- causal superluminal transport has no experimental producer.

No new abstraction layer counts as payment for these leaves.

## 19. Success criteria for the first implementation programme

The programme is successful when the repo can do all of the following without changing epistemic rules between domains:

1. take a concrete physical-domain state and expose the relevant conserved/accounted quantities;
2. prove when a coarse observation is insufficient for a requested device/physical consumer;
3. calculate an explicit residual relative to admitted same-object channels;
4. refine the observer when a nuisance variable matters;
5. block unsupported promotion to anomalous/exotic claims;
6. reuse the same architecture for at least four physically distinct domains;
7. connect existing Casimir/QFT-style negative-energy candidates to GR obligations without calling them warp engineering;
8. type warp/wormhole/FTL/teleportation consumers so each stronger claim visibly requires additional producers;
9. preserve source attribution and DASHI synthesis ownership;
10. expose the exact next experiment/source/data artifact that would maximally advance each live frontier.

## 20. Programme thesis

The overarching DASHI physics thesis for this programme is:

> Compile controllable structure into physical behaviour while proving exactly which distinctions matter for each desired effect.

The domain ladder is:

atoms → chemistry;
geometry → Hamiltonian;
state → entropy/work;
fields → momentum;
stress-energy → geometry;
geometry/causal structure → transport.

The final arrow is a research target, not an established capability.
