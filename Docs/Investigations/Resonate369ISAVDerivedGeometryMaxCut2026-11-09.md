# Resonate369 / ISAV derived geometry — maximum-cut ledger (2026-11-09)

## Scope and attribution
- Historical Slobodian / Infinity SAV claims are *not* equivalent to the independent David Holmstrom / Resonate369 C07, Dodecatron, V1 impulse motor or AtmoMotor.
- Read-only third-party STL / STEP may be inspected for metrology; **do not vendor, mirror, redistribute, embed, reconstruct source meshes or commit downloaded CAD**. Retain independently produced measurement tables and mathematical abstractions, with creator, product page, access date, measurement method and uncertainty.
- No claim of anomalous energy generation follows from geometry or peak/open-circuit voltage.
- For C07, manufacturer listing warns about magnet retention; this repo work does not certify mechanical safety.

## Public source locations and claims to verify
- https://friendbeacon.com/product/resonate369-1st-isav-hand-start-prototype-stl-build-kit/ — C07 claimed 8-station rotor, two offset stations; catalogue dimension claims 92 mm rotor diameter; 24.1 × 9.0 × 4.4 mm magnet blocks.
- https://friendbeacon.com/product/resonate369-impulse-resonator-motor/ — V1 impulse motor, bifilar and reed-switch timing claims.
- https://friendbeacon.com/product/aether-pulse-motor-ez-spin-impulse-motor-build-files/ — separate EZ Spin variant.
- https://friendbeacon.com/product-category/3d-stl-files/ — product category; not an archive of downloaded geometry.
- https://friendbeacon.com/resonate369-electro-v6-atmomotor-stl-files/ — electrostatic AtmoMotor: physically distinct.
- Friendbeacon Resonate369 Single Phase Dodecatron product text supplied by the user — 12 magnets, 12 series-connected CW/CCW coils, alleged 330 V / 50 mA near 300 Hz.
- Historical Infinity SAV USA technical presentation (2017), claimed 250 bifilar coils / 250 magnets; third-party historic source, not a design identification.

## Source-to-proof admission rule
Every physical geometry coordinate requires (source, selected design revision, coordinate frame, extraction method, units, uncertainty, independent verification status). Unobserved coordinates remain symbolic. 
CAD body geometry is not necessarily actual magnet centre or coil winding centre. In particular bobbin outlines are not proof of copper turns, terminal polarity, or gap under rotation.

## Closed in the finite arithmetic reference module
- `c07NominalPitchCloses`: 8 × 45,000 millidegrees = 360,000.
- `dodecatronNominalPitchCloses`: 12 × 30,000 = 360,000.
- `historicalMG10ClaimedPitchCloses`: 250 × 1,440 = 360,000.
- `c07HalfTurn`, `dodecatronHalfTurn`, `historicalMG10HalfTurn`: exact nominal opposing-station angular separation.
- Three `GeometryReference` values maintain scope separation and explicit `sourceCADNotVendored`.
- Kernel acceptance remains **unverified** unless separately executed with the pinned repo toolchain.

## Remaining highest-alpha gates

| Priority | New declaration contract | What pays it | Status |
|---|---|---|---|
| P0 | `originalC07CADMeasuredStationCoordinates` | Read-only selected C07 STL/STEP geometry, versioned measurement receipt | OPEN |
| P0 | `originalDodecatronCADMeasuredStationCoordinates` | Read-only selected Dodecatron geometry, or mark no CAD accessible | OPEN |
| P0 | `originalC07TwoOffsetStationsSameCAD` | Distinguish six baseline from two angled magnet stations in real model | OPEN |
| P0 | `sameRevisionCoilMagnetAxisAirgap` | Source-selected coordinate frames, nominal and minimum gap | OPEN |
| P0 | `sourceCADMeasurementUncertaintyBound` | Quantised mesh / CAD extraction uncertainty, registration and tolerances | OPEN |
| P0 | `derivedGeometryKernelChecked` | Agda 2.9 acceptance on actual repo head and imports | OPEN |
| P1 | `finiteCyclicStationIndexClosure` | `Fin N`, modular successor and all-word coordinate congruence | OPEN |
| P1 | `signedPitchErrorTelescopes` | A selected ordered cyclic lift of actual station angles | OPEN |
| P1 | `rigidRotationPreservesRelativeGeometry` | Circle-group action and metric isometry, without axial simplification | OPEN |
| P1 | `alternatingWindingSameOutputPolarity` | Coil-terminal wiring, rotor-pole sign and observed phase assignments | OPEN |
| P1 | `c07DodecatronMG10RefinementComparison` | Explicit embeddings/coarse-graining, not assumption that 8 divides 12 or 250 | OPEN |
| P2 | `measuredFluxIsSourceCoilFlux` | Original coil turns, magnetic field / flux calibration and selected geometry | OPEN |
| P2 | `originalSwitchingLawSameReedOrDrive` | Distinguish V1 reed switch from Part 11 electronics | OPEN |
| P2 | `originalShaftTorqueFromCoenergy` | Source-calibrated field/coenergy vs angle at fixed current | OPEN |
| P2 | `sameCycleElectricalMagneticMechanicalBalance` | Simultaneous waveforms, energy storage changes and torque/speed | OPEN |
| P3 | `loadedOutputPowerSameReportedVoltageCurrent` | Show 330 V and 50 mA same-time loaded RMS/real-power relation | OPEN |
| P3 | `independentAnomalousEnergyResidual` | Repeated complete system boundary accounting vs uncertainty | OPEN |

## Concrete nonclaims / negative controls
1. `330 V × 50 mA = 16.5 W` only if volt/current are simultaneous appropriately defined DC or resistive RMS quantities; AC real power needs phase and harmonic analysis. No input-output efficiency bound follows from that multiplication.
2. 300 Hz electrical frequency and 3,000 RPM imply six pole pairs only under selected alternation and fundamental harmonic assumptions; not universal.
3. The physical 250-position claim provides nominal 1.44° pitch but **not** a measured CAD geometry or a demonstrated mapping to the C07.
4. A winding labelled clockwise need not have the same effective polarity as another clockwise winding until viewing direction, terminal choice and rotor pole sign are fixed.
5. No accumulation of magnets creates additional energy by itself. Inductive energy recovery changes where previously supplied energy is dissipated, not whether conservation holds.

## Integration targets
Inspect and reuse instead of duplicating:
- `DASHI.Foundations.Base369CirclePhase` and `Base369PolyphaseCharacters` for finite phase carriers.
- `DASHI.Geometry.Base369SectorUnrollingFinite` for discrete angular/radial witness idioms.
- `DASHI.Physics.QuantumVacuum.CoilNoiseExperiment` for discrimination between spectral phenomena and harvestable power.
- Existing electromagnetic energy accounting and source/provenance receipts, after exact import discovery.

## Next maximum cut
The greatest evidence gain comes from the same-revision measured C07 station coordinates and coil-axis/polarity map, then exact cyclic comparison. The greatest physical gain comes from loaded simultaneous voltage/current and shaft torque/speed with storage boundary accounted. Avoid spending the next cycle on unconditional over-unity claims, unjustified 250-coil identification or vendor-file redistribution.

## 2026-11-09 continuation: conditional polarity and common refinement

Added `DASHI.Physics.Motors.Resonate369ConditionalPolarityExact`:
- `flipInvolution`
- `pairedReversalPreservesSign`: flipping both magnet pole and winding sign leaves selected-terminal parity unchanged.
- `reversingTerminalFlipsSign`
- `reversingOnlyPoleFlipsSign` (negative control).
- These are explicit symbolic hypotheses; no actual winding or polarity correspondence was observed from CAD.

Added `DASHI.Physics.Motors.Resonate369CommonRefinementExact`:
- 3000 nominal sectors × 120 millidegrees = 360 degrees;
- C07 station step = 375 sectors, 8 × 375 = 3000;
- Dodecatron step = 250 sectors, 12 × 250 = 3000;
- Historical 250-position claim step = 12 sectors, 250 × 12 = 3000;
- independent first-station and full-turn exact numeral witnesses for all three.
- Common grid is mathematically useful for comparison but is NOT evidence that physical coils or magnets are actually aligned to that grid.

A local Python enumeration checked all 24 Boolean parity invariant cases and the common-grid integer arithmetic; **that is not Agda kernel acceptance**. The Agda toolchain was not available in the current container. All three Agda modules therefore remain kernel-verification pending.

### Updated cut status

- `c07DodecatronMG10RefinementComparison`: **nominal common-grid arithmetic closed; actual measured coordinate mapping remains open**.
- `alternatingWindingSameOutputPolarity`: **conditional sign parity closed; source measured polarity, terminal and waveform correspondence remain open**.
- `finiteCyclicStationIndexClosure`: selected exact numeral turn closures done; arbitrary `Fin N` group action remains open.
- `signedPitchErrorTelescopes`: remains open at Agda kernel level; do not equate nominal reference proofs with measured nonuniform spacing.
- Input/output measurement, magnet retention, actual CAD extraction, and all physics gate proofs remain open.

## 2026-11-09 continuation II: nonuniform signed angular walk

Committed `DASHI.Physics.Motors.Resonate369SignedPitchTelescopingExact` at commit `10953bb0673533b7ab75c05f6accfb8f873f37b3`.

- `AngularGroup`: an explicit abstract group receipt for unwrapped angular coordinates; all required group laws are fields, not silently assumed.
- `Walk.difference`: relative displacement `neg a ⊕ b`.
- `Walk.signedIncrementSum`: finite sum along any selected ordered list of angular samples, including nonuniform station spacing.
- `Walk.cancelFirst`: algebraic cancellation of the first increment.
- `Walk.signedPitchTelescopes`: start angle plus all signed increments equals the final sampled angle.
- `Walk.leftCancelToZero`: explicit left cancellation, used for closed walks.
- `Walk.closedWalkSignedPitchZero`: a walk returning to exactly the same **unwrapped** angle has zero net signed increment.
- `Walk.rigidRotationPreservesDisplacement`: a rigid coordinate translation transports any established relative displacement.

**Important distinction:** a one-turn *unwrapped* rotor path ends at its initial angle plus one full turn, not at its initial angle; it is not covered by the zero-increment closed-walk assertion. For a full turn, instantiate the endpoint displacement as 360000 millidegrees and compare a list of selected nominal increments using a separately proven pointwise-error summation theorem. A circle quotient may identify endpoints but must not lose the winding number.

### Verification status for this continuation
- Local brute-force model checks across finite modular groups and balanced-parentheses check passed. These are not Agda kernel checks.
- No `agda` executable was present in the current available container. **Kernel acceptance is open**, and this PR remains draft.
- The theorem signatures are mathematical contracts in Agda source but have not yet been accepted by the pinned toolchain.

### Next hard leaves, in order
1. `measuredPitchErrorListSumsToZero`: select unwrapped CAD station sequence and prove pointwise measured-minus-nominal pitch-error sum zero for one full turn, retaining winding number.
2. `originalC07TwoOffsetStationsSameCAD`: original-source coordinate witness for the two specifically angled C07 stations.
3. `finiteCyclicStationIndexClosure`: integrate generic `Fin N` modular successor with the existing finite phase carrier and the new list walk; the new list telescope is only a partial closure.
4. `derivedGeometryKernelChecked`: run Agda 2.9 on all four new source modules and imports.
5. `sameRevisionCoilMagnetAxisAirgap` and real polarity wiring remain measurement dependent.
6. Same-cycle electrical/magnetic/mechanical power accounting remains a separate original physical experiment gate.

### Additional generic full-turn lemmas, commit 03bd40f9

- `Walk.leftCancellation`: cancellativity for two arbitrary relative displacements in a common angular group.
- `Walk.fullTurnSignedPitch`: the measured ordered samples have signed increment sum exactly `turn` whenever the unwrapped last sample is the initial angle plus `turn`. This closes the **abstract** full-turn telescope with a supplied endpoint witness, but not the concrete C07 station list, nominal-pitch error sum, or geometric measurement.
- The name `closedWalkSignedPitchZero` applies only to equal *unwrapped* endpoints; do not use it to erase 360 degrees.
- Both new lemmas are unverified by Agda and require pinned-toolchain acceptance.

## 2026-11-10 schematic-entailment route (commit 52ca35eb)

New module `DASHI.Physics.Motors.Resonate369SchematicAdmissionExact.agda` replaces the erroneous assumption that CAD metrology is mandatory for electrical topology.

### Implemented source/evidence interfaces

- `DesignIdentity` explicitly distinguishes historical Slobodian MG10 from the independently designed Resonate369 C07, Dodecatron, V1 impulse, EZ Spin and AtmoMotor.
- `EvidenceKind`: manufacturer description, original schematic, read-only CAD, video observation, instrument measurement.
- `SourceReceipt` and `SelectedEvidence`: versioned, same-design provenance with explicit inspection obligation. Records are **interfaces**, not magically certified eyewitness facts; no concrete observation is populated.
- `Component`, `Port`, `Netlist`, `Reachable`: directed pin-level connectivity model. `twoEdgePath` establishes two-edge structural path entailment conditional on explicit source connections.
- `AdmittedConnection`: combines a selected-source witness and the actual represented edge.
- `SelectedSeriesTrace`: distinguishes positive series path evidence from a further absence-of-bypass obligation; a prose claim that coils are 'series' is not a verified electrical netlist.
- `SelectedWindingPolarity`, `OppositePoleAndWinding`, `pairedCoilsPredictedSignAgreement`: conditionally proves sign agreement when source-backed opposite pole/winding and equal terminal conventions are supplied.
- `ExperimentClosure` is a separate measurement gate; no topology theorem instantiates physical output, recovery fraction or anomalous energy.

### Source-derived vs conditional vs unmeasured

| Design | Accessible description claim | Conditional inferred consequence | Not yet admitted |
|---|---|---|---|
| C07 | Eight stations, six main and two angled stations, historical-derived experimental coil roles | Finite angular index; nominal 45-degree pitch only if uniform | Measured two-station angles, polarity, actual coil terminal connections |
| Dodecatron | Twelve magnets, twelve CW/CCW coils described as series | Opposite pole plus opposite winding can reinforce selected terminal sign | Pole-by-pole sign sequence, terminal orientation, complete netlist, loaded output |
| V1 Impulse | Bifilar and reed-switch commutation description | Position-responsive switching is plausible under specified wiring | Actual reed contact circuit, phase, energy recovery path |
| Historical MG10 | 250-coil / 250-magnet presentation claim | 1.44-degree nominal station pitch if uniform | Actual position map and original switch/control circuit |

**No complete original manufacturer schematic was acquired in this continuation.** Friendbeacon product and membership pages confirm the marketplace and access pathways but cannot attest the completeness of a schematic: https://friendbeacon.com/ and https://friendbeacon.com/faq/.

### Highest-alpha revised maximum cut

- S0 (DONE as implementation, unverified kernel): source-bound schematic inference interface, typed design separation, 2-edge path, conditional winding sign theorem.
- S1 (OPEN): fetch/inspect actual original schematic or annotated assembly images and instantiate `SelectedEvidence` with a traceable, source-specific receipt; inspect every claimed connection.
- S2 (OPEN): convert a complete original C07/Dodecatron/V1 netlist to a finite port graph, prove component-port compatibility, polarity order and no bypass; do not infer absence of missing wires from silence.
- S3 (OPEN): check V1 reed-switch polarity/timing and any coil flyback recovery branch from real source wiring; distinguish diode clamp dissipative circuit from energy recapture.
- G1 (OPEN): read-only CAD/dimensioned drawing for C07 two angled stations and coil/magnet gap; electrical topology does *not* require exact CAD metrology.
- V0 (OPEN): pinned Agda kernel acceptance of all source modules. Environment in this tool session does not contain Agda; no kernel-check claim.
- P0 (OPEN): observed simultaneous cycle-integrated input and output, energy storage, shaft torque/speed with instrument uncertainty; no over-unity inference before this.

Avoid treating the constructibility of a `Set`-valued witness as real-world inspection: provenance requires matching a source receipt to an actual source and its content, outside of Agda's logical kernel.

### 2026-11-10 additional canonical netlist model

Added `DASHI.Physics.Motors.Resonate369SeriesTraceModelExact`, commit `eadf0092`.

- Defines `SeriesEdge` with distinct through-coil traversal and inter-coil junction constructors.
- Defines `canonicalSeriesNetlist` and a generic path concatenation `appendReachable`.
- Defines `canonicalSeriesPath n` for a model containing `n+1` nominal series coils.
- Instantiates `twelveCoilSeriesPath` for coil indices 0 through 11.
- Crucially, does **not** construct a real-device `SelectedSeriesTrace`, nor claim that the model is the manufacturer's actual wiring.

The schematic admission file was corrected at commit `cd031186` to use `Netlist : Set₁` (since its edge family takes values in `Set`), to avoid reserved `then` as a constructor, and to expose Boolean attestations for source inspection and no-bypass status. These remain trust-boundary assertions requiring an independent exact source inspection.

#### Remaining max-cut after this implementation
S0 model (implemented, kernel unchecked): generic topology, two-edge derivation, canonical series model, conditional winding sign.
S1 source (open): actual original/source-specific schematics or annotated build wiring, with exact URL/revision and wire-to-port transcription.
S2 weld (open): source-depicted edges = model `SeriesEdge` for the same Dodecatron build revision, including bypass exclusion, coil terminal sign and polarity.
S3 switching (open): real V1 reed contact and commutation/flyback graph; do not identify 'recycling' merely from coil-switch presence.
G1 physical geometry (open): two C07 angled stations and measured air gap from authorized read-only reference.
V0 proof (open): pinned Agda kernel checking on actual branch.
P0 experiment (open): full source/output, storage and mechanical load energy accounting.

Public Friendbeacon listings are sufficient for **design claims**; not for proof that all physically relevant netlist edges are present. No vendor CAD was added.

## 2026-11-10: reusable 369/27 circuit-components and search tranche

### Repo reuse audit

- `DASHI.Foundations.Base369TriadicPhaseTower` already exposes `Phase27`, `triTo27`, `phase27ToNonarySector`, `phase27ToTriSector` and section theorems.
- `DASHI.Foundations.Base369PolyphaseCharacters` already models symbolic three-sequence exponent characters. No physical sinusoidal signal implied by the finite field.
- `DASHI.Computation.AStarPlateauFibreExact` provides A* tie-fibre boundaries and `AStarCorrectnessContract`. `DijkstraQueueFibreExact`, `PathfindingFibreFamilyExact` cover related algorithm contracts.
- PR #1486 `Filsinger × Lyden Earth-port max-cut: source bounds and switched-capacitor power audit` contains existing numerical capacitor energy and recharge/recirculation bounds. Its two changed files (as compared to master during inspection) are `Docs/research/FilsingerLydenEarthPortMaxCut20261110.md` and `scripts/filsinger_lyden_earth_port_maxcut.py`. Reuse these for numeric energy audit rather than duplicating them in motor schematic code.
- Default-branch GitHub code search for literal `capacitor`, `resistor`, and `Kirchhoff` returned no indexed module matches. This is NOT a proof those constructs do not exist in historical/unmerged PRs.

### New modules

- `DASHI.Physics.Motors.Circuit36927ComponentGraphExact` defines component kinds (passive R/L/C, sources, semiconductors, switches, magnetic elements), dimension-tagged nominal values, arbitrary pins/junctions, explicit wire edges, graph routes, source-bound model interfaces, and a coarse/fine 3/9/27 phase projection with a reused section proof. A declared component/edge is not an actual observed device.
- `DASHI.Physics.Motors.Circuit36927SearchBridgeExact` connects circuit wiring graphs to existing A* contract types, records explicit Nat admissibility bounds and calculated route cost, requires a universally quantified comparison against rival routes for shortest-path promotion, and builds an exact C3-C9-C27 hierarchy. It does not claim the abstract source-dependent A* run already exists.
- `DASHI.Physics.Motors.Circuit36927IllustrativeRCExact` is an entirely DASHI-authored 12 V, 1 kohm, 3.3 microfarad RC component instance with integer units and three declared wire edges. It certifies exact value dimension labels but does not simulate current or capacitor charging.
- `scripts/circuit36927_netlist.py` is a standard-library, executable reference for parts, pins, values, wires, Graphviz DOT export, nonnegative-cost Dijkstra/A*, phase hierarchy and simple checks; uses independent example values only. Authoring-workspace tests passed, but this is NOT Agda kernel acceptance and NOT physical circuit validation.

### Diagram and inference boundaries

- DOT output represents explicit wires and component blocks. It does NOT silently insert conduction across resistors, capacitors, open switches, diodes or active semiconductors.
- Electrical topology and phase discretisation are orthogonal: tagging the same component by C3/C9/C27 does not assert that the physical machine has 27 coils, 27 phases, or any particular frequency. It is a finite resolution/refinement carrier.
- A* / Dijkstra answer connectivity/routing/design search only under their path-cost and heuristic contracts. They do not compute node voltages, branch currents, switching timing, electromagnetic flux or shaft torque.
- For a physical circuit model, KCL, KVL, constitutive equations (R, C, L, semiconductor, switch), component tolerances, energy storage, source boundaries and load power must be introduced as separate law-bearing interpretation records.
- C07, Dodecatron and V1 manufacturer schematics remain **not acquired**. No actual vendor netlist instantiated.

### Highest-alpha remaining lemmas and deliverables

| Priority | Exact gate | Evidence / theorem |
|---|---|---|
| P0 | `allCircuit36927ModulesKernelChecked` | Run pinned Agda 2.9 with current module import graph, fix errors |
| P0 | `actualDeviceSchematicTranscriptionSameSource` | Versioned Friendbeacon original circuit / drawings, pin labels and revision correspondence |
| P0 | `wireEndpointsWithinDeclaredPinCount` | Fin-indexed parts and pins, no missing IDs or unresolved junctions |
| P0 | `sourceBoundNetlistGraphWeld` | Measured or visually attested wires to signed port graph, explicit missing-connection boundary |
| P1 | `circuitRouteSoundnessFromNetlist` | Route iff finite paths in selected and valid netlist |
| P1 | `astarOptimalityFromAdmissibleConsistentHeuristic` | Actual A* algorithm/refinement to existing family contracts, not merely carrier |
| P1 | `phase27CoarseGraphPathLift` | Explicit edge-preserving refinement map and path lift; false in general without assumptions |
| P1 | `seriesCoilPolarityActualWiring` | Source-selected terminal and magnet-polarity observations |
| P2 | `sameNetlistKirchhoffKCLAndKVL` | Selected reference orientation and node/loop incidence |
| P2 | `resistorCapacitorInductorConstitutiveLaws` | Physical R/L/C units and differential/DAE semantics |
| P2 | `switchedTopologyEnergyCycleIdentity` | Source drive, flux, flyback, stored-energy and dissipation algebra with switches |
| P2 | `motorCoenergyTorqueSameGeometry` | Magnet, airgap, winding geometry and calibrated constitutive laws |
| P3 | `realDeviceLoadedPowerResidual` | Calibrated simultaneous input/output/storage/shaft measurements, uncertainty |

No STL/STEP/CAD or original manufacturer circuitry copied. Attribution: historical Slobodian/Infinity SAV, Holmstrom/Resonate369 and independent DASHI formalism remain separately identified.

### 2026-11-10: generic internal-transfer conservation

Added `DASHI.Physics.Motors.Circuit36927InternalTransferConservationExact` (commit `b5fb0b5a`). It reuses `Resonate369SignedPitchTelescopingExact.AngularGroup` and constructs:
- `pairedSignedTransfer i = neg i ⊕ i`
- `eachInternalTransferCancels`
- `aggregateInternalTransfers` over an arbitrary finite list
- `allInternalTransfersCancel`, an abstract group-law cancellation theorem.

This is an **exact structural accounting identity**, *not* per-node Kirchhoff current conservation, real device current continuity or measured energy conservation. Per-node edge incidence and physical constitutive weld remain OPEN. Agda kernel verification of the new module and prior modules is also OPEN.

## 2026-11-10 continuation: physically meaningful numerical RLC solver and bounded pins

### Implemented
- `Circuit36927TypedPinsExact.agda` (commit `43bd1a62`): `FiniteParts`, `ValidPort`, `ValidWire`, `TypedNetlist`; bounded component index and dependent bounded pin index; wire reversal involution. These replace the prior unconstrained raw-Nat pin references at the trustworthy graph boundary.
- `Circuit36927TwoNodeKCLExact.agda` (commit `0b38543d`): conditional two-branch equality implies signed node-current cancellation. Uses existing additive-group contract; equality of physical currents must be established independently.
- `scripts/circuit36927_mna.py` (commit `19b08ebb`): independent modified-nodal analysis reference for two-terminal R/C/L elements and ideal voltage/current sources, with explicit ground, wire-union node identification, per-source branch-current unknowns, backward-Euler capacitor history current and inductor history current, partial-pivot linear solve, singular/floating-network rejection, branch voltages/currents, and KCL residual diagnostics. This is an original DASHI reference implementation, not source-derived vendor wiring.

### Tested in authoring environment
- RC example: 12 V, 1000 ohms, 3.3 microfarads, backward-Euler dt=0.00033 seconds, 100 steps; resulting capacitor voltage 11.99912921140919 V, matching BE closed form 11.999129211409182 V.
- At each RC step, tested: KCL residual under 1e-9 A, resistor/capacitor current equality, series KVL, and source power = resistor power + capacitor stored-energy difference / dt + nonnegative BE numerical dissipation. The numerical dissipative term cannot be mistaken for a source of energy.
- RL example: 10 V, 10 ohms, 1 H, dt=0.1 seconds, initial 0 A; BE first-step inductor current 0.5 A.
- Input validation: rejects missing connection endpoints and an electrically disconnected floating resistor component; a correctly grounded lone resistor is *not* singular.
- A local test was executed against a slightly more verbose implementation of the same stamping algorithm; the subsequently committed condensed script has not yet been executed in this environment. Treat exact committed-script regression verification as pending until run.
- Agda 2.9 kernel acceptance remains open because the toolchain is not installed here.

### Important nonclaims
- Model only: ideal linear R/L/C and DC independent voltage/current sources. NO diode, MOSFET, reed-switch transitions, hysteresis, coil–magnet coupling, flux calculation, mechanical torque, AC harmonic solver, nonlinear solver or experimentally demonstrated pulse-energy recovery.
- Physical energy conservation and the discretisation energy identity are distinct. Backward Euler adds nonnegative numerical dissipation; a calculation of negative numerical loss would signal an implementation/sign problem.
- Finite C3/C9/C27 phase indices support refinement, not mystical/empirical 369 energy significance.
- A* graph search remains distinct from MNA. A* can optimise probe paths or candidate topology, not solve circuit dynamics.
- No vendor CAD, STL, STEP, schematics, or copyrighted netlist content is vendored.

### Revised highest-alpha cut
1. V0: run pinned Agda kernel on all new modules; run the exact committed Python MNA script with tests.
2. M1: weld `TypedNetlist` to the Python wire-node compiler with a jointly checked finite incidence matrix.
3. M2: add machine-checkable R/C/L constitutive laws and per-node KCL/KVL to Agda, then a source-selected MNA soundness bridge (symbolic or rational arithmetic).
4. M3: support ideal switch states and realistic diode/MOSFET models (with explicit signed passivity/energy assumptions), then investigate pulse recovery.
5. S1: acquire lawful read-only schematic/wiring documentation from Holmstrom and verify same-design/source topology; preserve Slobodian/Holmstrom/DASHI attribution.
6. P3: original instrument input/output, capacitor and inductor states, shaft torque/speed and uncertainties. Do not infer physical efficiency from topology or simulations.

## 2026-11-10 switched-capacitor recovery / exact rational equalisation continuation

### New source files on PR #1482

- `scripts/circuit36927_switched_capacitor_recovery.py` (commit `0b94de51`): two-capacitor switched resistor model with explicit closed/open switch; backward-Euler charge transfer; exact (up to floating-point) discrete energy partition into final capacitor storage, resistor heat, and nonnegative integrator loss. Contains 200 seeded randomised tests and one closed/open multi-step reference.
- `scripts/circuit36927_equalization_exact.py` (commit `f53542f5`): rational arithmetic using Python `Fraction`, checking 501 cases including the reference 100 µF each at 12 and 0 V. Identifies final voltage `(C1*V1+C2*V2)/(C1+C2)` and equalisation loss `C1*C2*(V1-V2)^2/[2*(C1+C2)] >= 0`.
- No vendor CAD, electrical design files or proprietary netlists were added.

### Local checks actually executed

- Original reference at `/mnt/data/circuit36927/switched_capacitor_recovery.py`: initial 7.2 mJ, final 3.6 mJ, resistor heat 3.2727272727 mJ, backward Euler artificial loss 0.3272727273 mJ, 1 open step and 1999 closed steps, 200 randomised cases; no residual beyond tolerance.
- Original reference at `/mnt/data/circuit36927/circuit36927_equalization_exact.py`: 501 exact rational cases passed, 6 V final and 9/2500 J equalisation energy difference in the demonstration.
- Previously provided local `/mnt/data/circuit36927/circuit36927_mna.py` executed and reported RC 11.9991292114 V, 100 steps with four checks each, RL first step 0.5 A; this file is a mounted local reference and is not guaranteed identical byte-for-byte to the GitHub `scripts/circuit36927_mna.py` revision.
- `python -m py_compile /mnt/data/circuit36927/*.py` passed. This checks Python syntax only.
- **The committed GitHub file bytes for the two new scripts were not re-downloaded and executed separately**; local scripts and committed scripts are intended to implement the same test, but treat exact committed-file test status as pending unless re-executed.
- No Agda compiler was available; Agda kernel checking remains open.

### Exact mathematical and physical boundary

The equalisation formula follows algebraically from charge conservation and common final voltage. For the closed, passive, two-capacitor network without an external source, any differential-voltage energy is dissipated by physical losses and/or numerical dissipation in the selected implicit method; the code is *not* evidence that an alternative resonant switched circuit cannot return some energy to a designated storage node.

The 3/9/27 representation is an existing finite phase-resolution/indexing abstraction. Neither phase index, A* route search, nor the equalisation law establishes physical gain. A* can be reused for probe placement or topology optimisation with explicit cost/admissibility; physical dynamics remain in the RLC/MNA solver.

### Remaining maximum-cut obligations, ordered

1. **V0**: Agda 2.9 kernel acceptance for all changed modules and transitive imports, plus exact committed-script executable regression.
2. **S1**: actual original source-specific electrical schematics and connected coil/capacitor/switch terminals for the Holmstrom V1 impulse and Dodecatron; avoid false claim that a vendor design has been recovered.
3. **M1**: source-independent typed-pin finite incidence matrix, KCL/KVL correspondence, and machine-checked R/C/L laws plus MNA soundness over a selected algebraic carrier.
4. **M2**: passive switch / diode state model, recoverable inductor energy and capacitor return path; test simultaneous stored-energy and resistive-loss ledger including numerical integration loss.
5. **M3**: physically calibrated motor magnetic field / inductance versus angle, coil polarity, torque and mechanical load.
6. **P3**: physical-source admission via synchronized current/voltage/torque/time observations, fixed boundary and uncertainty. Never infer over-unity from a simulation or open-circuit voltage.

Attribution: Slobodian's historical claims, Holmstrom's documented designs, and the independent DASHI modelling contributions remain separate.
