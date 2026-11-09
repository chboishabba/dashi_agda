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
