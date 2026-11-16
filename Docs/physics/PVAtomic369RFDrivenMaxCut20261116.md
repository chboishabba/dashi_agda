# Photovoltaic x atomic 369 x RF-air x nonlinear drive: max-cut, 2026-11-16

**Status:** draft research cut. No same-material photovoltaic Hamiltonian, measured net gain, RF opacity proof, or Agda kernel acceptance is claimed. Follow local verification over CI. Keep source attribution and physical gates fail-closed.

## Existing sources reused

- `DASHI.Physics.Chemistry.AtomicPeriodicTable369C3FourierSpatialRestrictionExact` already contains exact character-addition and Fourier/rotation commuting law. `C3OpticalWorkBoundaryExact.c3PhaseTransportSquare` reuses the *same* C3 representation; it does not manufacture a new 9-slot model or optical dipole matrix.
- `DASHI.Physics.Chemistry.AtomicPeriodicTable369ManyBodyHamiltonianTerminalMaxCutExact`: selected interaction-sensitive p² Coulomb matrix `V_ee=(21/128) I_3` was already constructed. **Full periodic-material Hamiltonian and empirical spectra remain open.**
- `DASHI.Physics.Chemistry.AtomicPeriodicTable369SymmetryProjectionCompilerExact`: continuum/finite same-object equivariance requirements.
- `DASHI.Mathematics.Symmetry.DiamondNearestNeighbourBlochExact`: ideal spinless diamond Bloch structure; no real NV photovoltaic device.
- `DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact`, `Circuit36927RecoveryEnergyBoundExact`, and `Docs/research/SmithFilsingerCausalNonlinearSourceRollup20261115.md`: finite retarded channels, nonlinear pump work, explicit driver/recovery, source-qualified Poynting inputs.
- `DASHI.Environment.PhotosyntheticLightTransportCrossPollinationExact`: bio action spectrum and site conditioning. Does not imply bio-PV 50% conversion.

## C3 commuting-square and selection rule

For an exact C3 cycle shift P, three Fourier eigenchannels m, and a dipole operator D_r transforming in C3 charge sector r, a finite Fourier conjugation gives
`F† D_r F : m -> m+r (mod 3)`. A separately executed Python 3x3 numerical check verifies
`D_r F = F(F† D_r F)`, all forbidden entries below 5e-16 and the allowed values at 1 within error.

**Negative control:** D=0 has the same covariance but no optical absorption. C3 selects allowed channels; it does **not** imply a larger absorption coefficient, a real semiconductor bandgap, or better electrical power. The missing physics is optical dipole oscillator strength, spin/strain/sublattice, selected crystal, material-matched Hamiltonian, recombination, and a measured port.

## RF air optical-opacity discriminator

Collisionless free-electron cutoff `ncrit = eps0*me*(2*pi*c/lambda)^2/e^2`. Values:
- 0.5 micron: 4.46e27 electrons/m3 (178x neutral-air molecule count);
- 0.8 micron: 1.74e27 (70x);
- 1 micron: 1.11e27 (45x);
- 10 micron: 1.11e25 (0.45x).
Neutral-air molecular density assumed 2.5e25/m3. Ratios are **not** ionisation fractions. Ionisation of one electron per molecule even at a hopeful 12 eV costs at least ~4.8e7 J/m3 before collisional and maintenance losses. Thus visible solar-plasma mirror route is strongly disfavoured; enclosed tunable gas / thin absorbing film is a more testable alternative. Opacity, reflection, optical depth, heat extraction, RF input and plasma density must be measured.

## Nonlinear drive, capacitor and finite propagation

For q(V)=C0 V+alpha V^3, exact differential energy is
`U(V)= C0 V^2/2 + 3 alpha V^4/4`.
Naively using `C(V)=q/V` in `U=.5*C(V)*V^2` is wrong by `alpha V^4/4`. In a reversible closed charge-voltage cycle `int V dq=0`: high gross reactive flow may be recycled but is not newly harvested energy. Retarded local field `E(x,t)` need not equal instantaneous driver voltage. A *material effect* (Franz-Keldysh, QC Stark, Floquet sidebands, carrier separation) is required for conversion gain. The generic proof `<V(t)J(V(t))> <= max VJ` is only valid under unchanged memoryless I-V assumptions; do not use it to reject nonlinear or causal devices.

## Thermal TODO only

Do not implement cooling in this tranche. Record incident solar, outward light, exported electric energy, RF sent and returned, initial/final storage, and thermal residual. If later considering heat pump + heat engine, compare **net work** with the same-source exergy; boiling and condensate do not create a cold reservoir. Ideal example: source 323.15 K, sink 298.15 K, boosted 373.15 K; heat-pump plus engine can do no better than `1 - 298.15/323.15 = 7.736%` net per source heat in reversible limit.

## Exact remaining gates (not closed)

1. `PVMaterialBlochDipoleSameSource`: real atomic 369/C3 -> periodic interacting material Hamiltonian -> band edges -> measured dipole and oscillator strength.
2. `PVDrivenFranzKeldyshFloquetMaxwell`: time/spatially dependent field, local response, signed RF port work, photon flux, dissipative carrier continuity, and matched DC control. Find actual repository Floquet producer or explicitly declare absent; do not fabricate.
3. `PVFilmSpectralSplitterBidirectional`: thin-film transfer/scattering matrix and finite-angle/polarisation loss, compared with wedge, waveguide and luminescent systems.
4. `PVRFAtmosphereOpacityPowerNoGoOrWitness`: calibrated gas/plasma constitutive response, driver and receiver aperture, actual solar visible/NIR opacity, passivity or source-accounted gain.
5. `PVBioHybridChargeHarvest`: action spectrum, electrode electron export, rate equations, self-repair, steady-state maintenance and standard independent PCE/area efficiency.

## Sources / lineage

- GaAs voltage-dependent Franz-Keldysh observation: https://doi.org/10.1002/pip.3270
- Strong THz Stark in CdSe-CdS QDs: https://doi.org/10.1021/acs.nanolett.7b01837
- 2026 Ta2O5/SiO2 thin-film spectral splitter: https://www.sciencedirect.com/science/article/pii/S0960148126004027
- Luminescent cholesteric spectral lightguides: https://doi.org/10.1002/adom.71939
- PV angular/photon-recycling GaAs experiment: https://doi.org/10.1039/C3EE43584A
- 2026 engineered conductive-pili BPV: https://doi.org/10.1038/s41467-026-72407-7
- 2026 photosystem electrode review: https://doi.org/10.1021/acs.chemrev.6c00021
- Experimental air filament plasma density: https://pmc.ncbi.nlm.nih.gov/articles/PMC4248277/

**Acceptance boundary:** The new Agda file has not been Agda kernel checked in the current runtime. The independent Python/SymPy finite diagnostics passed locally but have not been ingested into this PR. This is draft max-cut infrastructure, not a closed physical efficiency gate.
