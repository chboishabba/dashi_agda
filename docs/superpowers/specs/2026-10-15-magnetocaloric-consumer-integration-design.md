# Magnetocaloric Consumer Integration Design

## Goal

Populate the existing DASHI consumers that can soundly constrain or consume the magnetocaloric/AMR lane: SI/metrology, condensed-matter crystal and magnetic symmetry, chemistry/atomics, quantum/statistical mechanics, and continuum transport. Reuse NS/YM machinery only through already-generic operator/continuum interfaces; do not identify AMR physics with Clay Yang-Mills or Navier-Stokes claims.

## Architecture

The thermodynamic device lane remains the upper-level owner. New consumer bridges point from existing lower-level/state-specific machinery into its abstract carriers without collapsing observables. The dependency shape is:

atomic/electronic state -> crystal/magnetic symmetry -> quantum/statistical thermodynamics -> magnetocaloric material -> regenerator transport -> AMR cycle -> protected device.

SI quantities are attached at the boundary through exact dimensions and measurement records. Condensed-matter and chemistry bridges preserve the existing `shared carrier != shared observable` rule. Continuum transport is linked to the existing `ContinuumBalanceSystem`, `FluidDynamicsLaw`, and `DiffusionTransportLaw`; the Navier-Stokes regularity problem stays explicitly separate.

## Consumers

1. **SI/metrology**: add missing coherent dimensions required by magnetocaloric engineering (magnetic field strength, entropy, heat capacity, specific heat capacity, thermal conductivity) and a typed measurement bundle for AMR calibration.
2. **Condensed matter**: bridge material states to separate crystal phase, magnetic order, band-energy and thermodynamic observers; reuse observable-fibre/symmetry precedents without asserting a material-specific Hamiltonian.
3. **Chemistry/atomics**: bridge atomic-shell/valence and composition/substitution/hydrogenation descriptors into material identity and calibration; reuse the existing Schur closed-shell bridge as operator-reduction precedent only.
4. **Quantum/statistical mechanics**: make the Hamiltonian/ensemble/free-energy-to-observable chain explicit as an evidence-bearing provider of magnetisation, entropy and heat capacity; no partition function is fabricated.
5. **Continuum/NS**: connect regenerator solid/fluid transport to continuum balance and Fourier/fluid-law surfaces. Clay regularity is neither required nor inferred.
6. **YM**: no physical YM consumer is introduced. The only valid reuse is generic operator-reduction/symmetry machinery already factored out of the YM lane.

## Promotion boundary

No bridge may promote a symmetry skeleton, shell class, model Hamiltonian, SI type, continuum law interface, or vendor observation directly to measured `M(T,H)`, `Delta S`, `Delta T_ad`, cooling power or COP. Those still require material/device calibration evidence.
