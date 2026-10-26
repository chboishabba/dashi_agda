# Crystallography × 369 periodic-table / atomic / quantum prior-art audit

## Scope, ownership and no-promotion rule
This document concerns the shared *interfaces* between chemical identity,
spatial lattice/basis symmetries, electron configuration, and many-body
physics. It does not identify numerical 3/6/9 encoding with a discovered
physical interaction, and does not infer a material structure from the
atomic number or an uncalibrated ternary carrier.

### Confirmed native owners (inspected on master)
- `DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact`:
  canonical recovered 369 periodic-table lane, using pre-existing
  `Triadic.Kernel`, `NineSheet`, `AtomicFermionShellExact`,
  `AtomicValenceFermionBridgeExact`, and shell recurrence. Exposes
  `AtomicIndex` (proton, neutron, electron numbers), `Neutral`,
  `ElementEquivalent` (proton number), and `IsotopeEquivalent`.
  Its header expressly forbids equating ternary cardinality with orbital
  quantum numbers or structural closure with spectra/bonding.
- `DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact`:
  stage-indexed atomic -> molecular -> reaction -> industrial chemistry
  witnesses with separate provenance for each stage. An atomic state
  cannot be *definitionally* promoted to a bonded solid.
- `DASHI.Physics.Chemistry.AtomicPeriodicTable369PhysicalValidation`:
  archived Hartree defect, radial correction, H/NIST and helium
  physical evidence receipts; distinguishes repaired radial selection
  from SCF/many-electron/ionisation status.
- `DASHI.Physics.Chemistry.AtomicClosedShellSchurBridge`:
  conditional quantitative Schur-gap transport to valence stability,
  not unconditional band insulation or crystalline gap.
- `DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact`:
  finite antisymmetric two-fermion exchange and valence-pattern carrier;
  not a full electronic Fock space of a crystalline material.
- `DASHI.Physics.Chemistry.AtomicPeriodicTable369AttributionLedgerExact`:
  first-source chronology, citations, provenance authority and
  explicitly unresolved historical executable evidence.
- `DASHI.Physics.Chemistry.AtomicPeriodicTable369SymmetryReconstructionValidation`:
  reconstruction/chirality/biomolecular separation checks, with
  coarse-symmetry versus full physical identity boundaries.

### New repo bridge
`DASHI.Mathematics.Symmetry.CrystalAtomic369TypedSeparationExact`:
imports the *real* `AtomicIndex`, classification enums and point-group
types; carries a crystal-site metadata label with an element-identity
witness and a seven-system compatibility witness. The toy tetragonal
constructor is a formal schematic, not the structure of any element.
A fractional-site Nat label is *not* a real fractional coordinate.

## Correct multi-scale factorisation

1. **Element / isotope / ion:** nucleus indexed by Z,N and electrons.
   Chemical element equivalence is Z equality; isotopic equivalence adds N.
2. **Electron configuration / fermionic state:** one-particle Hilbert
   space, antisymmetrisation, actual Hamiltonian and its symmetries.
   Filling order and valence are model/prediction-dependent.
3. **Sites / crystal decoration:** Bravais lattice Λ, periodic
   atomic basis p_i in R³/Λ, species labels Z_i (and optionally
   isotope/occupation/magnetic moments). Symmetry g must preserve
   the *labelled* configuration, not simply the abstract lattice.
4. **Space group and site stabilisers:** (R,t) acts on sites; species,
   occupancy and appropriate spin/charge structure must be carried
   equivariantly. A site's Wyckoff stabiliser is not automatically
   its atomic orbital angular momentum symmetry.
5. **Band and many-body theory:** periodic Hamiltonian H and lattice
   translation representation; Bloch fibres H(k), orbital site
   representations, spin-orbit and magnetic/time-reversal operations.
   A space-group action maps H(k) to H(R k) with appropriate
   nonsymmorphic phase and *reciprocal* lattice action.
6. **Observable evidence:** diffraction structure factor with actual
   nuclear/electron scattering density, selection rules, measured
   intensities, instrument context, uncertainty and provenance.

The 369 ternary kernels and hyperfabric can encode finite approximations,
colourings, local incidence sections, or experiment metadata; they
do not imply any of the additional physical structures by counting alone.

## Strong proposed typed welds
- `PeriodicAtomicBasis`: lattice + finite indexed fractional positions
  + `AtomicIndex` species; site action needs `speciesPreserved`,
  `occupancyPreserved` and Seitz-compatible position equality mod Λ.
- `EquivariantCrystalHyperfabric`: same vertex/edge incident action
  commuting with existing `TypedHyperfabricCore.restrict`; optionally
  atomic species/charge/spin labels in stalks.
- `OrbitalBlochAdapter`: reciprocal-lattice action U^{-T}, site orbit,
  fermionic Hilbert/Hamiltonian and a spectral equivariance theorem.
- `NuclearVsElectronicScatteringBoundary`: distinguish nuclear Bragg
  diffraction and x-ray electron density, including experimental
  wavelength and form-factor authority.
- `PeriodicTableToSolidCounterexample`: same element admits different
  crystal structures (allotropy, polymorphism), so no unqualified map
  element -> unique Bravais class or space group.

## Attribution
Classical crystallography and space-group theory: IUCr International
Tables. Quantum atomic structure, antisymmetry, orbital/band and
diffraction theory: historical/primary literature, not credited as
new DASHI results. Prior native module headers and the 369 atomic
attribution ledger remain authoritative for the programme's
implementation chronology. This PR provides typed integration and
boundary contracts only. No new Agda typecheck, physical validation,
quantum kernel proof, or structure identification is claimed.
