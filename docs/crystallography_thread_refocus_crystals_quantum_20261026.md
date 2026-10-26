# PR #1261 — renewed thread-wide scientific and formal roadmap
2026-10-26. This document supersedes an XOR-centric reading of the project.

## Scientific centre of gravity

The initial question was a tetragonal 4/mmm visual/source check and
exact formalisation, with attribution. The project widened because
DASHI already owns useful Weyl and finite group actions, 3D and 4D
lattices, atomic quantum and 369 periodic-table models, tensor and
hyperfabric charts, T4/T9/T18 local-to-global descent, and recent
diamond/NV/crystal and magnetic Seitz/Bloch research.

The objective is **one source-audited crystallography and quantum
material realisation layer**, supporting independent finite models
and physical tests. Its primary outputs are actual *representations*,
lattice automorphisms, site orbits, compatible atomic decorations,
Hamiltonian symmetry tests, and operational experimental discriminators.
A finite ternary cube is an unusually useful discrete testbed, not
a proof that physical crystals are intrinsically ternary.

## Existing donors and attribution (not recreated)

- B4: `DASHI.Physics.RootSystemB4Carrier` and
  `RootSystemB4WeylAction`.
- Finite geometric lattice: `Base369Ternary27HypervoxelFabricGeometryExact`;
  NS `NSIntegerFourierLattice`; Yang–Mills
  `BalabanBlockedPeriodicLattice`.
- Hyperfabric local/global: `TypedHyperfabricCore` and
  `TypedHyperfabricPantsGluingBridgeExact`.
- Exact T9 descent and T18 6-cell boundary / C3:
  `Trialectic369DescentNaturalityExact`,
  `TrialecticThreeCellHyperformSynthesisExact`.
- Atom/periodic-table and provenance:
  `AtomicPeriodicTable369GenerativeExact`,
  `AtomicPeriodicTable369PhysicalValidation`,
  `AtomicPeriodicTable369AttributionLedgerExact`.
- Diamond sensor (PRs #1238, #1262): NV four axes,
  spin-one Sz² obstruction, optical/magnetic forward model,
  explicit conditional physical gates.
- Material-specific magnetic Seitz/Bloch (PRs #1076, #1115):
  transfer typed techniques, never assign this material's
  magnetic symmetry group to diamond.

Established IUCr crystallography and mathematical Weyl/Coxeter,
Bloch/Seitz, spin and diffraction claims retain original attribution.

## Fundamental carrier separation

1. **Group** (D4h, O_h, W(B3), W(B4), C3 etc).
2. **Representation/action** on a specified geometric carrier.
3. **Lattice** with basis, metric, direct/reciprocal pairing.
4. **Atomic basis** with true element/isotope/electronic identity.
5. **Defect site** and ordered N/vacancy occupation.
6. **Quantum state and Hamiltonian** with independently checked
   symmetry or explicitly proved obstruction.
7. **Measurement** with source, calibration and uncertainty.
8. **Ternary encoding/charts** with explicit residual, geometry
   and local-to-global restriction witnesses.

No item can be inferred from a shared cardinality or naming
coincidence (e.g. 111, 13, 27, C3) alone.

## New reusable consumer gate

`CrystalRealizationConsumerContractExact.agda` specifies one
source-level interface for classified Bravais/point-group compatibility,
separately-typed direct and reciprocal G-actions, preserved pairing,
G-equivariant species-labelled site positions and a conditional
scalar band-energy symmetry. Its fields are **obligations**; the
record does not manufacture instances or quantum material evidence.

## Pareto phases and deliverables

### A. Validated finite mathematical core (immediate)
- Check/repair source Agda definitions, constructor patterns and
  proofs; no CI dependency is needed, but Agda compilation matters.
- Reuse B4 to obtain D4h and cubic signed-permutation actions.
- Prove common action on the distinct nine-cell, 8-height and
  27-cube carriers without false isomorphisms.
- Finish punctured 27 ↔ (8+9+9) proof, antipodal
  quotient of 26 → 13, projective strata 3+6+4.
- Note corrected kernel: -I acts trivially on all unoriented
  axes; both 13-axis and four-axis projective actions factor
  through O_h/{±I} of order 24.

### B. Actual crystal lattice and space-group mathematics
- Concrete rational/integral 3D Bravais basis and metric instances;
  explicit direct and contragredient reciprocal actions.
- Crystallographic group representation certificates, not just
  labels. Test order, faithful action, metric, lattice preservation.
- Tetragonal tP/tI and diamond fcc cF with 2-site basis;
  Seitz operators including nonsymmorphic translations.
- Broaden to 32 point groups and 230 space-group types with
  source-versioned IUCr/spglib data and verification receipts.

### C. Atomic + quantum consumer instantiation
- Weld `AtomicIndex`, electronic/valence/fermion carriers into
  species-labelled periodic basis and equivariant site orbits.
- For diamond, transport the four <111> axes, ordered
  N-vacancy defect stabiliser and existing NV spin-one
  obstruction; do not confuse spatial C3 with level C3.
- For both tetragonal and cubic exemplars, derive Bloch
  momentum transport and actual Hamiltonian covariance;
  include little groups, nonsymmorphic phases, possible
  degeneracies and counterexamples.

### D. Ternary/hyperfabric cross-validation (supporting track)
- Use 27 spatial testbed and native punctured-nine as finite
  representation of local-to-global residual preserving charts.
- Preserve T4/T9/T18, nonperiodic cube versus C3³ torus,
  and original hyperfabric pants matching.
- Study binary XOR orientation residual only when it solves a
  concrete seam-compatibility obstruction. This is a small
  supporting deliverable, NOT the central project.
- Distinguish operator-specific module action from mere
  finite-state permutations, especially modular braid versus
  geometric graph automorphisms.

### E. Physical/experimental evidence
- For test cases, record predicted diffraction/selection
  rules, magnetic response, optical ODMR, band structure and
  defect-axis spectroscopy with calibrated parameters.
- Compare steelman mechanisms against matched null models,
  real source data and held-out discriminatory measurements.
- Never promote a count or algebra analogy to a novel
  physical mechanism without an operational test.

## Deliverable gates and proof status

- Existing source files: provenance confirmed by GitHub retrieval.
- Newly committed type declarations: authored, compiler receipt open.
- Python finite certificates: finite mathematical diagnostics,
  not Agda kernel certificates.
- Classical classification metadata (7/14/32): implemented as
  enumerations, not full classification theorem.
- 230 space groups, Bloch Hamiltonian, space-group generators,
  NV sensor calibration: still open.

## Steelman
A common *typed symmetry/representation/gluing* abstraction can
make the existing DASHI mathematics much more reusable for actual
crystal classification, defects and spectral experiments.
The ambitious but defensible prediction is improved rigorous
interoperability, a calculable symmetry-reduction/search workflow
and explicit falsifiers. There is no claim that a generic 369
encoding by itself predicts new physical properties.

## Immediate next three independent max-cuts
(1) Compiler-grade finite source audit and real B4-native action
    inclusion, including correcting suspect #1261 proof terms.
(2) One end-to-end crystallographic realization instance for
    tetragonal 4/mmm and then diamond fcc, with actual lattice
    preservation; use this to test the new contract.
(3) Real symmetry-resolved physical operator for NV spin or a
    Bloch test Hamiltonian, citing original sources and preserving
    negative/counterexample obligations.

Thread attribution: source roots + chronology + actual owner +
proof status + independent physical corroboration are recorded
separately throughout. No donor PR contents are rewritten here.
