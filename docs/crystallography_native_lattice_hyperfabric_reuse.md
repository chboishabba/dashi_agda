# Native lattice / hyperfabric reuse audit for crystallography

## Confirmed existing repository owners (read from master)

1. `DASHI.Physics.Closure.NSIntegerFourierLattice`
   [file `DASHI/Physics/Closure/NSIntegerFourierLattice.agda`]:
   exact `FourierMode` record with `kx ky kz : ℤ`,
   `addMode`, `negateMode`, and typed resonance equation.
   **Reuse:** integer coordinate carrier for reciprocal-wavevector
   actions; do not infer the material's direct lattice or metric.
2. `DASHI.Physics.YangMills.BalabanBlockedPeriodicLattice`:
   certified finite coordinate splitting
   `Cube4(M * L) ↔ BlockedCube4 M L`, built from `remQuot`
   and `combine`, with both round-trip proof terms.
   **Reuse:** multiscale finite periodic geometry / supercell-style
   charts. Note this is four dimensional, and no 3D crystal supercell
   equivalence is established until an explicit 3D specialization.
3. `DASHI.Reasoning.TypedHyperfabricCore`:
   typed stalks, incidences, restriction maps, compatible global
   sections, obstruction and provenance-preserving reorganisation.
   Original cited method: Duta, Cassarà, Silvestri and Liò,
   *Sheaf Hypergraph Networks* (arXiv:2309.17116).
   **Reuse:** multi-site atomic/field decorations, overlap consistency,
   provenance and symmetry-equivariant section candidates.
   Its sheaf-like carrier does *not* prove the axioms of a physical
   lattice, diffraction theory, or a full sheaf on a chosen site.
4. `DASHI.Physics.RootSystemB4Carrier` and
   `DASHI.Physics.RootSystemB4WeylAction`: exact 4D integer signed
   permutations. **Reuse:** actual Weyl parent for
   W(B2) × W(A1) via a 3-coordinate block with a frozen 4th.
5. `DASHI.Biology.D4NineCellOrbitCompressionExact`, T4/T9
   descent and T18 cyclic compatible boundary: **reuse** orbit,
   cover and gluing interfaces. They are not Bravais lattices.

## Newly committed
`DASHI.Mathematics.Symmetry.CrystalFourierLatticeD4hBridgeExact`
defines the three integer coordinate maps R,S,H on the existing
`FourierMode` type. No integer group law proof is asserted
without explicit negation/integer arithmetic lemmas and an Agda
typecheck receipt.

## Crucial geometry/reciprocal distinction

A direct lattice has basis B and translations Λ=Bℤ³. Reciprocal
wavevectors sit in Λ* = 2π B^{-T}ℤ³ (up to Fourier convention).
An orthogonal spatial symmetry A preserving Λ acts on direct
coordinates by U=B^{-1}AB ∈ GL(3,ℤ), and on reciprocal integer
coordinates by U^{-T}. On orthonormal cubic coordinates the two
often coincide, but in a non-orthonormal basis (e.g. hexagonal)
they cannot be identified silently.

Correct diagrams to formalise:
- direct integer action U on position integer triples;
- contragredient U^{-T} on reciprocal integer labels;
- Fourier pairing invariant under simultaneous action;
- hyperfabric section transport via group action on incidence,
  stalk values, and restriction maps, with explicit commuting squares.

## Crystal structure ownership split

(a) Seven systems, fourteen Bravais types, thirty-two point-group
labels are classification metadata. (b) A lattice metric and finite
integral automorphisms require proof. (c) A coloured/atomic basis
is a compatible hyperfabric section only after source-proven
incidence and species-labelled transport. (d) A space group uses
Seitz operations and translational cosets, not solely point-group
matrices. (e) A particular specimen requires independent physical
observation.

## Pareto tasks (all remain unless execution receipts exist)

1. Construct a generic `LatticeBasis3` and inverse transpose action;
   reuse the NS Fourier coordinate carrier and B4 signed permutation.
2. Prove exact tetragonal metric preservation for a=b>0 and c>0;
   distinguish primitive and body-centred Bravais cases.
3. Specialise the existing finite four-dimensional block decomposition
   to a typed three-dimensional supercell theorem.
4. Make a symmetry-equivariant hyperfabric incidence/restriction record,
   with compatible section transport and a provenance field.
5. Build Seitz semidirect algebra and nonsymmorphic extension data.
6. Instantiate group matrices for 32 point-group labels, then compare
   standard operations with versioned IUCr/spglib tables for all 230.
7. For each theorem, maintain source roots, local diagnostic status,
   compiler/kernel receipt and empirical identification separately.

### Attribution
IUCr classification, Weyl/Coxeter theory, Seitz operators, reciprocal
lattices, Maschke/Reynolds theory and Bloch/Fourier theory are established
prior art. DASHI adds typed adapters, formal proof terms and diagnostics.
No original authorship is transferred by a cross-module import.
