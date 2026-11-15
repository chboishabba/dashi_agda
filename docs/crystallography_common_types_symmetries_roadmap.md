# Crystallography shared classification max-cut: reuse, not duplication

## External source authority and attribution
- International Union of Crystallography, *International Tables for
  Crystallography*, Volume A, *Space-Group Symmetry*: authoritative
  terminology and classification for 7 crystal systems, 14 Bravais
  lattice types, 32 crystallographic point-group types, 230 ordinary
  three-dimensional crystallographic space-group types.
- IUCr (2018), "Crystallographic shelves: space-group hierarchy
  explained", Journal of Applied Crystallography:
  https://journals.iucr.org/j/issues/2018/05/00/in5013/
- IUCr (2010), "How to read (and understand) Volume A of International
  Tables for Crystallography: an introduction for nonspecialists":
  https://journals.iucr.org/j/issues/2010/05/02/kk5061/
- Older crystallographic discoveries, group classifications, invariant
  theory and Weyl/Coxeter results stay attributed to their original
  mathematical and crystallographic sources. This repository does
  not claim to discover the seven/fourteen/thirty-two/two-hundred-thirty.

## Native implementation owners
- `DASHI.Physics.RootSystemB4Carrier` defines `B4Point = Vec ℤ 4`.
- `DASHI.Physics.RootSystemB4WeylAction` defines 24 explicit
  coordinate permutations and signed-coordinate flips.
- `DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact`
  independently contains a B4 orbital-grid application.
- `DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact`
  represents classical W(B2)×W(A1), not all of B4.
- `DASHI.Biology.D4NineCellOrbitCompressionExact` and trialectic
  T4/T9/T18 modules are alternate action carriers, not identified
  with spatial lattices by cardinal coincidence.

## Completed classification scaffold in this PR
- `CrystalClassificationSevenFourteenExact.agda`: typed seven systems,
  fourteen conventional 3D Bravais labels and their system mapping.
- `CrystalPointGroup32CatalogExact.agda`: 32 point-group labels
  divided by system (2,3,3,7,5,7,5); `4/mmm` explicitly maps to
  tetragonal. The catalogue does not forge matrix group certificates.

## A correct full formalisation architecture
1. **Integral lattice**: basis B in GL(3,Q) and lattice Λ=B Z³,
   metric tensor M=BᵀB; certify positive-definiteness and admissible
   centring cosets. Point-group compatibility needs gΛ=Λ.
2. **Point group**: finite subgroup G of O(3) with integral action
   in lattice coordinates; track Schoenflies/Hermann–Mauguin symbols
   as labelled metadata, not the proof of group equality.
3. **Symmorphic space group**: Λ ⋊ G only where a lattice-preserving
   action is constructed. Distinguish a semidirect product from an
   arbitrary space group: nonsymmorphic screws/glides require Seitz
   translations and extension/cocycle data.
4. **Affine operations**: Seitz pairs (R,t), multiplication
   (R,t)(S,u)=(RS,t+Ru). Translational equivalence, origin shift,
   conjugacy and standardized setting are separately typed.
5. **Basis / orbit**: fractional atomic positions and species labels,
   Wyckoff multiplicities, stabilisers and orbit decomposition.
6. **Evidence**: predicted symmetry vs measured diffraction/morphology,
   material-specific provenance and uncertainty.
7. **Optional extensions**: magnetic/Shubnikov, colour/spin-space,
   superspace, quasicrystal/cut-and-project, and external Fourier
   experiments; never flatten into the 230 ordinary groups.

## Pareto completion order
- First transport the already-written signed-permutation B4 donor into
  the tetragonal B2×A1 inclusion by explicit coordinate embedding.
- Then build cubic W(B3), orthorhombic C2³, hexagonal D6 and trigonal
  D3 as faithful lattice actions; use G2/A2 root subsystems only with
  actual rank-two lattice charts. (D6 also relates to W(G2).)
- Next full 32 point-group matrix representatives and lattice
  compatibility predicates, using IUCr source classifications.
- Then 14 Bravais metric/centring checks and Seitz multiplication.
- Finally validate the 230 labels/operations against a versioned
  trusted crystallographic data table (for example spglib or
  IUCr setting) with attribution and machine-readable receipts.
  A 230-entry data import is not itself a kernel-level exhaustive
  classification proof.

## Current proof status
The seven/fourteen/thirty-two labels are source-attributed
definitions. They have not been typechecked in this session.
The D4h finite matrix construction has independent Python checks,
while its exhaustive Agda proofs still lack an Agda compiler receipt.
This roadmap is not a claim of 230 groups formalised.
