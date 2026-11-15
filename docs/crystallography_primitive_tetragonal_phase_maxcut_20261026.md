# PR #1261 — Max-cut closure of the primitive tetragonal lattice phase
2026-10-26. Source-attributed milestone; Agda compiler receipt open.

## Actual new implementation (not only documents)
1. `TetragonalIntegerMetricPairingExact.agda`:
   reuse native Agda integer ring solver to construct Z³ signed
   scalar and prove preservation of a universal weighted form
   B_{a,c}(p,k)=a(px kx+py ky)+c pz kz by the three tetragonal
   generators; use the existing all-D4h theorem to transport the
   result to all 16 normal forms. The parameters a,c are arbitrary
   integers; a positive-definite physical metric requires a,c>0
   and dimensionful unit conversion, which is separate.
2. `TetragonalFourierLatticeBridgeExact.agda`:
   exact round trips from native NSIntegerFourierLattice.FourierMode
   to integer triples, addition equivariance, all-D4h
   weighted pairing and Fourier-shell invariance.
3. `TetragonalSignedCoordinateGroupActionExact.agda`:
   independent-of-coordinate Agda proof clauses for the
   16×16 D4h composition law, sourced from classical Coxeter
   relations; finite enumeration is 256 cases, not a proof of
   a physical crystal specimen.
4. `TetragonalPrimitiveSeitzExact.agda`:
   actual infinite integer translation carrier Z³; Seitz
   product (g,t)(h,u)=(gh,t+gu); source-level identity,
   inverse and associativity witnesses; affine action
   identity and composition on lattice positions.
5. `TetragonalAtomicFourierRealizationExact.agda`:
   nontrivial test instance of `CrystalRealization`,
   with distinct direct-position wrapper and reciprocal
   FourierMode, native 369 AtomicIndex species, source-labelled
   tP/4mmm compatibility and momentum-shell rather than a
   constant spectral test observable.
6. `scripts/check_tetragonal_cubic_metric_stabilizer_exact.py`
   and `scripts/check_tetragonal_primitive_seitz_exact.py`:
   independently executable integer/group tests.

## External original sources
- International Union of Crystallography, *International Tables for
  Crystallography*, Vol A, space-group 123 P4/mmm, D4h^1:
  https://onlinelibrary.wiley.com/iucr/itc/Ac/ch2o3v0001/sgtable2o3o123/
  16 general positions, primitive tetragonal, generators include
  three primitive translations, 4-fold, mirror, inversion.
- Original diamond structure crystallographic source coordinates,
  fcc primitive basis and two-atom motif:
  https://lampz.tugraz.at/~hadley/ss1/crystalstructure/structures/diamond/diamond.php
  space group Fd-3m #227; no diamond operations added here.

## Exactly what the local checks establish
- Exact-integer local `tetragonal_integer_audit.py`:
  16 distinct signed matrices preserve diagonal tetragonal
  metrics and Euclidean Fourier index pairing.
- Exact-integer local `crystal_seitz_verification_1261.py`:
  D4h coordinate composition, affine Seitz product, identities,
  inverses, and all 4096 finite **representative** associativity
  group triples. This is independent finite corroboration.
- Symbolic coefficient-pair metric check confirms the stabiliser
  of generic diag(a,a,c) inside signed cubic B3 is D4h (16);
  when a=c it enhances to cubic B3 (48).
- No Agda compiler installed in this execution runtime.
  Source-level witness definitions and locally run Python
  audits are not Agda kernel receipts.

## Updated roadmap / phase gates

**Phase A — primitive tetragonal model: substantively assembled,
kernel gate OPEN.**
16-element D4h, Z³ direct/reciprocal and weighted pairing,
symmorphic affine translations with proof terms, nonconstant
spectral fixture, and species-labelled local-point consumer
all implemented. Remaining: actual Agda typecheck, fixing any
elaboration errors, more rigorous direct/reciprocal metric units,
and source-matched 16 Wyckoff/general-operation enumerations.

**Phase B — cubic/diamond physical crystal: next major scientific
max-cut.**
Promote existing B3/B4 Weyl operations to an actual fcc
Bravais lattice plus the diamond two-atom basis,
nonsymmorphic Fd-3m (#227) Seitz fractional translations
and site-orbit/stabiliser proofs. P4/mmm results are
reusable algebra, NOT diamond's own space-group operations.

**Phase C — atom/quantum consumers: important live donor path.**
Connect real diamond defect-site labels to the native
AtomicPeriodicTable369GenerativeExact and spin/fermion
carriers. Reuse NV four axes, spin-one Sz²/C3 obstruction
and multicore logical encoding (PRs #1238/#1262/#1270).
PR #1269 owns finite photon histories/Bayes/identifiability.
Only after a physical Hamiltonian/optical-forward bridge is
defined should these be welded to diffraction/ODMR data.

**Phase D — full classification and validation.**
32 point-group matrices, 14 Bravais metric instances, 230
space-group tables with origin/settings and Wyckoff data;
finite and spectroscopic experimental discriminators.
Generic hyperfabric, T4/T9/T18, 27→26→13→4 and
pants seam gluing remain useful supporting testbeds;
the XOR sign residual is NOT the programme's centre.

## Attribution and operational distinctions
IUCr and classical Fourier/Weyl theory remain the
mathematical source authority. DASHI earlier owner
modules and their original authors are preserved;
this PR authors only its new adapters/certificates.
Never identify a generic ternary digit carrier,
a Hamiltonian symmetry, a measured device,
or an unspecified Bravais lattice because of shared
cardinalities or the labels C3/111/13/27.
Physical band structure, NV sensitivity/advantage and
materials predictions remain experiment-gated.
