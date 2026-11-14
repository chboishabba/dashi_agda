# 2026-10-26 max-cut: from tetragonal 4/mmm to source-matched diamond Fd-3m

## Result of latest PR sweep
Reviewed current #1261, newest diamond #1269 photon histories and
count sufficiency, #1270 SAXON Q finite logical qutrit, #1262 NV
spin-one/C3 obstruction, #1249 native punctured27/projective13
orientation, #1239 finite modular/path/Jordan non-equivalences,
and #1115/#1076 material-specific Bloch/Seitz donors.
The mathematical maximum-Pareto choice was to instantiate the
physical diamond **fcc lattice** and **fractional Seitz glide**,
rather than spend another round on XOR or reproduce PG(2,3).
The original tetragonal 4/mmm (P4/mmm No.123) question remains
a separate, reusable source-owned exemplar.

## Implemented in this PR
- `DASHI/Mathematics/Symmetry/DiamondFccPrimitiveGlideExact.agda`:
  primitive cubic-quarter-coordinate fcc basis and diamond A/B
  two-sublattice site carrier; signed coordinate permutation
  primitive automorphisms; a genuine nonsymmorphic glide
  (flip-x plus a quarter-cell (1,1,1) offset) with the
  source-level theorem Gx² = translation (0,2,2);
  corresponding geometric position-equivariance lemmas.
- `DASHI/Mathematics/Symmetry/DiamondNVOrderedBondStabilizerExact.agda`:
  geometric threefold cycle and XY reflection satisfying C3v
  relations on *actual ideal diamond sites*, fixing an ordered
  A(0) to B(1/4,1/4,1/4) bond. Atomic 369 labels for
  nitrogen versus a typed vacant site (no fake atomic number 0).
- `DASHI/Mathematics/Symmetry/DiamondFccBccReciprocalExact.agda`:
  native ring-solver proof term for each bcc equal-parity
  reciprocal family pairing to a multiple of 4 with all
  primitive fcc translations; a genuine reciprocal-lattice
  inclusion with explicit integer winding witness.
- `scripts/check_diamond_fcc_glide_nv_bond_exact.py`:
  48 signed cubic linear operations and their diamond-compatible
  translation cosets; 192 distinct affine operations modulo a
  conventional cell, all 36,864 group products closed, exact
  eight-site motif preservation, 24 atomic-site versus 6
  ordered-[111]-bond stabilizers; three literal IUCr
  origin-choice-1 operation examples (2), (13), (25);
  exact reciprocal criterion over tested k and integer
  winding identities. These checks ran successfully in
  independent local Python using the same equations.

## Main exact structure and limits
Quarter-cell basis:
  F(u,v,w)=(2(v+w),2(u+w),2(u+v));
  diamond = F(Z³) ∪ ((1,1,1)+F(Z³)).
An x-glide Gx(x,y,z)=(1,1,1)+(-x,y,z) obeys
  Gx²(x,y,z)=(x,y+2,z+2).
Its square is an FCC translation, not the identity.
This is the first nontrivial *nonsymmorphic* crystal operation
in this thread, instead of the primitive tetragonal
symmorphic affine group alone.

Cubic symmetry sign-permutations G of order 48 have affine
translation t_G=(1,1,1) for odd number of sign reversals,
otherwise zero. Composition differs from this chosen
representative by an actual FCC translation. With four FCC
centring cosets mod the conventional cubic cell, there are
48×4=192 operations. This exactly matches the IUCr
general-position multiplicity of No.227. The code checks
that these operations preserve the eight ideal diamond
atomic positions, not just the affine multiplication table.

For reciprocal k in conventional 2π/a units, kx,ky,kz
have the same parity iff they pair integrally against all
three fcc primitive translations (in quarter-cell coordinates).
The Agda proof currently establishes the forward
equal-parity family inclusion with explicit factor-four
integer winding; the converse is covered by finite Python
tests, **not yet an Agda theorem**.

## External sources / original authorship
IUCr International Tables for Crystallography, space group
Fd-3m No.227, origin choice 1:
https://onlinelibrary.wiley.com/iucr/itc/A1b/ch2o3v0001/sgtable2o3o227/
Origin-choice-2 tables:
https://onlinelibrary.wiley.com/iucr/itc/Ac/ch2o3v0001/sgtable2o3o227/
Primitive FCC lattice and diamond structure:
https://aflowlib.duke.edu/p/A_cF8_227_a-001/
Classical group theory, fcc/bcc reciprocity and Seitz groups
are prior art, not original claims by DASHI. Code adaptation,
same-carrier proof bridges and local executable certificate
are the new PR contribution. Original atomic 369,
T9/T18, hyperfabric, NV and SAXON Q authors and PR
history remain separate and cited by owner.

## Updated Pareto roadmap
P0 (Immediate): repair and **typecheck** the new Agda
dependency cone locally or with an actual Agda compiler.
No requirement to focus on CI. Static Agda source and
Python exact checks are separate evidence stages.
P1 (Tetragonal): source-verified D4h/Z³/reciprocal/primitive
P4/mmm; confirm complete group, metric positivity,
origin settings and physical unit convention.
P2 (Diamond): B3 signed permutations and actual FCC
primitive basis/glide constructed; next formalise all
48 representatives and 192 Seitz operations *inside Agda*,
complete reciprocal BCC converse theorem, explicit site
multiplicity/Wyckoff and symmorphic-vs-nonsymmorphic no-go.
P3 (Quantum): instantiate group action on spin-orbital
Hilbert carrier and physical Hamiltonian (Bloch/fcc
tight-binding first), distinguish spatial C3v from the
proven non-C3 spin-one Sz² label permutation (#1262);
then connect qutrit multicore (#1270), NV optical
history/count/Bayes observer (#1269), and MCG (#1238),
each with sources, parameter/calibration/error receipts.
P4 (Generality): extend 7/14/32 labels into actual
verified lattice/point-group instances; authoritative
230-group operation tables, Wyckoff/origin and
magnetic/antiunitary operations separately.
Support only: T4/T9/T18, punctured nine and 27→26→13→4,
hyperfabric pants and optional binary sign residual
are excellent finite regression carriers, not the main
objective and not an identification with FCC physics.

## Quantified readiness / proof-status cut
- Primitive tetragonal P4/mmm: substantial source-level
  action/reciprocal/seitz formalisation, Agda verification open.
- Diamond Fd-3m: actual FCC+two-site motif and glide
  modeled, local exact operation census 192 passed; full
  Agda group quotient and compiler acceptance open.
- Actual NV defect: geometric ordered bond C3v source
  and typed N/vacancy decoration done; physical charge
  state, bond strain, Hamiltonian and spectroscopy open.
- Direct reciprocal: forward family factor-4 Agda term;
  full biconditional and Bloch phase characters open.
- 369 atomic programme: reused exactly as index owner,
  not confused with generated crystal properties.
- Native hyperfabric/PG13: consumed as prior-art
  comparisons, no duplicated implementation.
- Experimental diamond/SAXON sensors: distinct
  conditional published/device source evidence gates.

Most decisive upcoming experiment/proof: an actual
same-Hamiltonian C3v representation on the chosen
atomic defect Hilbert space, including strain and
Zeeman-breaking counterexamples, followed by a calibrated
photon observation/refinement discriminator.
