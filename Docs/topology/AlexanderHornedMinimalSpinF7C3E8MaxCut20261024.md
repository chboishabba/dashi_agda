# Minimal finite-field spin observer max-cut: 2I, C3, F7, Galois descent and full actor

Date: 2026-10-24. Repo PR #1244. Status: **explicit exhaustive finite
Python calculations**, new source/roadmap records, NOT geometric
wild-complement, physical Dirac or kernel-certified Agda proofs.

## Attribution and reused theorem owners

**Classical roots rather than original DASHI claims**
- Hamilton quaternion multiplication, Klein's binary icosahedral group
  and the unit-icosian/600-cell description (8+16+96 vertices).
- Choi and Lee (2018), *Binary Icosahedral Group and 600-Cell*,
  Symmetry 10(8) 326, DOI 10.3390/sym10080326:
  https://www.mdpi.com/2073-8994/10/8/326.
- McKay finite SU(2) groups/affine ADE representation graphs;
  see primary-style expository treatment in
  https://www.claymath.org/library/monographs/cmim04c.pdf.
- Maschke: finite group representation over a field of
  characteristic coprime to group order is semisimple.
- Standard quadratic finite fields and restriction of scalars.

**Prior actual DASHI owners** (do not relabel):
- `Algebra/FiniteQuaternionDoubleCover`: Q8 -> V4 central sign.
- `Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact`:
  literal rational Hamilton multiplication/norm.
- `Mathematics/Topology/AlexanderHornedQuaternionC3SpinExact`:
  chosen rational 120-degree q rotor, q^3=-1.
- `Foundations/BinaryPolyhedralMcKayDimensionExact`:
  numerical affine E6/E7/E8 dimension eigenvectors only.
- `Mathematics/Topology/AlexanderHornedC3MaschkeR3Exact`:
  rational spatial 1+2 Reynolds and cyclotomic plane.
- `Mathematics/Topology/AlexanderHornedC3Mod3JordanExact`:
  modular characteristic-three nonsemisimple test.
- `Mathematics/Topology/AlexanderHornedSpinVOAFactorFunctorExact`:
  rational pointwise 180->360 state pullback, not a Monster VOA.
- `scripts/alexander_horned_spin_icosahedral_bridge.py`:
  already had the literal 120-element SL2(F5) source
  and its 2:1 A5 quotient.

## Impasse 1: F7 Maschke does NOT give a 2D full-2I spinor

The complete finite actors are

  Qspin=(2I)^3 rtimes C3,    |Qspin|=5,184,000,
  Qproj=(A5)^3 rtimes C3,   |Qproj|=648,000.

Both orders are coprime to 7. Over F7 ALL finite-dimensional
modules are semisimple. However for n=1,2,3:

  |GL_n(F7)| = product_(j=0..n-1) (7^n-7^j)

is not divisible by five. The order-five elements in 2I
generate all 120 elements (checked by an explicit subgroup
closure). Thus ALL 2I->GL_n(F7), n<=3, are trivial.

In particular a faithful TWO-dimensional full 2I spin
representation over bare F7 cannot exist. This does not
contradict the F7 two-dimensional C3/2T spin rotor, nor
Maschke: a semisimple group may have no nontrivial modules
of a particular small dimension.

## Impasse 2 solved exactly: minimal faithful degree = 4

New `scripts/alexander_horned_icosian_f49_minimal_spin.py`:

1. Construct F49=F7[t]/(t^2-5); 5 is nonsquare in F7.
   The Frobenius automorphism sends t -> -t.
2. Define phi=(1+t)/2, phi^{-1}=phi-1.
3. Enumerate all 120 unit icosians:
   8 signed coordinate units, 16 Hurwitz half units, and
   96 even-permutation golden-ratio coordinates.
4. Verify all 120 exact norms=1, all 14,400 products are
   closed and exactly the identity/central -1 have square 1.
5. Split the quaternion algebra over F7 by explicit i,j
   matrices with i²=j²=-I and ij=-ji. All 14,400
   quaternion->M2(F49) products agree. Their determinants
   are 1, hence 2I embeds in SL2(F49).
6. Restrict scalars F49/F7: a faithful 2D spin
   representation becomes a faithful 4D F7 representation,
   and -1 maps to the literal -I4 matrix.
7. **SAME-GROUP WELD:** choose generating (2,3,5)-pairs
   in both source SL2(F5) and quaternion icosians; propagate
   assignments through all 120 group elements with exact
   consistency and verify all 14,400 multiplication pairs.
   This constructs the explicit isomorphism
       SL2(F5) ~= unit icosians over F49
   in our actual finite carriers, not by matching cardinalities.
8. Compare with 5-torsion prohibition at degrees 1..3.
   So degree FOUR is mathematically MINIMAL NONTRIVIAL
   over F7 (and our example is faithful).

No abstract 2I/horned exterior identity is inferred.
This remains a finite quotient of the ABSTRACT horn
commutator colimit, not the actual geometric exterior pi1.

## Impasse 3: genuine Galois-conjugate spinors

The two-dimensional F49 spin representation has character
values containing sqrt5. Their Frobenius transforms differ
on selected order-five group elements, so the representation
and its Frobenius conjugate are distinct at the character
level. The four-dimensional F7 scalar restriction extends
back to F49 as a pair of Frobenius-conjugate spin2 modules.

Our exact script checks Frobenius t^7=-t across all 49
field elements, all 120 traces and the exact F7/F49 trace
identity, with an order-five witness whose trace is
non-F7. This is a REAL coefficient-descent mechanism,
analogous in methodology to the repository's older
cyclotomic conjugate-pair owner but NOT an identification
of the two coefficient extensions.

## Impasse 4: full spin actor has a faithful 12D F7 action

The prior 4D representation rho:2I->GL4(F7) induces

   (2I)^3 rtimes C3 -> GL12(F7)

on THREE four-dimensional blocks. An element (a0,a1,a2;k)
permutes the blocks by i->i+k and applies rho(a_{i+k})
on the destination block. Its multiplication law matches
the existing `C3FiniteVOAActorExact` wreath/semidirect
coordinates. A block-permutation identity forces k=0;
faithfulness of rho then forces all three factors to
identity. Thus the full actor hom is FAITHFUL without
enumerating its 5,184,000 elements.

New `scripts/alexander_horned_full_actor_f7_spin12.py`
checks 18x18 selected 12x12 matrix products and each of
the 120 single-factor elements in all three blocks.
The diagonal central (-1,-1,-1) acts by -I12. This
is a much SMALLER genuine spin-sensitive full-actor
representation than the 360-site permutation model.

**IMPORTANT**: 12D faithfulness is proved; minimality of
12 for the entire wreath group is NOT proved.

## Impasse 5: six C3 x C2 eigensectors vs TWO central-sign full-actor projectors

In the 360-dimensional F7 permutation module
V=Fun(C3 x 2I,F7) there are two commuting operators:

  Z(i,g)=(i,-g) central under the FULL actor;
  T(i,g)=(i+1,g) the selected external C3 generator.

Define
  P± = (I±Z)/2
  Pk = (I+zeta^{-k}T+zeta^{-2k}T²)/3,
  zeta=2 in F7, k=0,1,2.

All six E_{±,k}=P±Pk are pairwise-orthogonal idempotents.
Every nonidentity element of the subgroup C2 x C3 acts
fixed-point-freely on these 360 sites, so each
tr(E_{±,k})=360/6=60 (ranks 60). The even/odd pieces
have ranks 180 each; they need not be irreducible under
the full group and may admit finer invariant decompositions.

**Promotion discriminator:** the P± commute with the
ENTIRE (2I)^3 rtimes C3 group, because diagonal -I is
central. Pk generally DO NOT commute with the full group:
C3 rotates the three nonabelian factors; explicit
nonuniform factor operators fail to commute with T.
The new exact
`scripts/alexander_horned_f7_spin_c3_projector_scope.py`
constructs a concrete counterexample and tests the
central-sign projectors on sampled full actors.

Thus the SIX smaller blocks are only C3 x C2-isotypic,
not full-actor submodules. Do not claim a full-group
3-character VOA decomposition by silently transporting
the subgroup projector.

## Geometry and physics boundary

Existing `AlexanderHornedC3OrbitSolidExact` proves that
the union of a seed's three translated point sets is
strictly invariant under rotation and that its complement
inherits a point-set C3 action. `C3SatellitePlacementExact`
even gives exact widely separated rational sites.

Neither constructs a WILD D3 embedding, the tame attaching
tubes/collars, or the desired three-copy complement pi1.
Consequently the new field-theoretic spin modules are
not geometric Dirac zero modes, a Monster V-natural
representation, the E8 Lie algebra, or an En operad.

The affine E8 correspondence for 2I is an irreducible
representation tensor GRAPH, not an identification of
this new faithful 4D F7 module with E8 roots. The
icosians' 120 unit-quaternion coordinates also arise
from the H4 600-cell, a different classification.

## Roadmap / phase / deliverables

COMPLETED with independent LOCAL exact Python:
- actual 120/120 SL2(F5)-icosian group isomorphism;
- full exact quaternion matrix products and degree-4
  minimality over F7;
- faithful order-120 spin-sign-sensitive F7 representation;
- Galois quadratic descent and distinct spin trace;
- faithful full 5,184,000-order quotient actor via 12D blocks;
- 360-state central ± projector and six rank-60 subgroup
  Fourier sectors, with explicit non-full-equivariance.

NEXT MATHEMATICAL MAX CUT:
1. Transport the 4D F7 spin module to an actual BIDI
   observer of the abstract horn group using the
   existing surjective G->(2I)^3 presentation. Distinguish
   sign-sensitive linear observer vs projective A5 actor.
2. For geometric relevance, provide stagewise invariant
   wild ball with collared attaching tubes and show the
   `R(B)=B` same-object assertion. Then establish actual
   pi1 via open covers and van Kampen.
3. If physical Dirac spectra are pursued, use a
   characteristic-zero smooth spinor bundle and choose a
   self-adjoint domain. F7 modular splitting is a
   finite algebraic control, NOT a physical state.
4. Only pursue a concrete McKay E8 representation-graph
   adapter when supplied with an actual irrep/tensor
   decomposition; dimension vectors alone do not suffice.

Per user instruction, Agda typecheck and CI are not
treated as current work priorities. They remain unclaimed.

## Additional same-meridian BIDI receipt (after initial report)

The locally executed `scripts/alexander_horned_f7_spin12_horn_meridian_bidi.py`
uses the SAME 2I root selected by the existing
`alexander_horned_spin_icosahedral_bridge.py`, including its
actual generating commutator children. Transporting that element
through the explicit finite SL2(F5)-to-icosian isomorphism and
the 12D full-actor representation gives

    rho_spin12(m^3) = diag(-I4,I4,I4) != I12,
    rho_A5(m^3) = 1.

This improves the earlier abstract non-descent into a
literal computationally executable quotient-to-linear
same-root example. It is not a geometric identification
of m with a loop of an actual wild complement.
