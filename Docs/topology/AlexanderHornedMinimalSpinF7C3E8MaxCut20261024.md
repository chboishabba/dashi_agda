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


## 2026-10-24 clopen-ball / real 3D gluing Pareto correction

We found significant prior art:
`Geometry/SSP369ClopenBallBridge`,
`Foundations/InverseLimitClopenRefinement`,
`Foundations/Base369PrefixUltrametricExact`,
`Foundations/CantorFiniteClopenPremeasureExact`,
`Foundations/CantorProjectiveCylinderMeasureExact`,
`Geometry/ProObjectSemantics`,
`Analysis/NonArchimedeanPadicCylinderBorelSourceExact`.

The real binary Cantor measure/finite clopen algebra owners
are more relevant than the ternary 3/6/9 authority tags.
In particular the old
`SSP369ClopenBallBridge.canonicalClopenAuthority`
uses label constructors, not a topological openness proof;
the old `InverseLimitClopenRefinement` stores
`intersectionSingleton : Set` and
`ultrametricComplete : Set` obligation fields, not
automatically inhabited certificates.

New `AlexanderHornedC3ClopenCylinderMassExact.agda`
welds the ACTUAL three-sector binary horn addresses with
the EXISTING Cantor cylinder mass, with exact
`1/(3*2^n)` normalization, child mass consistency,
rotation invariance, decidable finite prefix-cylinder
membership and complement, and cylinder nesting.
This is intrinsic wild-END topology, not an ambient
R3 ball or global decomposition of the CONNECTED exterior.
Indeed any continuous map from connected exterior
to totally disconnected K=C3×Z2 must be constant.

New local exact witness
`scripts/alexander_horned_clopen_linking_impasse_probe.py`
uses the same clopen address system for two different
3D link configurations with signed intersection-linking
numbers -1 and 0; the same oriented Hopf clasp can be
rotated into all 3 disjoint sectors with rational margin
proofs. The local linking witness is NOT Hatcher's
global perfect commutator tower/van Kampen receipt.

New local rational scaffold
`scripts/alexander_horned_clopen_tree_handle_scaffold.py`
uses the already source-defined 0 and 9e_i ball centres,
three axis-aligned radius-1/4 disjoint spoke cores and
a 4-vertex/3-edge C3-invariant TREE. Under genuine
collared topological B3 seed + tame attachments,
standard boundary connected sum yields a B3.
The wild satellite embeddings, attaching collars and
pi1 transition maps are still NOT constructed.

The old `AlexanderHornedC3OrbitSolidExact` ALREADY
makes any 3-phase seed orbit's set union R-invariant.
Hence the priority is no longer a standalone `R(B)=B`
conditional lemma, but constructing an actual embedded
wild topological 3-ball under that orbit and verifying
the complement Hatcher group via genuine geometric
van Kampen. Full audit/provenance/acceptance:
`Docs/topology/AlexanderHornedClopenBallGeometryMaxCut20261024.md`.

No Agda kernel/CI receipt claimed at user request.


## 2026-10-24 concrete geometry and OUTER-sector C3 improvement

Primary Hatcher Example 2B.2 pp171–172 inspected directly, with
the actual punctured-torus meridian commutator and injective
van Kampen stage maps. New source/technical roadmap:
`Docs/topology/AlexanderHornedThreeSectorGeometricVanKampenMaxCut20261024.md`.

**Source group identity now sharpened**:
`G_three = G_A * G_A * G_A` (free product), as an
independent three-copy filtered colimit of the Hatcher
free-stage commutator towers, NOT the direct product
`G_A^3`. `(2I)^3⋊C3` is its finite direct-product
QUOTIENT actor, consistent with the old 12D spin
representation. All-stage injectivity follows from
literal reduced-word fourfold expansion, as each
parent's two child letters occupy a disjoint alphabet.
Independent local audit checked 18,112 reduced words,
including exact sector-rotation commutation.

**ABSTRACT outer-action CLOSED**:
the C3 permuting the three free factors has exact
order 3 in `Out(G_three)`. Proof: retract onto
factor zero; rotated nontrivial factor-zero meridian
becomes identity, whereas the retraction of ANY inner
conjugate remains a nontrivial conjugate.
The SL2(F5) meridian witness and 120/120 conjugate
check are in
`scripts/alexander_horned_three_sector_outer_c3_witness.py`.
Only its geometric `Out(pi1(exterior))` incarnation
awaits an equivariant pi1 same-object isomorphism.
This is POSITIVE outer symmetry progress, not an
asserted nonsplit central spin cover of C3.

**Concrete geometric bug corrected**:
previous radial thin-spoke cores t∈[1,8] merely
TOUCHED the central and satellite unit spheres;
they did not define an attached 1-handle!
Patched original
`scripts/alexander_horned_clopen_tree_handle_scaffold.py`
to cores t∈[1/2,17/2], radius 1/4.
Each full endpoint disk is inside the relevant unit ball,
with radius² 5/16 <1; exposed tube components remain
disjoint. Scaled outward Hopf/unlinked loop pairs
fit INSIDE unit satellites without meeting spokes.

**Genuine Euclidean clopen control, not tags**:
`scripts/alexander_horned_tame_cantor_ball_cylinders.py`
constructs strictly nested actual 3D balls for every
binary cylinder with child containment margin >0 and
positive sibling separation at all depths, as a
TAME comparator. 511 finite cylinders checked. Its
identical symbolic `C3×Z2` ends do NOT force wildness
or exterior π1, a key topological discriminator.

NEXT P0: source-specific Hatcher wild satellite B3
with its actual tame attachment disk/collar. Distinct
from the standard unit satellite BALL geometric overlap
now checked. Then splitting spheres and an actual
simply-connected-overlap van Kampen for the full
threefold exterior. User requested local Python rather
than Agda/CI, so no new kernel claim.


## 2026-10-25 source-supported inward cap + literal separator sphere breakthrough

**Primary-source progress:** Franca Lippert, *The Alexander Horned
Sphere and Bing's Hooked Rug*, §2.1–§2.2 (Figure 2, pp. 2–4),
https://www.maths.gla.ac.uk/~mpowell/WriteUp_Franca.pdf,
describes horn-stage homeomorphisms becoming the identity
away from shrinking attachment support; the wild sphere is
locally flat off its Cantor ends. Hatcher, *Algebraic Topology*,
Example 2B.2, pp. 170–172 gives the genuine individual
exterior meridian/commutator van Kampen group.

Consequently we can choose a classical supported Alexander
construction that leaves an initial round B0 inward cap
unchanged. New
`scripts/alexander_horned_supported_stable_cap_certificate.py`
checks explicit coordinates for B0 radius 3/4 in a unit
reference satellite:
  Phi(u,v,s)=(-sqrt((3/4)^2-u²-v²)+s,u,v),
  u²+v²<=1/16, |s|<=1/8.
It is a genuine local TWO-SIDED collar with an inverse
chart, not a symbolic `ClopenWitness` label.
The corrected spoke endpoint t=8.5 with disk radius
1/4 has squared satellite-centred norm 5/16<9/16,
so overlaps the ACTUAL cap-preserved wild B0, not
merely the outer reference unit container.
The local exact script passed 797 rational chart tests.
The source-supported infinite horn attachments still
have to be instantiated to declare an executable
infinite-coordinate embedding.

A much sharper geometric van Kampen separator is now
available: three literal disjoint spheres
  S_i={|x-9e_i|=4}.
Their *only* contact with the constructed solid is the
respective straight spoke, and on each sphere the
intersection is the single transverse disk GRAPH
  t=9-sqrt(16-u²-v²),   u²+v²<=1/16.
Its near axial range is 5<=t<8.5. The far root
is outside the tube; all other reference balls/tubes
lie beyond the sphere. Radius-1/4 collars around the
three S_i are disjoint. New
`scripts/alexander_horned_three_sector_separator_spheres.py`
and an independent exact-Fraction local equivalent
passed 197 rational cross-sectional checks; all-radius
claims follow from exact monotone square-root bounds.

Thus `S_i∩E=S²\closed(D²)`, an OPEN DISK, so the
exterior open-cover overlap is simply connected.
This is the proper geometric van Kampen cut; a PLANE
minus disk would instead have pi1=Z and must not
be used as though it were simply connected.

New comprehensive source-attributed proof note:
`Docs/topology/AlexanderHornedSupportedCapSeparatorVanKampen20261025.md`.
It spells out how a threefold collared boundary
connected sum can yield B3 and, using the standard
unknotted-tree-neighbourhood/side-cap equivalences,
`pi1(E)=G_A*G_A*G_A` with outer C3.
This is a **paper-level source-supported geometric
proof scheme** with exact local geometry; the native
infinite horn support map and all ambient deformation
retractions are NOT machine-proved or explicitly
coordinate-constructed in the repo.

This discharges the earlier vague *existence of a tame
cap as an unexplained input* by pointing to and using the
actual supported original horn construction. The
remaining max-cut is no longer 'find separating spheres',
but instantiate its *supported infinite attachment*
and the complement-piece homeomorphisms as concrete
same-object maps. No Agda/CI work per user request.


## 2026-10-25 roadmap reset: FINITE vs INFINITE physical observables

New source-audited decision report:
`Docs/topology/AlexanderHornedRoadmapRealWorldImplications20261025.md`.

**Critical Hatcher object discriminator:** `B_n` is a
locally-flat/tame finite horned BALL with simply connected
exterior (Schoenflies), whereas Hatcher's stage enclosure
`X_n` is a genus-`2^n` handlebody with nontrivial
exterior `Y_n` and `pi1(Y_n)=F_(2^n)`.
For three independent sectors, stage group rank is
`3*2^n`. The ideal limit `B=intersection X_n` is
the source of the perfect but nontrivial exterior group.
Do NOT use a finite printed B_n and falsely advertise
the complement group of X_n or the ideal limit.
Original: Hatcher Example 2B.2 (printed pp171-172)
and locally-flat Schoenflies.

**Essential noncommutation of limit/abelianization:**
Each source meridian becomes a child commutator, so
H1(Y_n)->H1(Y_(n+1)) is the ZERO map despite each
H1(Y_n)=Z^(3*2^n). Thus H1(E)=0 while
pi1(E) is nontrivial. In R3 the exterior also has
H2(E)=Z from the sphere at infinity; in S3 the
complement of the compact contractible ball is
reduced-acyclic. Do not call R3 exterior fully acyclic.

**Flat U1 vs nonabelian holonomy**:
Hom(perfect G,U1)=1; each isolated finite free stage
has nontrivial U1 characters that cannot be carried
compatibly through all commutator refinements.
In contrast existing 2I=SL2(F5) perfect quotient
has an order-six root q with q^3=-I, recursively
compatible child commutators and spin-character
Wilson trace -2. Nonflat Maxwell connections can
still have Wilson loops on contractible paths.
A one-level Q8 commutator [i,j]=-I works, but
Q8 cannot extend recursively: [Q8,Q8]=C2.
The perfect 2I target is essential for ALL scales.
Executable finite audit:
`scripts/alexander_horned_scale_holonomy_maxcut.py`.

**Actual experiment/control roadmap:** finite sculpture,
finite X_n handlebody, and unlinked/tame controls must be
labelled DIFFERENT specimens. A synthetic SU2/optical
control circuit may implement recursive commutator
identities and observe relative Wilson phases; this is
not direct observation of the infinite wild pi1.
Prior published physical feasibility roots: Lucien
Grillet's FOUR-level 20cm PLA/PVA horned sculpture,
Bridges 2022; Q. Liang et al. Nature Physics
(2024), DOI 10.1038/s41567-024-02644-4
synthetic SU2 nonabelian AB in a 1D ladder, and
Sugawa et al. npj Quantum Information (2021)
nonabelian Wilson-loop measurements.
No original DASHI experiment currently exists.

**Quantitative synthetic signature:**
`scripts/alexander_horned_su2_controls_noise_probe.py`
verifies exact quaternion algebra
`tr([A,B]) = 2-4 sin²(alpha) sin²(beta)` for
orthogonal-axis SU2 controls; at alpha=beta=pi/2
this is -2 versus commuting U1 +2. Angular control
errors change the trace; a lone global -1 spinor sign
must be measured against a reference. One SU2
commutator does not prove the whole tower's perfectness.

**Hard acceptance gates:** actual supported Hatcher
infinite horn coordinates and cap, the three piecewise
open-cover/van Kampen homotopy maps, CAD models with
known finite stage group, calibration/flatness controls,
specified Maxwell/Dirac operator and boundary data.
No implication of gravity anomalies, free energy,
superluminal communication, quantum consciousness or
new physical zero modes.

The work priority is a dual track: geometry source
same-object closure plus practical finite nonabelian
control experiment; defer Agda typecheck/CI by request.
