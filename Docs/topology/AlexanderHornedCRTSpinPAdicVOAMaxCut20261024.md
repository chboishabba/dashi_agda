# Horned C3 maximal reuse: binary/ternary CRT, pro-p congruence, 2I spin cover, nonabelian VOA

Date: 2026-10-24. Existing PR: #1244, keep DRAFT pending kernel.
Scope: actual abstract three-root injective commutator tower, and
its conditional wild-sphere geometric realization; NEVER conflate.

## Source roots and retrieved math

1. Alexander (1924) original wild sphere, Hatcher *Algebraic
   Topology* Example 2B.2 for actual one-root exterior
   injective commutator tower, perfect group and colimit:
   https://pi.math.cornell.edu/~hatcher/AT/AT.pdf
2. John Baez, binary icosahedral group: 2I=SL2(F5) (120) and
   2I/{+/-I}=A5 (60):
   https://math.ucr.edu/home/baez/icosidodecahedron/23.html
3. J. Herzig, *The mod p representation theory of p-adic
   groups*, §2: the congruence kernel GL_n(Zp) ->
   GL_n(Fp) is pro-p, with finite successive quotients
   M_n(Fp). Source cited at
   https://www.math.toronto.edu/~herzig/modpreptheory.pdf
4. Standard CRT/inverse limit:
   lim_n Z/(3*2^n) = Z/3 x Z2 (topological RINGS), due
   gcd(3,2^n)=1 and compatibility. See Cambridge
   profinite-group lecture notes:
   https://www.dpmms.cam.ac.uk/~grw46/LectureNotes2021.pdf
5. McKay (1980) / affine E8 dimension skeleton of 2I and
   established binary-polyhedral SU2 theory. McKay dimensional
   compatibility is NOT a group construction.
6. Serre; Fulton & Harris: existing SO3->A5->C3
   character restrictions, source attribution already present
   in DASHI. No A5->C3 homomorphism exists.
7. DHR/DR and Lie spin work: independent mathematical/physical
   sources, not a consequence of a finite horn quotient.

## Existing actual donors — reuse not reinvention

- Foundations.Base369BinaryTernaryRefinement: true 2^a3^b
  INDEPENDENT precision axes and commuting diamond.
- Foundations.NestedModularTensorLift: hex CRT and ternary
  lift; Arithmetic.SixWheelCRTExact: actual finite
  residue-6 bijection with Fin2 x Fin3.
- ComputerScience.BinaryBalancedTernarySubcarrierExact:
  lossless bit->strict {-1,+1} trit embedding (center unused).
- Codec.TriadicPAdicCylinderExact and
  Mathematics.Topology.AlexanderHornedBinaryPadicCylinderExact:
  exact prefix-refinement transport.
- Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact
  and Mathematics.Topology.QuaternionHopfUnitOrbitExact:
  exact rational quaternion norm, Hopf group action.
- Algebra.FiniteQuaternionDoubleCover: Q8 -> V4;
  Foundations.BinaryPolyhedralMcKayDimensionExact:
  affine E6/E7/E8 irrep-dimension SKETCH, not literal 2I.
- Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact:
  actual abelian Lie-torus restriction INSIDE SU2, not a
  universal inverse nonabelian reconstruction.
- Physics.QFT.FiniteDHRAbelianReconstructionReceipt and
  Physics.QFT.NonAbelianFusionFromSpin: conditional tensor
  upgrade under Rep(SU2) sector equivalence, NOT a sourced
  nonabelian group reconstructed from abelian observations.
- Physics.SFGC.NonAbelian.CliffordToM2Iso: four basis elements
  identified, not a general multiplicative algebra iso.
- Mathematics.Topology.AlexanderHornedAbelianHolonomyBIDIExact
  and AlexanderHornedProPSolvableBlindExact: compatible
  meridians invisible in any finite-derived-length target.
- Mathematics.Topology.AlexanderHornedC3FiniteVOAActorExact
  and AlexanderHornedC3VOAModeLiftExact: existing rational
  commutative pointwise VOA actor; q:F_3-root->A5^3 compatible
  source representation still needs exact-head certification.

## Break A — real CRT ring vs digit encoding

Symbolic wild-tip addresses:
    C3_ext x {0,1}^N = C3_ext x Z2.

Modulo binary prefix depth n, the classical CRT gives
    C3 x Z/(2^n) =~ Z/(3*2^n).
The maps from n+1 to n commute with the CRT construction,
hence the inverse-limit isomorphism.

The product C3 x Z2 is NOT the source exterior group G.
The external C3 rotates the root-sector coordinate.
A bit->balanced trit embedding is merely a CODEC, not
an additive hom from Z2 to Z3. The reverse fixed two-bit
trit code 00,01,10 for {-1,0,+1} has 11 unused, and is
likewise only a reversible codec on its image.

New Agda:
  Mathematics.Topology.AlexanderHornedMixedPrimeCRTWeldExact
constructs an actual HornCRTStage(n)=C3 x binary prefix n;
proves commuting forget-and-rotate operations, reuses
R23 resolution diamond and SixWheelCRTExact base CRT and
old binary-ternary embedding; adds a reverse exact
balanced-trit -> two-bits partial decoder with roundtrip.

New Python:
  scripts/alexander_horned_mixedprime_congruence_audit.py
exhaustively checks 6141 C3×binary-prefix states for n=0..10,
CRT inverse/compatibility, and general 2^a*3^b CRT for
1<=a,b<=4. All tests PASS in an independent local run.
This is a finite arithmetic receipt; a full *Agda theorem*
of CRT for EVERY depth remains an open consumer.

The true full mixed p-adic ring is Z2 x Z3, from the
two-axis inverse limit a,b->infinity. Our horned endpoint
chart fixes ternary exponent b=1, so is Z2 x C3.
These are not identical. No continuous additive group
isomorphism Z2->Z3; each is pro-p of a distinct prime.

## Break B — finite spin quotient closing A5/McKay/Q8 provenance

Previously the chosen A5^3 quotient erased the third power of
a root meridian mapped to a 3-cycle.

Take the literal matrix group
    S=SL2(F5), |S|=120.
In scripts/alexander_horned_spin_icosahedral_bridge.py
we enumerate all 120 matrices; show:
- exactly five Q8 subgroups, each order 8;
- normalizer of a selected Q8 has 24 elements (2T);
- conjugation on these five Q8 subgroups gives ALL 60 even
  permutations, with exact kernel {+I,-I};
- S has only one nonidentity involution (-I), so central
  extension S->A5 is NONSPLIT;
- an element q in the Q8 normalizer satisfies q^3=-I
  and q^6=I; conjugation cycles the 3 quaternion axes;
- all 120 S elements are commutators of some S pair;
- for this q, at least one commutator pair generates S;
- recursively choose finite commutator witnesses for every
  generator of the binary horn tree. Compatibility holds at
  every depth as a *mathematical constructive recurrence*;
  locally checked explicit stages n=0..5.
- By stage-one surjectivity (each root's two child images
  generate S), the resulting abstract three-root tower has
  a quotient onto S^3. Rotation permutes the factors, giving
    (G rtimes C3) -> (S^3 rtimes C3).
- The finite projective quotient is
    (S^3 rtimes C3)->(A5^3 rtimes C3),
  and the central sign is killed in the second step.

Unlike before we have a **two-level, nonabelian SAME OBJECT
quotient chain**, not just a similarity of symmetry orders.
For a root m mapping to q:
    image_S(m^3)=-I != I
    image_A5(m^3)=1.
Therefore the 2I observer distinguishes information lost
in the A5 observer; no source torsion is inferred.

The earlier rational Hurwitz rotor (1+i+j+k)/2 also has
cube -1 and conjugates Q8 with the same order-three axis
permutation, but a same-matrix isomorphism from that
particular rational quaternion group presentation to this
SL2(F5) matrix presentation HAS NOT been Agda-constructed.
Classical abstract 2I=SL2(F5) identity is externally known.
The selected matrix rotor q might differ by conjugacy
or signed choice from the rational one.

The earlier McKay E8 calculation is the nine-dimensional
irrep-node *dimension* skeleton: 1,2,2,3,3,4,4,5,6
(sum squares 120). No claim that the numerical skeleton
alone yields the literal binary icosahedral group.

## Break C — 360-dimensional finite VOA detects the spin sign

Let OmegaS=C3 x S (360 coordinates),
OmegaA=C3 x A5 (180 coordinates).

Both carry the existing rational commutative zero-charge
pointwise vertex-mode algebra (over complex scalars if
the conventional finite-dimensional C-VOA is required).

Pullback along
    OmegaS -> OmegaA, (i,g)->(i, g mod +/-I)
injects Functions(OmegaA,K) into Functions(OmegaS,K).

It preserves every pointwise vertex mode, vacuum, and the
finite-group action after transporting
    S^3 rtimes C3 -> A5^3 rtimes C3.

The spin delta-function at -I distinguishes -I from +I
on OmegaS; NO function pulled back from OmegaA distinguishes
those two. The actor-group quotient therefore has an
operationally grounded loss-of-spin-sign witness.

New Agda source:
    AlexanderHornedSpinVOAFactorFunctorExact.agda
takes an *actual* surjective factor-group hom with proof
fields and proves coordinate equivariance in all nine
phase/sector cases, mode preservation, right-action
intertwining and injectivity at every coordinate
WITHOUT assuming functional extensionality.

    AlexanderHornedBinaryIcosahedralSpinSignBidiExact.agda
uses existing ConsumerDescentMinimalObserverExact to prove
no recovery of central spin sign from the projective actor,
with concrete quotient data as the required witness.

These modules are source-written, NOT Agda-kernel verified.
The finite 120-element group / map is realized in Python,
NOT yet as an Agda group instance. The 360-coordinate
model is not the selected Monster V-natural module.

## Break D — integral p-adic rank obstruction (newly sourced)

Herzig's congruence theorem:
    1 -> K1 -> GL_n(Zp) -> GL_n(Fp) -> 1,
where K1 is pro-p (inverse limit of p-group reductions).

If G is perfect, every map G->any solvable group, hence
any pro-p group, is trivial. Thus a hom
    rho:G -> GL_n(Zp)
is trivial whenever the mod-p image rho_bar lies in a
SOLVABLE subgroup of GL_n(Fp).

In particular GL2(F2) and GL2(F3) are SOLVABLE.
The finite Python audit computes full derived series:
    GL2(F2): 6 -> 3 -> 1;
    GL2(F3): 48 -> 24 -> 8 -> 2 -> 1.
So there are NO nontrivial integral homomorphisms
    G -> GL2(Z2) or G -> GL2(Z3).
Similarly all rank-one integral characters are trivial.

Do NOT generalise this to all GL_n(Qp) representations:
unbounded image may not be conjugate into GL_n(Zp).
Do NOT generalise it to all n or all p: the 60/120
regular representations over every Qp survive.

`AlexanderHornedPadicCongruenceNoGoExact.agda` reuses
the old solvable-meridian theorem to prove that a separated
congruence actor whose finite-level target images are
solvable kills every meridian. A concrete Zp matrix
and separation model is not Agda-instantiated.
An exact SL2(F5) quotient is a mod-5 group, NOT
automatically an integral two-dimensional lift to GL2(Z5).

Also important: a representation into GL_n(Zp) with
trivial reduction mod p MUST be trivial, but a nontrivial
one need not be faithful when reduced; its kernel may be
nontrivial in a non-solvable finite-by-pro-p extension.
Avoid claiming reduction preserves every element.

## Why this actually changes priorities

The source group still has no finite p-group quotient
and has trivial pro-p completion for every prime. However
the full profinite completion is nontrivial (A5^3 and
now 2I^3 quotients), and nonabelian p-adic permutation
matrix observers remain possible. Pro-p visibility
is therefore much weaker than profinite/linear visibility.

The binary/ternary carrier, finite quotient, VOA and
p-adic representations are now organized as three
different arrows:

  endpoint address inverse system (topological/set)
  abstract horn colimit -> 2I^3 -> A5^3 (group)
  functions C3 x A5 -> functions C3 x 2I (mode algebra)

No SAME-OBJECT identification among these is implied
except the explicitly given factor and pullback maps.
The actual wild exterior still requires its collared
van Kampen/topological compactness proof.

## Acceptance and residual max cut

P0. Construct finite SL2(F5) group and 5-Q8-subgroup
conjugation action in Agda or reuse an already compiled
finite group owner; connect it to actual tower maps.
P1. Typecheck new Agda modules at exact head; repair
any algebraic import/type errors, add CI compiler receipts.
P2. Complete actual wild embedding collar cover, stage
fundamental-group inclusions and direct limit transport.
P3. Only when warranted, build a same-axis/group
intertwiner from rational quaternion 2T to this exact
SL2(F5) normalizer, and a selected 3B VOA consumer.
Do not equate E8 dimension signatures or 120/360
counts with physical identification.

Locally run equivalent full finite Python probes PASS:
- 120 SL2(F5), five Q8, 24 normalizer, 60 A5 quotient,
  120/120 commutators, root generation, horn stage n0..5;
- CRT 6141 mixed states, general two-axis CRT through
  exponents a,b<=4, GL2 derived series.
Committed scripts have CI entries, but NO GitHub Actions
Agda/Lean exact-head SUCCESS returned in this session.
PR #1244 remains draft.


## New literature-backed break: residual alternating finite quotients

Original source roots:
- The residual finiteness of finite-rank FREE GROUPS
  (classical theorem; e.g. Magnus/Karrass/Solitar).
- The Ore conjecture, proven by Liebeck, O'Brien, Shalev and
  Tiep, *The Ore conjecture*, JEMS 12 (2010), 939–1008,
  DOI 10.4171/JEMS/220, https://ems.press/journals/jems/articles/3979.
  Every element of each nonabelian finite simple group is
  a single commutator, in particular every A_n for n>=5.
- Their 2011 extension to finite quasisimple groups,
  DOI 10.1112/blms/bdr043, identifies exceptional covers;
  do not automatically assume every arbitrary central
  cover has universal commutator width one.

For any nontrivial element x in the ABSTRACT horn colimit
G, choose a free stage F_(3*2^n) containing a nontrivial
representative w of x (injectivity prevents collapse).
Because that finite-rank free group is residually finite,
there is a finite group H and a hom F_n->H distinguishing w.

Embed H into a finite alternating group A_m:
Cayley embeds H into S_|H|; the map S_d -> A_(d+2)
corrects odd parity by swapping two fresh points, and
is an injection. Increase m to at least 5 as needed.
So obtain a stage hom F_n -> A_m separating w.

Ore's theorem makes EVERY selected stage generator
image in A_m a commutator of two chosen elements.
Assign those two values to its two new horn generators
at stage n+1. The resulting hom F_(n+1) -> A_m
commutes with the commutator substitution F_n->F_(n+1).
Repeat indefinitely using finite choice on the finite
set A_m. The stage map thus extends uniquely along the
direct limit, giving q_x:G->A_m with q_x(x)!=1.

Consequences for the ABSTRACT source G:
  (1) G is residually alternating, hence RESIDUALLY FINITE.
  (2) The natural map G->its FULL profinite completion
      is INJECTIVE (stronger than merely nontrivial).
  (3) For every prime p, composing the family q_x with
      regular permutation matrices
        A_m->GL_(|A_m|)(Z)->GL_(|A_m|)(Qp)
      gives a FAMILY of finite-dimensional nonabelian
      p-adic matrix observers separating EVERY x!=1.
  (4) Each individual quotient may have a large kernel.
      No single finite-dimensional faithful GL_n(Qp)
      representation is established by this argument.
  (5) All pro-p completions remain trivial because
      alternating simple targets are NOT p-groups.
      No contradiction with faithful FULL profinite recovery.

Companion existing repo audit:
`scripts/alexander_horned_ore_residual_alternating_probe.py`
now exercises one finite A5 commutator section and four
extension stages. Its finite test is NOT a kernel proof of
unbounded residual separability, and the abstract proof
above still relies on the two credited theorems and
injectivity of the free tower.

The ACTUAL three-copy geometric complement still needs
its open-cover / van Kampen / compactness identification
with this abstract G before any geometric claim can be
promoted. The faithful family is a theorem about the
specified *abstract group*, NOT wild topology proved
by p-adic matrix numerics.
