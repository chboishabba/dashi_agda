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


## 2026-10-24 strict Spin(3) 360/720 cover audit

The precise standard theorem is **Spin(3)=SU(2) -> SO(3) TWO-to-ONE**.
SO(3) rotations themselves close at **360deg/2pi**. The
identity-starting path lift of a full 360deg rotation ends at
the central quaternion `-1` (not `+1`), so spin-half
amplitudes close at **720deg/4pi**. This is why a 360deg
SO(3) *loop* is noncontractible even though its endpoint
is the identity rotation; the doubled 720deg loop is
contractible. `pi1(SO3)=C2` is NOT `pi1(horn exterior)`.

Previously established owners:
- `Foundations/SU2SO3IrrepDimensionExact.agda` proves the
  spin-half highest-weight-one representation does not
  descend to SO3 and integer-spin even-weight lane does.
- `Algebra/FiniteQuaternionDoubleCover.agda` has exact
  kernel/fibres for FINITE `Q8->V4`, not the full continuous
  SU2->SO3 cover.
- `Algebra/CliffordSpinLift.agda`, `Physics/SpinAssumptions.agda`,
  `Algebra/ContinuousSpin31LorentzCover.agda` carry
  conditional/status/other-signature interfaces; these
  are not completed topological double-cover proofs.
- `AlexanderHornedQuaternionC3SpinExact.agda` already
  proves q=(1+i+j+k)/2 has `q^3=-1` and
  `(-q)^3=+1`, with both inducing the *same actual*
  120deg spatial map.

NEW exact finite witness owner
`AlexanderHornedSpin360720Exact.agda`
reuses Q8->V4, proves `rho(-1)=rho(+1)`,
`-1!=+1`, `(-1)^2=+1`, `i^2=-1`,
and imports the pre-existing spin-half descent and
threefold horn rotor theorems. Reproducible exact
Fraction audit: `scripts/alexander_horned_spin_360_720_audit.py`.
It does NOT construct the universal-cover path-lift
theorem or the geometric horned pi1.

Full source/proof boundary:
`Docs/topology/AlexanderHornedSpin360720CoverAudit20261024.md`.

**Number trap**: the 360-coordinate finite spin VOA
`Fun(C3×2I,Q)` has vector-space dimension 360,
which has NOTHING to do with the 360-degree SO3
period. Its 180-coordinate A5 quotient likewise
is NOT a half-turn interpretation.


## 2026-10-24 C3 steelman: strict spin action versus 720-degree angular path

See canonical attributions, exact data and proof-status ledger:
`Docs/topology/AlexanderHornedC3SpinLiftSteelman20261024.md`.

**P0 mathematical break:** restricting Spin3->SO3 to the
actual 120deg C3 subgroup gives a SPLIT central extension
`C6 ≅ C3×C2`, since `H²(C3,C2)=0`. The old rational
quaternion `q=(1+i+j+k)/2` (order 6, q³=-1) is the
identity-started +120deg PATH lift, NOT a homomorphic C3
generator. The same rotation's other lift `-q` has
order 3, giving a genuine spin-equivariant C3 action.
Neither lift changes the torsion-free source exterior G.

**Agda exact source:** `AlexanderHornedC3SpinLiftSplitExact.agda`
reuses EXISTING `FiniteC3OrbitStabilizerExact`, Q8 signs
and ambient horn C3. It constructs the six-element spin
preimage, a strict homomorphic C3 section, unique
order-three generator lift, a nonhomomorphic path-section,
and proves by all nine cases that the path's central
carry cocycle is an EXPLICIT coboundary.
No continuous covering-space Agda kernel certificate
has been created.

**A same-coordinate Dirac field consumer exists** on ANY
C3-invariant open subset E of R3:
`Tψ(x)=U(-q)ψ(R^-1 x)`,
`T³=1` and `DT=TD` on
compactly supported two-component spinors.
The Gaussian-rational `spin_dirac_probe.py` checked
all three Pauli/Dirac coefficient identities and
125 exact finite position/spinor samples.
This requires `R(E)=E` for the *actual* wild
embedding, not a completed fundamental-group theorem,
nor any spectral domain/self-adjointness statement.

**Fixed-axis and characteristic-3 discriminator:**
`tr(U(-q))=-1`, `det(U(-q)-I)=3`; fixed-axis
C3-invariant spinor values vanish in characteristic
zero. On each free 3-position orbit with two spin
components, the exact averaging projector
`P0=(I+T+T²)/3` is idempotent of rank 2.
The Q3 2D cyclotomic block has zero fixed dimension,
whereas reducing it modulo 3 yields a unipotent
representation with a 1D fixed subspace. This is
Maschke failure, not a new characteristic-zero zero
mode or Monster eigenspace. The existing C3Fourier/
C3CyclotomicRealDescent/3B projector owners are
literature/technique donors, NOT the same spinor operator.

**Spinor MODULE over SAME finite scalar VOA:**
`V=Fun(C3×A5,Q)` has 180 scalar sites;
`M=Fun(C3×A5,H_Q)` has 720 rational coordinates.
It admits a right-Q(i) spinor complex structure,
yielding 360 dimensions over Q(i), which is NOT
`Fun(C3×2I,Q)`, the distinct old 360-site spin
charge algebra. For `g=(a,k)`, spinor right pullback
is `r^k ψ(g.x)` with r=-q, and preserves scalar
pointwise vertex-module multiplication. The existing
finite semidirect actor is reused. The finite
`spin_voa_module_probe.py` checked 18 sampled
actors, 18x18 group pairs, 180 sites and sign
periodicity. No Monster-VOA module is identified.

**Full A5 global obstruction still non-split:**
`2I->A5` remains globally non-split even though
its restriction to any C3 subgroup splits. Hence
C3 alone is NOT a test of the global spin Schur
class. Continue using an actual 2I/A5 same-object
map for this, not an order-three phase analogy.

Independent local finite probes PASS, CI files updated,
but no successful exact-head Agda/Lean workflow
receipt returned. The geometric `R(B)=B` and
van Kampen identification remain open.


## 2026-10-24 decisive follow-on: SAME quaternion spin matrix and full F7 actor

**Stronger actual same-object representation owner**
`DASHI/Mathematics/Topology/AlexanderHornedC3SpinCyclotomicIntertwinerExact.agda`
reuses the LITERAL Cayley-Dickson rational Gaussian-complex
and rational quaternion carriers. Let q=(1+i+j+k)/2,
V=U(-q) in the standard Gaussian 2x2 quaternion realization,
and A=[[0,-1],[1,-1]]. The explicit invertible change-of-basis
matrix and its inverse are

    T    = [[1, -(1+i)/2], [0, (1-i)/2]],
    T^-1 = [[1, i],       [0, 1+i]].

The new owner proves V*T = T*A and both inverse laws
by componentwise rational polynomial identities.
An independent local exact Gaussian-rational probe
also passed modulo 3, 5 and 7 (over the corresponding
Gaussian quotient algebras). Since det(T)=(1-i)/2
and its norm is 1/2, T remains invertible modulo
every odd prime. This **pays** the former same-carrier
gap between the actual Horn coherent quaternion rotor
and the cyclotomic companion field-comparison matrix
at odd characteristic. p=2 is deliberately excluded.
Script:
`scripts/alexander_horned_c3_spin_cyclotomic_intertwiner_audit.py`.

**Full finite-group Maschke break** is stronger than
the C3-only character calculation:

    Gprojective=A5^3 rtimes C3, |Gprojective|=648000
    Gspin=2I^3 rtimes C3,      |Gspin|=5184000.

Both orders are 3 modulo 7. Therefore **Maschke applies
to every linear representation of BOTH full actors over F7**.
In characteristic 5, C3 alone is semisimple, but the
full A5 and 2I actors are modular. In characteristic
2 the central spin sign collapses. Characteristic 7
is thus the smallest prime simultaneously avoiding
2,3,5, preserving +/- spin, and allowing full finite
spin/projective-actor semisimplicity.

NEW exact arithmetic owner
`AlexanderHornedC3F7FullActorMaschkeExact.agda`
proves both group orders and their division-with-remainder
formulas, the 180/360 coordinate double-fibre identity
and its rational normalized mean coefficient.
Maschke's theorem itself is attributed to the pre-existing
pinned mathlib/classical source; not falsely reconstructed
as a new Agda theorem.

**Same finite module / projector diagram:**
with pi:OmegaS=C3x2I -> OmegaA=C3xA5 (2:1),
the uniform average on either function space over F7
is the projection to constant invariant functions.
Each finite group acts transitively on its coordinate set.
Since 180 mod7=5 and 360 mod7=3,

    180^-1 = 3 mod7, 360^-1 = 5 mod7,
    2 * 360^-1 = 180^-1 mod7.

Therefore for EVERY f on OmegaA,

    P_S(pi^* f) = pi^* (P_A f).

The full finite SL2(F5) quotient, five Q8 subgroups,
360->180 fibre counts, normalized averages and
group translations were checked independently with
exact finite arithmetic:
`scripts/alexander_horned_c3_f7_full_actor_reynolds.py`.
This is a genuine equivariant, mode-compatible finite
algebraic result, not a claim that the actual selected
Monster VOA or physical Dirac spectrum is realized.

Proof levels: these three new Agda modules are SOURCE
WRITTEN, not exact-head kernel checked. The scripts
were independently reproduced locally and committed.
Geometric horned R(B)=B, analytic Dirac domains,
and 3-copy exterior pi1 are still independent gates.


## 2026-10-24 actual Maschke-where-it-applies cut

Do NOT treat the split C3 cover as a 'negative result' we ever
sought. It is already paid by
`AlexanderHornedC3SpinLiftSplitExact.agda`.
The productive question is whether the SAME horn rotation
action admits Maschke projectors and nontrivial semisimple
spin/sign observations under a controlled change of field.

Actual previous donors reviewed:
`C3CyclotomicRealDescentExact`,
`C3FourierConjugationExact`,
`R3HodgeCrossExact`,
`SpinorRepresentationReceipt`,
`IbrahimMonster3BWholeCharacterIsotypicBypassExact`
and `BinaryPolyhedralMcKayDimensionExact`.

NEW source-written term-level rational owner:
`AlexanderHornedC3MaschkeR3Exact.agda` uses the existing
`Ambient.rotateXYZ` on the SAME triple coordinates,
constructs and proves the Reynolds idempotent
`P=(I+R+R²)/3`, proves vector = invariant diagonal +
sum-zero transverse residual and identifies the literal
transverse companion matrix `[[0,-1],[1,-1]]`.
It bridges the old symbolic 1+2 cyclotomic record without
assuming a nonexistent general ℚ-to-ℝ equivalence.

Finite exact modular comparison:
`scripts/alexander_horned_c3_maschke_field_comparison.py`.
Over F3 the transverse cyclotomic polynomial becomes
`(X-1)^2`; `(A-I)²=0`, invariant line is NOT a
direct summand, and the 3-site Reynolds sum is nonzero
nilpotent. Over F5 the module is irreducible semisimple;
over F7 it splits into 1D eigencharacters 2 and 4,
with **explicit orthogonal rank-one projectors**.
Over F2 it is also semisimple but spin -1=+1 disappears.
This is a representation-theoretic phenomenon, NOT a
physical Dirac zero mode.

**Stronger entire-actor answer:** char 7 divides neither
`|A5³⋊C3|=648000` nor `|2I³⋊C3|=5184000`,
so Maschke applies to EVERY finite module for BOTH complete
groups. `scripts/alexander_horned_c3_full_actor_maschke_f7.py`
reuses the 120->60 literal SL2(F5)->A5 map and tests the
180/360 coordinate pullback and 2-to-1 central-sign
averaging `(f(x)+f(-x))/2`, which yields an invariant
even/odd 180+180 splitting over F7. The older independent
full-actor local equivalent test PASSED. Exact new script
will run in the focused CI; no successful Agda receipt.

McKay nuance: binary 2T/2O/2I give affine E6/E7/E8
representation graphs, not a direct group map
`C3->E8`, not the separate `3^n` En-hyperfabric
and not a Monster VOA physical realization. Original
source: Kostant 1984 PNAS; classical McKay 1979/1980.
See full attribution and proof-gate roadmap at
`Docs/topology/AlexanderHornedC3MaschkeR3E8CrossCut20261024.md`.

Remaining high-value cut is an executable Agda kernel
receipt and genuine same-object geometric R(B)=B for
the exact embedded horned ball, NOT another abstract
C3 split-obstruction proof.


## 2026-10-24 completion: MINIMAL F7 spin4, faithful wreath spin12, scope of C3 projectors

The constructive bottleneck beyond ordinary Maschke has now been
paid in the exact finite witness library:
`Docs/topology/AlexanderHornedMinimalSpinF7C3E8MaxCut20261024.md`.

- `scripts/alexander_horned_icosian_f49_minimal_spin.py`
  constructs F49=F7(sqrt5), 120 golden-ratio unit icosians
  (8+16+96), their 2x2 determinant-one matrix algebra,
  scalar-restricts to faithful GL4(F7), and builds the
  *ACTUAL SAME GROUP* bijective map to existing SL2(F5)
  using (2,3,5) generators and all 14400 products.
  Central -1 acts as -I4. No rank <=3 representation
  of 2I over F7 can be nontrivial, because order-5
  elements generate 2I and 5 divides none of
  |GL1(F7)|, |GL2(F7)|, |GL3(F7)|.
  Thus 4 is the MINIMAL nontrivial F7 degree.
- The 2D spin actor exists over F49 and its Frobenius
  conjugate has a genuinely different order-5 trace;
  restricting scalars gives the 4D F7 module.
  Do NOT claim a 2D full-2I spin representation over
  bare F7 from the earlier C3/2T rotor example.
- `scripts/alexander_horned_full_actor_f7_spin12.py`
  builds a faithful GL12(F7) block-monomial representation
  of (2I)^3 rtimes C3: the C3 block permutation reveals
  the phase, each faithful GL4 block reveals one factor.
  The diagonal central (-1,-1,-1) maps to -I12.
  Faithful 12D is proved; **minimal 12D is NOT asserted**.
- `scripts/alexander_horned_f7_spin12_horn_meridian_bidi.py`
  welds the PREVIOUS actual commutator root q of the
  binary Hatcher source to the new SAME 2I quotient:
  m^3 maps to diag(-I4,I4,I4) != I12, but to identity
  in its A5 projectivization. The group-quotient
  statement is finite/abstract, not a wild pi1 theorem.
- `scripts/alexander_horned_f7_spin_c3_projector_scope.py`
  corrects a crucial FULL-group invariant trap.
  The central sign ± splits 360 sites into full-actor
  invariant 180+180 even/odd spaces.
  The further six rank-60 C3×C2 joint Fourier spaces
  are subgroup eigensectors ONLY: the C3 Fourier
  projectors do NOT commute with arbitrary nonuniform
  2I^3 factors. A literal counterexample was locally
  computed. The 180± subspaces may further decompose;
  no irreducibility claim is made.

Independent LOCAL Python arithmetic passed: 120 finite
icosians, exact 120-element SL2F5 isomorphism, 14400
quaternion and matrix products, determinant-one, F49/F7
Galois trace descent, degree obstruction, 18x18 selected
full-actor 12x12 products, six projector idempotents
and explicit noncentral counterexample, same root cube
in spin12 vs A5. No typecheck/CI status promoted.

Attribution: unit icosians and binary group sources
precede DASHI; see Choi & Lee 2018, DOI
10.3390/sym10080326, and the classical McKay
correspondence. Our finite F49/F7 scalar restriction
and exact group-map calculation is a new computational
derivation on these prior mathematical roots.

PRIORITY now moves to the GEOMETRIC SAME-OBJECT task:
concrete C3-invariant three-copy wild-ball embedding
with attaching collars and van Kampen stage identification.
The earlier `C3OrbitSolidExact` already makes arbitrary
seed-orbit set invariance exact, but it does not construct
the actual Hatcher wild seed or its gluing. Do not spend
more cycles proving an abstract C3 extension splits.


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
