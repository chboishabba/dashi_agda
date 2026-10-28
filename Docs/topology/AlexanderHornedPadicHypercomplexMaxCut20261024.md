# Alexander horned C3: p-adic, quaternionic and hypercomplex max-cut

Date: 2026-10-24; PR #1244; source and same-object audit.

## 0. Source ownership and what we actually have

Primary classical roots:
- J. W. Alexander (1924), wild sphere construction.
- Allen Hatcher, *Algebraic Topology*, Example 2B.2, printed
  pp.171-172, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf:
  classical nested binary horns, Cantor wild set, injective
  free-group stages and direct-limit complement pi1.
- Hamilton quaternions and their Spin(3)->SO(3) conjugation.
  The binary tetrahedral group of Hurwitz units and its C3
  conjugation of Q8 are classical. See also
  https://www.math.stonybrook.edu/~tony/bintet/quat-rep.html.
- The 2-adic integers are the inverse limit of binary prefix
  cylinders, and the 3-adic integers are the inverse limit of
  ternary prefix cylinders. A Cantor set is homeomorphic to Z_p,
  for each prime p; the *address radix* determines a natural
  compatible ultrametric, not a unique abstract Cantor topology.

Existing DASHI proof ownership (not newly rediscovered):
- `DASHI/Codec/TriadicPAdicCodec.agda`: CylinderSystem contract.
- `DASHI/Codec/TriadicPAdicCylinderExact.agda`: executable
  ternary low-order-digit projection and refinement.
- `DASHI/Geometry/SSP369Ultrametric.agda`,
  `DASHI/Metric/AgreementUltrametric.agda`: prefix ultrametrics.
- `DASHI/Topology/TernaryCylinderPantsGeometryExact.agda`:
  finite *ternary* cylinder/pants analogy, NOT the binary horns.
- `DASHI/Physics/YangMills/BalabanP33RationalQuaternionCoreExact.agda`:
  literal rational quaternion multiplication, not a placeholder.
- `DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda`:
  composition/norm algebra.
- `DASHI/Mathematics/Topology/QuaternionHopfUnitOrbitExact.agda`:
  same unit-quaternion action on Hopf coordinates.
- `DASHI/Algebra/FiniteQuaternionDoubleCover.agda`:
  exact Q8->V4 twofold quotient.
- `DASHI/Geometry/Clifford/SpinFromSignature.agda`:
  typed Clifford/Spin owner, continuous spin cover still a receipt.
- `DASHI/Foundations/PolyhedralFiniteRestrictionInstancesExact.agda`:
  SO3(j) -> A5 -> C3 *representation restriction* (j=0..35).
- `DASHI/Moonshine/Base369Monster3BVOAActionPhaseAdapterBidiExact.agda`:
  selected 3B action: different algebraic source and same-object gate.
- `DASHI/Mathematics/Topology/AlexanderHornedAbelianHolonomyBIDIExact.agda`:
  every abelian character kills all horn meridians.

## 1. EXACT binary-vs-ternary separation

At stage n the classical Hatcher horn has 2^n marked handles, and
its infinite branch addresses are `{0,1}^N`. Interpret the
CHRONOLOGICAL address as

    (b0,b1,...) -> sum_(n>=0) b_n*2^n in Z_2.

Its prefix distance is `2^(-k)` when the first disagreement is at
position k. In our THREE sector construction the wild endpoint
address is

    C3_ext x Z_2.

Important subtlety discovered in the actual source file:
`AlexanderHornedC3FiniteStageExact.HornAddress.suffix` stores
the MOST RECENT digit FIRST because `leftChild` prepends.
One must reverse the suffix to map the initial refinement to
the low-order 2-adic digits. The new module
`AlexanderHornedBinaryPadicCylinderExact.agda` explicitly
proves the chronological ordering and instantiates the
existing `TriadicPAdicCodec.CylinderSystem` with binary streams.
It also proves sector rotation leaves every finite binary
cylinder observation unchanged.

This is a homeomorphism/ultrametric model of the WILD ENDPOINT
CANTOR SET, not of the OPEN CONNECTED 3-MANIFOLD EXTERIOR.
No natural `C3 x Z2 = pi1(E)` claim exists. In particular,
a nontrivial Z_2 *space of endpoints* DOES NOT imply a nontrivial
pro-2 completion of the exterior group.

Ternary-cylinder/Digit369/369-hypervoxel machinery is relevant
for *sector phase observations* or comparative refinements,
but it is the WRONG radix for literal binary horns.

## 2. Exact rational quaternion rotor: same ambient map

Use the repo's actual rational quaternion ring and define

    q = (1+i+j+k)/2, qbar = (1-i-j-k)/2.

Then norm(q)=1, q*qbar=qbar*q=1,

    q^3=-1, q^6=1, (-q)^3=1,

and for EVERY (x,y,z) in Q^3,

    q*(xi+yj+zk)*qbar = zi+xj+yk.

The right hand side is exactly the SAME existing
`AlexanderHornedC3AmbientRotationExact.rotateXYZ` formula
`(x,y,z)->(z,x,y)`. This is a genuine same-coordinate-map
identification over Q (and hence as a rational polynomial
identity in R or Q_p), not a numerology match.

`AlexanderHornedQuaternionC3SpinExact.agda` now uses the
existing literal rational quaternion core, Cayley-Dickson norm
and Hopf unit-quaternion action and Q8->V4 source to construct:
- both signed lifts (of orders 6 and 3) of the same C3 spatial
  automorphism;
- an exact bridge to the prior Hopf unit-quaternion carrier;
- conjugation of Q8 basis 1,i,j,k by q, cycling i->j->k->i;
- the induced exact order-three permutation on the existing V4
  quotient of Q8.

Classical group hierarchy:

     Q8 ◁ 2T (binary tetrahedral) -> A4 <= A5,
       \                  |
        \-- conjugation C3 on Q8/V4

q lies in 2T (Hurwitz units), not in Q8. It induces an
EXTERNAL automorphism of Q8; Q8 alone has no order-three
element. An actual selected A4->A5 embedding and same-axis
transport are STILL required to identify that exact spatial
axis with the particular A5 3-cycle used by the finite VOA.
A character value or matching order does not supply this.

Crucially a spinor quaternion rotation element is NOT a loop
class in `pi1(exterior)`. Its order 3 or 6 is fully
consistent with the torsion-free exterior G.

The already existing Hopf right-multiplication action and
the spatial quaternion conjugation are TWO DIFFERENT ACTIONS
of the same unit quaternion. Neither is automatically a
physical gauge holonomy.

## 3. New p-adic representation NO-GO, more informative than abelian

Hatcher gives a nontrivial PERFECT G:
    G = [G,G], G_ab = 0.

Thus every homomorphism from G to a SOLVABLE group is trivial.
For a homomorphism f, f(G) is perfect, since
f([G,G])=[f(G),f(G)]. But a solvable perfect group is trivial
(the derived series both stays constant and reaches identity).

In particular ALL finite p-groups are solvable. Therefore

    Hom(G,P)={trivial} for EVERY finite p-group P,
    pro-p completion(G) = {1} for EVERY prime p.

This is stronger than merely killing abelian scalar characters.
It also makes a falsifiable difference between the p-adic
ADDRESS Z_2 and the COMPLETION of pi1: the first is a nontrivial
Cantor space, the second is the trivial pro-2 group.

New module
`AlexanderHornedProPSolvableBlindExact.agda` proves
from the literal recursive commutator relation that each
meridian image lies in EVERY term of an arbitrary finite
derived-series filtration of a target, and hence is trivial.
Its target supplies the derived filtration and finite
termination, not an axiom that the representation is already
trivial. Extend to every G element using the *existing*
MeridianGeneration certificate. The general theorem that
finite p-groups are solvable is classical and must be
applied when constructing a concrete finite p target.

### External C3 semidirect changes pro-p completion

Let H=G rtimes C3_ext. Perfectness of its normal kernel G
means every map H to a finite p-group kills G. Hence EVERY
such map factors through its C3_ext quotient.

Therefore the pro-p completions are exactly:

    pro-3(H) = C3_ext,
    pro-p(H) = 1  for p != 3.

It is NOT Z_3, despite the availability of ternary cylinders!
This is a particularly useful same-object / representation-vs-
symbolic-address discriminator. The external 3-fold rotation is
genuine finite torsion in H, not a nontrivial element of G.

## 4. Why p-adic LINEAR/VOA actors survive

The no-go only forbids SOLVABLE TARGETS, not general
`GL_n(Q_p)`. Our existing finite nonabelian group A5 is
perfect and has a faithful regular permutation representation

    A5 -> GL_60(Z) -> GL_60(Q_p),

for each prime p. A5^3 rtimes C3 acts faithfully by
permuting the 180 coordinates `C3 x A5` and thus admits
integer/permutation matrices over Q_p, not just C.

Consequently the existing rational pointwise commutative
vertex-algebra state algebra may be scalar-extended to Q_p,
and the same finite permutation action preserves the modes.
This is a finite algebraic non-Archimedean representation,
NOT a construction of a physical p-adic quantum Hilbert
space or the selected Monster moonshine VOA V^natural.
The linear representation still forgets ker(q) in G.

The p=3 field-of-roots nuance: a primitive cube root zeta3
is not in Q_3; Q_3(zeta3) is a ramified quadratic extension
and v3(zeta3-1)=1/2. For p congruent 1 mod 3, zeta3 is
already in Q_p. This affects eigenphase field selection but
not the existence of permutation matrices over Q_p.
No automatic `Q_p` field or valuation has been created in
Agda by the finite script.

## 5. Computational and kernel receipts

Independent local test of equivalent finite script:
- exact rational q^3=-1, (-q)^3=1, q*qbar=1;
- q conjugates 125 sample integer-coordinate pure quaternions
  to the existing cyclic permutation;
- 2-adic prefix valuations versus common-prefix length for
  ALL binary words at depths 1..7;
- stage chronological reversal/prepend/append compatibility;
- Z->C3 integer mod3 finite order discriminator;
- all 60 A5 elements are commutators, 60 regular
  permutation matrices distinguish all elements.

Result: PASS. Script committed as
`scripts/alexander_horned_padic_hypercomplex_audit.py`.
No nontrivial infinite theorem is inferred from the test.
The new Agda owner files are source-written; exact-head
Agda checks have NOT returned a kernel success. Keep PR draft.

The remaining geometric wall is STILL concrete identification
of the three-copy wild complement pi1 via collared open covers,
van Kampen, stage injections and the limit; p-adic address
topology, Spin lifts and quotient representations do not pay it.

## 6. Proof priority / Pareto

P0. Preserve Hatcher geometry/pi1 claim separation; obtain
concrete collar cover and stage-map isomorphisms.
P1. Exact-head typecheck the three new Agda modules; compile
and repair all imported-owner and definitional equality issues.
P2. Instantiate the selected A4->A5 permutation/rotation
identification for the quaternion rotor if useful; require
an explicit same-axis intertwiner to the 180-state VOA.
P3. If p-adic physics is desired, choose an actual local field,
operator/action and admissible p-adic analytic observable.
Only then examine 3B phases and deeper Clifford/Octonion
consumers. Do not infer from 27, 729, or 369 dimensions.

Attribution rule: classical source roots, source-written
definitions, finite computational receipts, kernel-certified
results, same-object identifications and physical claims are
six separately maintained statuses.

## 7. Stronger 3-adic scalar-versus-group phase discriminator

The original semidirect source H has a nontrivial **C3**
quotient, and thus nontrivial pro-3 completion. However its
scalar *one-dimensional* phase representation depends on the
chosen coefficient field.

For the bare field Q3, roots of unity are just ±1, so

    Hom(H,Q3^times) = {trivial}.

The nontrivial C3 phase has no scalar eigenvalue zeta3 in Q3.
Passing to the ramified quadratic field Q3(zeta3) creates
the two nontrivial third-root characters, and the rational
two-dimensional cyclotomic representation can split after
scalar extension. Q7 is another scalar field with primitive
third roots (3 divides 7-1).

The group-level map H->C3 is still present over ALL fields.
A three-cycle permutation matrix over Q3 is well-defined,
has order 3, and its nontrivial rational invariant block
has dimension two; it need not diagonalize over Q3.

Do not conflate:
1. nontrivial pro-3 group quotient (true),
2. a Q3-valued one-dimensional scalar phase (false),
3. a matrix actor over Q3 (true),
4. a selected Monster VOA 3B eigenspace (same-object open).

Standard references: local-field roots of unity and Hensel
lifting (e.g. MIT 18.785, 2021, Problem Set 4, problem 5;
the theorem that Qp has p-1 roots of unity for odd p),
https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/.


## 8. Profinite completion is NOT the product of this no-go

A further rigorous distinction: the project has a compatible
surjection `G -> A5^3` in the abstract commutator-tower
construction. Since `A5^3` is a nontrivial FINITE group,
the full profinite completion of G is NONTRIVIAL.

Yet `pro-p(G)=1` for every p. There is no contradiction:
the inverse system of *all* finite quotients can see
non-solvable finite groups, whereas every finite p-group
is solvable. The full profinite completion of G is therefore
NOT pro-p for any p, and cannot be recovered by merely taking
the product of its pro-p completions (which is trivial).

This also explains why nonabelian finite VOA and p-adic
matrix actors can retain real information that all flat
abelian/p-group-valued holonomies lose.


## 2026-10-24 impasse break: finite alternating separation and existing codec/actor reuse

Canonical source ledger:
`Docs/topology/AlexanderHornedOreResidualFiniteImpassBreak20261024.md`.

The earlier theorem `pro-p(G)=1` for all p is CONSISTENT
with a much stronger **positive** result: the abstract
Hatcher-type injective free-group/commutator direct limit
is RESIDUALLY FINITE (indeed finite-alternating separated).
For any nontrivial finite-stage word, residual finiteness
of free groups detects it in a finite quotient embedded
faithfully in an alternating group A_m. Ore's 2010
commutator-surjectivity theorem for simple finite groups
lets that quotient assignment extend through EVERY
subsequent binary horn subdivision, since
`x_w -> [x_w0,x_w1]`. Backward stage maps come by
precomposition; their directed colimit yields a
whole-source finite quotient detecting the selected word.
Therefore the canonical map from abstract G to its
FULL profinite completion is INJECTIVE, despite every
pro-p and prosolvable completion being trivial.

The new `AlexanderHornedOreFiniteTargetExtensionExact.agda`
proves that precise word-evaluation invariance through
one and arbitrary finite horn refinements, for a
target with genuine group laws and a chosen Ore
commutator section. The actual finite A_m proof and
colimit homomorphism remains an external mathematical
theorem/formal-import obligation, NOT kernel-certified
by that local source alone.

The existing `PolyhedralRegularRepresentationShiftExact`,
`AlexanderHornedC3FiniteVOAActorExact` and
`AlexanderHornedC3VOAModeLiftExact` now have a
same-actor consumer
`AlexanderHornedNonabelianRegularPadicReuseExact.agda`
proving faithfulness of a selected group-factor
regular action by observing its identity coordinate,
plus equivariance of the EXISTING rational vertex modes.
Every finite A_m quotient embeds in GL_|A_m|(Z),
hence in GL_|A_m|(Q_p) for every p. The collection of
such finite-dimensional actors is JOINTLY faithful,
but no ONE finite A5 or fixed-dimensional VOA is
claimed faithful on G. The infinite product of these
weight-zero state algebras is not automatically a VOA.

The existing
`BinaryBalancedTernarySubcarrierExact`,
`VerifiedFiniteTritCoder`,
`Base369BinaryTernaryRefinement` and
`BalancedTernaryC2C3DihedralCodecBridgeExact`
are now consumed by
`AlexanderHornedBinaryTernaryExistingCodecWeldExact.agda`:
  - actual Horn Bit -> existing strict nonzero balanced trit;
  - arbitrary trit -> two machine bits (11 rejected);
  - existing commuting 2^a*3^b resolution diamond;
  - exact finite C2 versus C3 order obstacles.
These digit maps do NOT give a continuous additive
isomorphism `Z2 =~ Z3`. Both are Cantor spaces,
but Hom_cont(Z2,Z3)=Hom_cont(Z3,Z2)=0 as
topological GROUPS, via coprime pro-p images.

The existing `Physics.QFT.NonAbelianFusionFromSpin`
is a CONDITIONAL Rep(SU2)-fusion upgrade from an
abelian CM source, NOT an automatic A5/3D-horn
representation. Existing SFGC `CliffordToM2Iso`
provides a genuine BASIS bijection, not multiplication
compatibility of entire algebras. No redundant
quaternion/Cayley-Dickson/Hopf or 369 owner was created.

Independent local finite computation PASSED 60 A5
commutator-section witnesses and 336 free-word
naturality comparisons across four stages. The
committed finite script, the focused workflow and
the exact-head Agda runner now include the new owners.
No successful exact-head Agda kernel/Lean geometry
receipt has been returned; the actual three-copy
wild-complement identification remains open and
PR #1244 must stay draft.


## 2026-10-24 max-cut: true spin-icosahedral / CRT / integral p-adic congruence bridges

Consolidated technical report, with exact primary source attribution:
`Docs/topology/AlexanderHornedCRTSpinPAdicVOAMaxCut20261024.md`.

**Previously built donor owners** include the genuine
`SixWheelCRTExact`, `Base369BinaryTernaryRefinement`,
`BinaryBalancedTernarySubcarrierExact`,
`U1AsSU2AbelianRestrictionExact`,
`NonAbelianFusionFromSpin` (conditional!),
literal quaternion/Hopf/Q8, and
`BinaryPolyhedralMcKayDimensionExact` (E8-dimensional
skeleton ONLY). These were inspected and reused, not reinvented.

**New literal 2I (spin) finite quotient**:
`scripts/alexander_horned_spin_icosahedral_bridge.py`
enumerates SL2(F5) (120), its FIVE Q8 subgroups and their
normalizer order 24, their conjugation action on five
subgroups (all 60 A5 elements, exact kernel +/-I),
non-splitting by the unique involution, and actual
order-six rotor whose cube is -I. It also enumerates a
commutator pair for EVERY 2I element (120/120) and a
root pair generating the full 120. Thus a compatible
three-root Hatcher abstract group -> 2I^3 quotient can
be explicitly defined stage-by-stage. The root cube
remains nontrivial central -I in 2I and is erased in
the old 180-dimensional A5 quotient.

**Concrete strict VOA improvement**:
functions on C3×A5 (180 coordinates) embed via pullback
into functions on C3×2I (360 coordinates). Old rational
pointwise vertex modes, action and the observer now live
on compatible SAME coordinate charts. New
`AlexanderHornedSpinVOAFactorFunctorExact.agda` proves
the nine actual sector/phase naturality cases, mode
equivariance, and injectivity pointwise from a proven
surjective group factor. New
`AlexanderHornedBinaryIcosahedralSpinSignBidiExact.agda`
proves the central sign cannot be recovered from the
projective A5 observer; the exact finite group supplier is
currently a Python receipt, not an Agda 120-element group
instance. Neither actor equals the Monster VOA.

**Mixed binary/ternary**:
`AlexanderHornedMixedPrimeCRTWeldExact.agda` reuses
the genuine old 2×3 CRT, 2^a3^b resolution lattice,
and bit-in-balanced-trit subcarrier. Adds the *reverse*
fixed 2-bit encoding of three balanced trits with
11 explicitly unused, proves roundtrip on image,
and proves sector-rotation commutes with binary horn
cylinder forgetting. The whole inverse-limit CRT
`C3×Z2 = lim Z/(3·2^n)` is a classical math
consequence, not asserted as an already kernel-proved
Agda ring equivalence. Independent finite CRT audit
`alexander_horned_mixedprime_congruence_audit.py`
passed 6,141 finite states n0..10, general 2^a3^b
for a,b=1..4.

**Real low-rank p-adic restriction**:
classical congruence kernel GL_n(Zp)->GL_n(Fp)
is pro-p. A perfect horned G maps trivially to any
solvable group and any pro-p group. Since GL2(F2)
derived series is 6→3→1 and GL2(F3) is
48→24→8→2→1 (exhaustively computed), ANY integral
G->GL2(Z2) or G->GL2(Z3) is trivial.
The source-level
`AlexanderHornedPadicCongruenceNoGoExact.agda`
uses the old finite-solvable meridian theorem and
separating congruence reductions. This does NOT
block higher-rank/noncompact Qp representations or
ordinary nonabelian A5/2I finite quotient matrices.
SL2(F5) is NOT automatically a 2D Z5 integral lift.

**Still open:** exact-head Agda kernel receipts and
the particular three-copy geometric exterior pi1
identification. No faithfulness of G or equivalence to
Monster 3B is promoted.


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
