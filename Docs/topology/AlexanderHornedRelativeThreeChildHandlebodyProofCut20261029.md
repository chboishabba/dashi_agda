# Relative three-child handlebody: six-obligation proof cut

Date: 2026-10-29. Source owner: #1244; adjacent #1414 has independently
owned polynomial S5/derived-series nonsolvability, **not** an embedded
Alexander horned complement proof. Follow the project's no ESD edits,
zero new postulates, no fabricated Monster 3B same-object identities.

## What is already exact

The original selected stage refinement is

```
w=[a,b][b,c]=a b A c B C, uppercase=inverse
p=a b A c
p^-1 w p=[b^-1,c^-1 a].
u=b^-1; v=c^-1 a; z=c.
inverse substitution: a=zv, b=u^-1, c=z.
```

Three elementary Nielsen operations suffice: reverse b; replace a by
c^-1a (left multiplication); exchange the first two handle-generator
labels. Existing `AlexanderHornedTernaryPantsMeridianBoundaryExact.agda`
owns the genus-one boundary word; `AlexanderHornedBalancedTernaryCommutatorTowerExact.agda`
owns the ternary abstract bonding word. New exact executable
`scripts/alexander_horned_relative_nielsen_stage_audit.py` checks
all 9,331 signed words length <=5, both inverse maps, and conjugation.
It was independently executed locally and passed. The source-written
Agda modules are not kernel checked.

Original Hatcher construction in *Algebraic Topology* Example 2B.2
uses TWO children per binary horn. The user's native THREE-child end
space `C3 × Trit^N` is a genuinely different nested stage proposal.
A homeomorphism of ABSTRACT Cantor ends is insufficient to identify
their wild embeddings or exterior fundamental groups.

## G1. Exhibit the standard tame genus-three handlebody with a cap

A standard topological carrier is a closed 3-ball `D^3` with three
disjoint 1-handles `D^1×D^2` attached to six disjoint attaching
2-disks on its boundary. It is the regular neighborhood of a bouquet
of three circles and has `pi1=F(a,b,c)`. Choose an embedded closed
2-disk `D_cap` in the unused part of the 0-handle boundary and a
product collar `D_cap×[0,eps]` disjoint from the attaching disks.
The three core loops are free generators. **Standard abstract tame
model is known.** No explicit certified PL-coordinates of six feet,
three arcs, cap collar and disjoint bounding boxes has been committed
here. Such coordinates are necessary for a fully checkable *specific*
G1 instance but not for the classical existence of H3.

## G2. Relative handle-slide support

The 3 elementary Nielsen operations have standard topological
realizations on a genus-three handlebody. They must be supported
outside `D_cap×[0,eps]`, not fixed on all of the boundary.
The full-boundary-fixing version is IMPOSSIBLE: the inclusion
`pi1(∂H3) -> pi1(H3)` is onto, so a boundary-identity
homeomorphism acts as identity on pi1. A slide inducing the nontrivial
Nielsen map cannot be such a homeomorphism.
**Missing certificate:** an explicit embedded system of cut disks,
band arcs and compact slide/isotopy supports disjoint from the
particular selected collar, and the inverse maps on the same carrier.
A bare free-group automorphism is not that certificate.

## G3. Relative theta ribbon and meridian

The cyclically reduced w is the boundary of an ABSTRACT genus-one
ribbon surface: the six-sided polygon has V=2, E=3, F=1, chi=0.
Its theta-graph spine has first Betti number 2. Under the Nielsen
basis `u,v,z`, its boundary is [u,v], with based conjugator p.
**Missing certificate:** a PROPER embedding of that punctured
torus into the actual complement of three selected *geometric*
child horns; an embedded based path representing p which is
disjoint from the cap/collar; a proof that all peripheral loop
labels map to the stipulated complement meridians. An abstract
surface-group map is not sufficient, and injectivity cannot
be inferred from symbolic word equality.

## G4. Stage inclusion and meridian naturality

Required square (based pi1, including connecting paths):

```
pi1(E_parent) -- actual inclusion --> pi1(E_children)
      | chosen meridian chart                | child chart
      v                                      v
 F(parent labels) ---- w/refinement ----> F(a,b,c)
```

The geometric inclusion must induce the EXACT commutator product
`[a,b][b,c]` (not just a conjugate with an unspecified basepoint).
The conjugator `p` must be entered in the path transport.
**Missing:** actual complements and pair maps, homotopy
equivalences to chart graphs, a compatible basepoint and the
proof the square commutes. Algebraic injectivity of a free-word
substitution does not itself establish geometric stage inclusion.

## G5. Infinite nested wild satellite and the stationary cap

Require closed tame finite stages `B_n` and handles with:
(i) nestedness and disjoint 3-child linking, (ii) uniformly
shrinking diameters along EVERY infinite trit address,
(iii) tame homeomorphisms `B_n ≅ D³` fixing the same cap,
(iv) uniform convergence and injectivity of the limit map,
(v) boundary wildness at prescribed end points,
(vi) no accidental intersections, (vii) true C3 equivariance
with three separated root sectors, (viii) collar supports
which do not accumulate into the stationary cap.
**Missing:** explicit source-faithful 3-child embedding
with quantified clearance and all these proofs.
A tame base-seven Cantor ball nesting and a three-legged
combinatorial pair of pants do NOT prove these properties.

## G6. Actual exterior fundamental group and equivariance

Need a cofinal open exterior exhaustion `E=∪E_n`
of the selected nested wild set; every compact based loop/homotopy
must be captured in some finite stage. Need compatible van Kampen
charts with the ACTUAL geometric G4 inclusion. The target is
the ternary group colimit with external sector C3 permutation,
and the orbifold semidirect group only after the action is
defined on the same exterior with a fixed basepoint.

**Missing:** G4–G5 inputs. Conditional algebraic/free-group
results cannot be upgraded to the real `pi1(E)` or actual
orbifold action without them.

## Cross-check: #1414 derived-series no-go

PR #1414's distinct `PolynomialDoubleCommutatorSolvableNoGoExact`
treats solvable-derived-series obstructions for polynomial root
permutations. It does not prove any of G1–G6. The broader
perfect-to-solvable observation is compatible with #1244's local
metabelian phase actor no-go. This is a legitimate methodological
cross-check (negative representation boundary), not a Monster,
Galois, or physical same-object identification.

## Explicit acceptance ledger

| Claim | Status | Correct verification |
|---|---|---|
| Standard abstract genus-3 handlebody | Classical mathematical construction | Topological handle attachment and deformation retract |
| Three selected Nielsen elementary maps | Exact source and 9,331-word execution | Algebraic inverse maps |
| Cap-disjoint 3D homeomorphism on specific H3 | OPEN | Embedded cut disks, bands, ambient isotopy |
| Punctured-torus word with based conjugator | Exact source/free-group computation | Word identity and surface polygon |
| Punctured torus in actual three-child complement | OPEN | Explicit proper embedding and meridian/path chart |
| Three-child actual meridian inclusion | OPEN | Based pi1 naturality square |
| Wild nested C3 satellite / cap collar | OPEN | Coordinates, nesting, injectivity, wildness |
| Exact exterior pi1 and orbifold | OPEN | Exhaustion + geometric van Kampen |
| Agda kernel checks on new modules | NOT RUN | Typecheck exact PR head |

Primary credit: Alexander (1924); Hatcher, *Algebraic Topology*
Example 2B.2; standard handlebody theory as presented by Sebastian
Hensel, *A Primer on Handlebody Groups*. Source-written repository
proof ownership stays with original individual PRs, including
#1254 pants, #1405 sonic T15/T16, #1414 S5 polynomial monodromy,
and earlier Ibrahim Monster 3B. No numerical or symbolic same-object
promotion.


## New G1 rational PL spine: finite geometric witness

**Executable, source-specific progress on G1**:
`scripts/alexander_horned_three_loop_pl_spine_g1.py` supplies an
explicit exact rational EMBEDDED planar graph. Its seven vertices
are central `O=(0,0)` and six selected feet
```text
  a: (8,1), (8,-1)
  b: (-5,8), (-6,7)
  c: (-5,-8), (-6,-7)
```
Each of the three triangles goes `O -> first foot -> second
foot -> O`. All 9 edges are tested for pairwise intersections;
different triangles meet only at `O`. The connected embedded
graph has 7 vertices and 9 edges. Its fundamental group is
free of rank `E-V+1=3`, canonically charted by the three
labelled triangles `a,b,c`. The classical regular-neighborhood
theorem makes a sufficiently thin embedded closed PL
neighborhood a tame genus-three handlebody in R³, with
a 0-handle near O and three 1-handles.
This is a *specific finite* tame three-dimensional carrier,
not merely a numerical count of three triangles.

A stationary cap is reserved on the **lower hemisphere**
of the central 0-handle, e.g. in the spherical patch with
`z <= -3/4`. The noncentral graph is planar (`z=0`), so the
cap has positive vertical separation from all graph parts
outside the central 0-handle. The existence of a sufficiently
small closed product-collar follows from this positive
separation and the tame 0-handle chart. The script does
NOT specify the complete non-overlapping 3D tubular
radii of all 9 edges or certify an exact polyhedral
boundary triangulation; that remains a stronger
coordinate-level model, but the standard regular
neighborhood theorem does establish an actual
genus-three HANDLEBODY for this embedded graph.

**Critical type check:** the loops `a,b,c`
in this G1 handlebody are its own **core fundamental-group
generators**. They are NOT automatically MERIDIANS OF
THREE HORNS IN ITS COMPLEMENT. The later G3/G4
must produce a chart from the actual complementary
exterior and geometric child meridian loops
to a free group with these names. Without it,
even a cap-fixed Nielsen automorphism of the
handlebody's OWN fundamental group does not pay
the required horned-exterior meridian inclusion.
This guards a possible internal/external
dualisation mistake.

**Updated accepted progress:**
- G1 (abstract actual tame genus-three handlebody,
  3 labelled core circles, disjoint reserved cap):
  PL graph and regular-neighborhood mathematical
  construction; exact rational noncrossing verified.
- G2 (specific cap-fixed ambient homeomorphism
  inducing chosen Nielsen map): STILL OPEN.
- G3 (punctured torus embedded in ACTUAL
  three-child EXTERIOR with based meridian chart):
  STILL OPEN; exact abstract free-word boundary
  and conjugator ALREADY owned.
- G4 (true horn-complement stage inclusion):
  STILL OPEN.
- G5/G6 (nested linked wild limit, actual
  C3-equivariant exterior group): STILL OPEN.
- #1414 S5 derived-series/double commutator
  remains separate; general perfect→solvable
  no-go does not solve ambient geometry.

Attribution: classical graph regular-neighborhood
theory, genus = E-V+1, Alexander/Hatcher original
wild geometry and prior source-owned Nielsen
and pants constructions. The script is a new
finite source-specific rational witness. No
Agda kernel certification, precise PL
handle-slide, ambient horned sphere or
Monster 3B identity is claimed.


## G1 strengthened: exact tame-complement meridian linking chart

We now have more than the abstract genus-three regular neighbourhood.
The new exact rational source
`scripts/alexander_horned_three_child_dual_meridian_g1.py`
uses the same three triangles, each with a simple planar spanning
2-disk, and constructs three closed **polygonal rectangle loops**
in R³ minus the graph. Each rectangle passes from z=-2 to z=+2 at
one point strictly INSIDE precisely one triangle and returns through
the plane at one point outside ALL three triangle disks:

```text
inside    outside   spanning disk
( 6, 0)   ( 9, 0)      a
(-4, 5)   (-8,10)      b
(-4,-5)   (-8,-10)     c
```

The exact determinant/segment audit proves all six crossing
projections avoid the nine embedded graph edges and that each
rectangle has exactly ONE interior transverse intersection with
its own spanning disk, zero with the other disks. Orientation of
the loops gives the integral LINKING matrix

```text
         a  b  c
  ma = [ 1, 0, 0 ]
  mb = [ 0, 1, 0 ]
  mc = [ 0, 0, 1 ]
```

As the graph is compact and the loops are disjoint from it,
choose the regular-neighbourhood radius sufficiently small
so they remain in its tame EXTERIOR. This certifies concrete
dual linking loops in the complement of the THREE-LOOP
TAME HANDLEBODY. In particular their homology classes pair
with the three graph cycles as the identity. This is not
a proof of the full free fundamental-group presentation
on those loops (which uses standard unknotted planar
handlebody complement theory), nor a proof that the
three loops become the correct *wild child meridians*
after the yet-to-be-designed ternary horn linking.

**Geometric wall now sharper:**
the three tame complementary meridian candidates are
explicit. The missing map is the actual 3D *satellite
stage* embedding, with a supported cap-fixed Nielsen
move and a properly embedded theta ribbon whose
boundary represents `[a,b][b,c]` in the SAME
exterior. Without those, neither the parent stage
inclusion nor the wild direct-limit exterior group
is identified.

Exact rational local audit PASSED for the linking
matrix. This is NOT the Agda kernel, a certified
3D PL triangulation or a physical acoustic experiment.

## 2026-10-29 local-C3 symmetry: obstruction and constructive algebraic repair

See [signed stabilizer](AlexanderHornedSignedMeridianStabilizer20261029.md)
and [order-three Nielsen stabilizer](AlexanderHornedOrderThreePeripheralNielsen20261029.md).

- Signed child-meridian permutations: exactly 4 / 48 preserve the unoriented
  class of w=[a,b][b,c]. No signed three-cycle does so.
- IMPORTANT QUALIFICATION: a **different**, non-signed-permutation automorphism
  of order THREE exists. In Nielsen coordinates u=b^-1, v=c^-1 a, z=c:
  phi(u)=v, phi(v)=v^-1u^-1, phi(z)=z. In original coordinates:
  a->c a^-1 c b, b->a^-1 c, c->c.
- Exact free-word audit establishes phi^3=id and phi(w) conjugate to w.
  Thus the earlier signed-permutation no-go cannot be promoted to a
  blanket local-C3 no-go in Aut(F3).
- Geometric G2–G6 are STILL OPEN. Specific topological existence would
  require a cap-relative supported map of the chosen actual complement,
  embedded based peripheral surface, equivariant bonding inclusion,
  compatible infinite wild stages and an exterior-group proof.
- Neither algebraic order-three nor the general mapping-class surjection
  implies an order-three cap-fixed geometric representative for this
  specific 3D wild construction. External C3 root-sector permutation is
  independently available and must remain distinct.

Attribution remains Alexander/Hatcher, Nielsen and Hensel, original
DASHI module owners and separate Ibrahim Monster 3B proof ownership.
No ESD edits, kernel checks, CI or physical/Monster same-object promotion.

## Source-first owner audit, 29 October 2026

See [the exact Agda and Lean source audit](AlexanderHornedAgdaLeanOwnerAudit20261029.md). External-sector `rotationCommutesAllTernaryStages` is already in the canonical Agda tower. Do not duplicate it or conflate it with a local Nielsen C3. The complement-side PL/meridian certificates G2–G6 are still open. The Lean recursive repository search was truncated and does not establish exhaustive absence. Attribution and Ibrahim Monster 3B non-promotion unchanged.


## 2026-10-29 exact local Nielsen based-naturality gate (new)

Read the actual canonical Agda sources, not only PR descriptions:
\`AlexanderHornedBalancedTernaryCommutatorTowerExact\`,
\`AlexanderHornedTernaryPantsMeridianBoundaryExact\`,
\`AlexanderHornedTetralemmaRelativeHandleSlideGateExact\`,
and \`AlexanderHornedC3ExteriorBridge\`. The attached Lean
\`ThreeArmCollarCoverAssembly\` and \`ThreeArmHatcherGroupTransport\`
remain conditional consumers. \`EverythingTOESymmetryResolved369\` already
imports the canonical boundary module, so the following results enter that
TOE import graph without a duplicate owner.

**Concrete strengthened G4 obstruction:** in \(F(a,b,c)\), with
\(w=[a,b][b,c]=abAcBC\) and
\(\phi(a)=ca^{-1}cb,\ \phi(b)=a^{-1}c,\ \phi(c)=c\), exact free reduction gives

\[
q=ca^{-1}ca^{-1},\qquad
\phi(w)=q\,w\,q^{-1}\ne w.
\]

It is a genuine equality of reduced free-group words, not just an
unexplained cyclic-equivalence boolean. The automorphism satisfies
\(\phi^3=\mathrm{id}\) by checking three free generators and extending
through the free-group universal property; this mathematical extension
is NOT yet a quantified Agda proof. The reduced-word Agda terms live
IN the original
\`AlexanderHornedTernaryPantsMeridianBoundaryExact.agda\` under
\`LocalNielsenReducedCertificate\`, including \`canonicalWordReduction\`,
\`puncturedTorusBoundary\`, \`phiCubedOnA/B/C\`,
\`phiPreservesPeripheralConjugacy\`, and
\`phiNotStrictlyBasedPeripheral\`. No algebraic analogue is silently
declared to be an ambient three-manifold action.

**Consequent geometric gate:** a based naturality square in which the
parent based meridian is fixed but the children transform by this
specific local \(\phi\) **cannot commute strictly**. It could commute
only after supplying compatible conjugating basepoint/path transport,
with the algebraic target class \(q\). An *actual path in the selected
complement*, its lift through cap-relative slides, and coherent
stage-to-stage transport are still absent. Conjugacy-class equivariance
is insufficient for the claimed *based* inclusion without those maps.
This does not obstruct the already canonical external three-sector C3
rotation, which permutes entire root sectors rather than children.

Source regression \`scripts/alexander_horned_order_three_peripheral_nielsen.py\`
now checks the exact \(q\), strict mismatch, and every 4,687 freely reduced
word of length <=5 for \(\phi^3\). A byte-matched local script was executed
successfully on 2026-10-29; GitHub readback and exact-head Agda typecheck
are separate receipts. G2 cap-relative PL map, G3 actual embedded
punctured torus, G4 geometric based square, G5 nested wild stages and
G6 exterior fundamental-group identification REMAIN OPEN.

Attribution: Alexander 1924 and Hatcher AT Example 2B.2 retain the
binary wild-topology source; Nielsen/classical free-group algebra and
handlebody theory retain original mathematical priority; current
DASHI owners retain source/proof ownership. The polynomial #1414,
sonic #1405, and prior Ibrahim Monster 3B work remain distinct.
No ESD, empirics, physical gauge, or same-object Monster promotion.


## 2026-10-29 second Pareto cut: modular conjugacy obstruction (27 vectors)

The canonical boundary owner now contains
\`NielsenMod3PermutationBarrier\`. It reuses
\`DASHI.Core.FiniteC3OrbitStabilizerExact.C3\`, \`groupElements\`,
addition and inverses to enumerate all \(3^3=27\) exponent vectors
over \(\mathbb F_3\). The local peripheral-stabilizing nonlinear
Nielsen map induces on the abelianization of \(F(a,b,c)\) the matrix

\[
N=\begin{pmatrix}-1&-1&0\\1&0&0\\2&1&1\end{pmatrix},
\qquad
P=\begin{pmatrix}0&0&1\\1&0&0\\0&1&0\end{pmatrix}
\]

for the naive literal child-label three-cycle \(P\). Both satisfy
\(N^3=P^3=I\), \(\det N=\det P=1\) and have
\(\chi(t)=t^3-1=(t-1)(t^2+t+1)\) over characteristic zero.
**That matching characteristic polynomial does NOT identify their
integral or mod-3 representations.** Direct finite calculation gives

\[
|\mathrm{Fix}_{\mathbb F_3^3}(N)|=9,\qquad
|\mathrm{Fix}_{\mathbb F_3^3}(P)|=3.
\]

Since a matrix in \(GL_3(\mathbb Z)\) reduces to an invertible matrix
modulo three, and conjugacy preserves the fixed-point-set cardinality,
\(N\) and \(P\) are not conjugate in \(GL_3(\mathbb Z)\). Therefore
their original \(F_3\)-automorphisms are **not conjugate in
\(\mathrm{Aut}(F_3)\)** either. This eliminates any attempted
free-basis change equating a literal generator three-cycle to the
specific nonlinear Nielsen peripheral stabilizer. It is strictly
stronger than the earlier 48-case signed permutation audit and
compatible with the existence of both distinct order-three actions.

The Agda finite certificates are \`allAbelianTriplesCount\`,
\`literalCycleFixedCount\`, \`localNielsenFixedCount\` and
\`unequalMod3FixedCounts\`. They prove concrete cardinality computations
IF the exact-head Agda kernel checks; the general conjugacy-invariant
argument is documented mathematically, not packaged as a quantified
Agda theorem. The committed Python regression enumerated all 27
vectors, passed, and also independently exercised the order-three
action. Local execution was byte-compared with GitHub source using
FNV-1a/length; no Agda kernel or CI.

This explains why sharing the rational C3 spectrum, a ternary cell
count or a polynomial S3/Monster fingerprint does not license a
same-object identification. External-sector rotation already has
its independent all-depth tower theorem. G2–G6 still require actual
relative 3D topology, with G4's separate conjugating path \(q\).
Underlying facts: classical integral representation theory and
abelianization of free groups, not a new claim of original
group-theoretic prior art. DASHI contribution is the precise
source-specific modular discriminator and finite regression.


## 2026-10-30 six ABC permutation continuation — canonical S3 reused

Read the actual \`TernaryRoleCarrierExact\`, \`TernaryEndomorphismConjugacyExact\`,
\`TernaryPermutationS3LawsExact\`, the six SSSP linear extensions,
\`AlexanderHornedSectorDihedralS3EndExact\`, the existing local
meridian module, and conditional HornedC3 Lean group transport.
The external-sector S3 is ALREADY OWNED; the new result is the
source-specific child-label **boundary-word orbit**, not an additional S3.

See [ABC six-permutation proof ledger](AlexanderHornedABCSixPermutationOrbit20261030.md).

In the canonical meridian Agda owner, \`ABCSixPermutationPeripheralOrbit\`
provides literal \`abc/acb/bac/bca/cab/cbaAnchored\` witnesses,
\`sixOrientedNormalFormsDistinct\`, six reversal-pair witnesses,
\`allSixMapToThreeUnorientedClasses\`, and
\`orbitFamilyEquivariant\` for the full 6×6=S3 action table.
All six oriented cyclic conjugacy representatives are distinct,
but inversion pairs ABC/CBA, ACB/BCA, BAC/CAB. This produces
**three** unoriented orbits. A selected single parent boundary class
is therefore not invariant under the FULL local child S3, while
its **six-word boundary family** is equivariant as an algebraic object.

DO NOT silently replace the original stage map by the family:
G4 now has two explicitly different design choices: (a) hold fixed
one parent class, permit only its actual stabilizer and prove based
path naturality, OR (b) construct a genuine three-dimensional
orbit-indexed multi-peripheral stage with six oriented charts and
prove it geometrically. Algebraic sixfold equivariance does not
supply six embedded punctured tori or six realizable cap-relative
slides. The previously shown GL3(Z) modular no-conjugacy obstruction
between local Nielsen C3 and literal label C3 remains valid.

**TODO/max-cut:** G2 actual supported PL moves; G3 actual embedded
relative theta ribbon/torus; G4 actual based inclusion/path and
explicit choice of single-boundary versus orbit-indexed geometry;
G5 coherent nested wild stages; G6 same-object exterior group.
No action from the pending polynomial #1414 or trialectic #1438
branches was imported as if it were a proven topology result.
The prior Hatcher binary geometry is still binary.
Source written, exact-head Agda and Lean kernel unexecuted; CI skipped.
