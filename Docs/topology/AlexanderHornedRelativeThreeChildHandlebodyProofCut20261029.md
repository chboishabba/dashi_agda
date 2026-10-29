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
