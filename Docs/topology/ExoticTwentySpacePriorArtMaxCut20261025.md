# Exotic topological spaces: source-specific max-cut and prior-art reuse

Date: 2026-10-25. Branch: `topology-exotic-spaces-prior-art-maxcut-20261025`,
based on horned-sphere branch / PR #1244, NOT master. **Stacked work**.
This is an implementation-plus-audit, NOT a claim that all twenty objects are now
geometrically formalised or kernel-proved.

## Exact, executed deliverables

1. `DASHI/Mathematics/Topology/ExoticEndProfilesViaCantorExact.agda` imports
   **existing** `DASHI.Foundations.CantorProjectiveCylinderMeasureExact`:
   end codes for Cantor-tree (binary streams), Loch Ness (unit), Jacob's ladder
   (two Boolean ends); staged genus markers; Cantor endpoint distinctness;
   re-exported original dyadic cylinder refinement **proof**.
   This is an end/genus presentation, not a topological realisation.
2. `DASHI/Mathematics/Topology/ExoticAmbientLinkingNoGoExact.agda` imports
   **existing** `AlexanderHornedC3FiniteStageExact` and `FiniteC3OrbitStabilizerExact`.
   Two explicitly marked objects with the identical HornAddress carry different
   linked bits; proves no function of address alone classifies every marker.
   This is a concrete information-loss statement, NOT a realised linked/unlinked
   embedding of the same Cantor set.
3. `scripts/exotic_topology_exact_models.py`:
   exact SymPy checks for six object families (Whitney umbrella, Ida,
   von Seggern seashell, Simons cone, finite Seifert Euler formula, and
   a chosen pinched-torus CW quotient). Executed locally: PASS.
4. `scripts/exotic_topology_surface_exhaustions.py`:
   concrete finite oriented compact-surface attachment schedules:
   * Cantor tree: start disk, glue a pair of pants at every outgoing boundary;
     stage n has genus 0, 2^n boundary circles, chi=2-2^n.
   * Loch Ness: start disk; add one genus-one/two-boundary cobordism per stage;
     genus n, one outgoing boundary, chi=1-2n.
   * Jacob ladder: start annulus; add one genus-one/two-boundary
     cobordism at BOTH ends per stage; genus 2n, two outgoing boundaries,
     chi=-4n.
   All attachments are along one entire boundary per connected cobordism,
   so Euler characteristics add (the gluing circle has chi=0).
   Executed locally: PASS at depths 0..12, including all 4096 Cantor
   boundary words at depth 12. Global locally finite direct-limit
   manifold and end-space homeomorphism proof NOT supplied.

## Local exact fixtures: mathematical scope

- Whitney: `(u,v)->(uv,u,v^2)`, image in `x^2=y^2 z`, Jacobian
  cross-product `(2v,-2v^2,-u)` vanishes only at `(0,0)`.
  Two source preimages at `u=0,v=+-3/5` coincide, while `(0,0,-1)`
  satisfies the polynomial but does not lie in the REAL parametrised image.
  Thus the algebraic locus is strictly larger than the parametrised image.
- Simons cone: polynomial `sum(x_i^2)-sum(y_i^2)=0` on R^4+R^4;
  gradient `(2x,-2y)` zero only at the origin; a unit-link sample passes.
  NO geometric measure theory / calibration / area-minimization proof.
- Ida: Idaszak/Francis parametrisation with (l,b,r1,r2)=(1,1,1/2,1).
  Trigonometric simplification checks EXACTLY
  `p(theta+pi,2pi-tau)=p(theta,tau)` in all three coordinates,
  and denominator >=1-1/sqrt(2)>0. No global immersion rank proof.
- Seashell: von Seggern source variant n=a=b=1,c=1/10, source domains as
  published. Checks `x^2+y^2=radius^2` and matching u=0 / u=2pi seam.
  NO assertion of global smoothness/embedding.
- Seifert: uses classical disk-and-band identity
  `chi=s-c=2-2g-b` on explicitly supplied sample diagram counts
  (unknot, trefoil, figure-eight, Hopf-link annulus). No algorithm
  deriving s from an actual oriented crossing diagram, nor a spanning
  surface embedding.
- Pinched torus: collapse one essential 1-cell of standard torus CW
  decomposition, leaving cellular differential zero and
  Betti numbers (1,1,1). No homeomorphism to a wedge is asserted
  (homotopy equivalence does NOT make singular spaces homeomorphic).

## Full 20-object acceptance matrix

The labels mean: C=concrete local fixture, P=finite/presentation consumer,
D=direct preexisting donor, OPEN=decisive geometric/analytic theorem missing.

| Requested object | Status in this branch | Primary prior-art owner(s) | Decisive acceptance test still to discharge |
| --- | --- | --- | --- |
| Lakes of Wada | P/OPEN | Cantor clopen cylinders, horned ambient-linking no-go, C3 | Three *connected disjoint open* planar domains with identical actual topological boundary, proof at infinite limit |
| Wild knot | D/OPEN | PR #1244 linking/collars; braid permutation donors | Source-specific embedded S^1, non-local-flat point and ambient isotopy obstruction |
| Wild arc | D/OPEN | PR #1244 horn recursions | Injective interval embedding plus non-1-LCC / non-tameness witness |
| Fox-Artin wild arc | D/OPEN | Horn group/proper-collar scripts | Fox-Artin specific iterated embedding and local 1-LCC/cellularity test; pi1 alone not enough |
| Cantor tree surface | P/OPEN | CantorProjectiveCylinderMeasureExact; surface exhaustion script | Countable collared pants union is planar 2-manifold; end space is Cantor; exact end-genus map |
| Jacob's ladder | P/OPEN | same finite stage glue library | Oriented connected 2-manifold, exactly two ends each with infinite genus |
| Loch Ness monster | P/OPEN | same finite stage glue library | Oriented connected 2-manifold, exactly one end and infinite genus |
| Warsaw circle | OPEN | homotopy/cochain/CW donors | Construct sine-curve closure with added arc; prove weak contractibility but not contractibility/CW type |
| Whitehead theorem | OPEN | FiniteCochainComplexExact; real HoTT backend | Weak equivalence between actual CW complexes implies homotopy equivalence |
| CW complex | P/OPEN | TernarySynthesisCellComplexExact | Arbitrary disks attached by maps with quotient topology and closure-finite/weak topology properties |
| Schoenflies problem | D/OPEN | PR #1244 wild sphere, collars | Locally flat S^(n-1) embedding gives standard complementary closed n-balls; wildness cannot be ignored |
| Ida surface | C/OPEN | ComplexManifold and geometric coordinate infrastructure | Smooth Klein quotient / global rank-two immersion theorem |
| Riemann surface | D/OPEN | ComplexManifold, ProjectiveLineAtlasGluingExact | Realised Hausdorff second-countable local C charts / analytic transition maps; CP1 as first case |
| Morin surface | OPEN | immersion/geometry candidate donors | Source parametrisation with rank two everywhere and sphere eversion regular homotopy |
| Nielsen-Thurston | OPEN | genuine mapping-class and curve systems missing | Full periodic/reducible/pseudo-Anosov trichotomy and dynamical foliations |
| Pinched torus | C/OPEN | QuotientSetoidSurface, finite cochains | Explicit torus quotient topology, singular point local topology, maps to cellular quotient |
| Simons cone | C/OPEN | metric/smooth algebra donors | Source-specific area-minimizing proof (calibration/varifold / GMT) |
| Seifert surface | C/OPEN | FiniteBraidRhizomeCalculus, finite cell donors | Real oriented knot diagram -> oriented embedded disk-band surface -> boundary knot |
| Seashell surface | C/OPEN | analytic coordinate geometry | Source-specific parametrisation and domain boundary/singularity identification |
| Whitney umbrella | C/OPEN | polynomial/singularity algebra donor | Formal polynomial map, image description, singular double-locus stratification |

## Avoided false promotions

- `DASHI.Topology.FiniteBraidRhizomeCalculus.Braid2` has swap^2=id:
  it is only a two-strand *permutation shadow*, NOT the full braid group B2=Z.
- `InverseLimitClopenRefinement.CompleteClopenAuthority` has abstract
  `intersectionSingleton : Set`/`ultrametricComplete : Set` fields;
  do not call mere fields proofs of metric completeness.
- Triple C3 symmetry alone does not prove a Lakes-of-Wada boundary.
- Source names `Wild` in the arithmetic/Monster lane concern wild
  ramification, NOT wild ambient topological embeddings.
- Explicit coordinates are not automatically embeddings or immersions.
- Ring-simplified / Python-checked algebra is not an Agda/Lean kernel receipt.
- Idaszak's Ida surface and Apéry/Morin eversion are different objects.
- Simons-cone critical-point algebra does not prove area minimality.

## Concrete maximal-reuse continuation cut

1. Use the existing `proofs/horned_c3_lean` and its Hatcher van Kampen donor
   for actual collared open covers; do not duplicate a separate abstract group.
2. For the three infinite-type surfaces, realise the finite oriented cobordism
   schedules as a locally finite collared union, prove connected orientable
   Hausdorff second-countable 2-manifold, then identify proper rays/end space.
   Apply Richards' classification only AFTER verifying genus/orientability/end.
3. For Wada, require genuine planar topology in Lean/Mathlib:
   nonempty pairwise-disjoint connected open sets U0,U1,U2 and
   `frontier U0 = frontier U1 = frontier U2`; construct a source-selected
   sequence of canals with *all three* boundary density properties.
4. Fox-Artin: upgrade the source-selected nested 3D placements, record
   local complements and 1-LCC rather than just global pi1.
5. Warsaw/Whitehead: instantiate actual sine-curve compactum and a
   CW/non-CW contrast. Do not treat ordinary finite cochain equality as
   weak homotopy equivalence.
6. For coordinate consumers: promote the actual real parametrisations using
   the existing geometry analytic surface, and pass global rank/injectivity
   obligations, with controlled singular exceptions (Whitney/Ida/Morin).
7. Seifert/Nielsen: implement genuine braid group (crossing generator of
   infinite order), combinatorial oriented diagrams, and mapping-class
   actions before using current finite permutation shadows.

## Source roots and authorship

- J. W. Alexander, 1924, horned sphere; A. Hatcher, *Algebraic Topology*
  Example 2B.2, for complementary group tower.
- R. H. Fox and E. Artin, 1948, wild arcs; R. J. Daverman and G. A. Venema,
  *Embeddings in Manifolds*, Chapter 2, for the local-cellularity distinction.
- Ian Richards, 1963, *On the Classification of Noncompact Surfaces*:
  https://people.dm.unipi.it/benedett/Richards.pdf
- Brouwer (1910) and Wada as described by Yoneyama (1917), the original
  three-lakes phenomenon. Modern source-specific example:
  Martí-Pete, Rempe and Waterman, *Wandering Lakes of Wada*,
  https://arxiv.org/abs/2108.10256
- H. Whitney, umbrella/pinch point; MathWorld source formula
  https://mathworld.wolfram.com/WhitneyUmbrella.html
- Ray Idaszak / George Francis, Ida surface, as documented by
  https://mathworld.wolfram.com/IdaSurface.html
- D. von Seggern, seashell parametrisation, as documented by
  https://mathworld.wolfram.com/Seashell.html
- E. Bombieri, E. De Giorgi and E. Giusti for Simons-cone area minimality.
- H. Seifert for oriented knot spanning-surface disk/band construction.
- J. H. C. Whitehead for CW weak-equivalence theorem; Brown/Mazur
  for generalized Schoenflies; Nielsen and Thurston for mapping classes;
  F. Apéry and B. Morin for sphere eversion.
- DASHI contributions here: typed reuse, precise scope separation, exact
  finite/cellular/coordinate verifications and the implementation matrix.
  Do not attribute any classical theorem's discovery to DASHI.

## Verification receipts

Executed locally (Python 3 + SymPy 1.14):
```sh
python3 scripts/exotic_topology_exact_models.py
python3 scripts/exotic_topology_surface_exhaustions.py
```
Both reported PASS in the model workspace before source mirroring. Source
code was committed on the stacked branch. Agda kernel typechecking,
Lean typechecking and GitHub CI for this exact branch were NOT RUN and
must not be labelled passed.


## Further constructive max-cut (same stacked branch)

### Warsaw circle: an ACTUAL compactum definition

`scripts/exotic_topology_warsaw_contour.py` implements the following
source-specific construction, rather than an arbitrary finite sine sample:

```
S = {(x, sin(1/x)): 0<x<=1} union ({0} x [-1,1])
A = segments [(0,-1)->(0,-2), (0,-2)->(1,-2),
              (1,-2)->(1,sin(1))]
W = S union A
```

**Exact witness of the entire vertical limiting segment:** for any
`t in [-1,1]`, take `x_n = 1/(2*pi*n + asin(t))`, `n>=1`.
Then `x_n>0`, `x_n->0` and `sin(1/x_n)=t`. Conversely every cluster
value along `x->0` lies in [-1,1], and away from x=0 graph continuity
identifies all closure points. Hence S is exactly the graph closure.
The graph has bounded coordinates in [0,1]x[-1,1] and S is closed,
so is compact. The added polygonal arc A is compact, is disjoint from S
away from its two endpoints (sin never goes below -1, and the x=1
cross-section contains only sin(1)), and connects the two indicated points.
W is therefore a compact connected planar continuum with the expected
Warsaw-circle defining shape. The script symbolically verified the
closure sequence identity/limit. The noncontractibility and vanishing
of ALL homotopy groups remain unformalised; neither finite cochains nor
point-set compactness prove them.

### C3 versus Wada: an explicit counterexample

`ExoticWadaC3BoundaryNoGoExact.agda` imports the SAME pre-existing
`FiniteC3OrbitStabilizerExact` and assigns the three sectors the
boundary-ray incidences (01),(12),(20). It proves all nine instances
of incidence equivariance under cyclic rotation and exhibits ray 0
where sectors 0 and 1 differ. Hence sector-permutation symmetry is
insufficient for identical boundaries even at incidence level.
This is NOT a full Euclidean realization theorem and does not exclude
source-selected Wada constructions with special interleaved canals.

### Two stronger positive mathematical identifications

1. **Whitney REAL image, not just equation.** For F(x,y,z)=x²-y²z,
   the parametrisation P(u,v)=(uv,u,v²) has precisely the semialgebraic
   image `{F=0 and z>=0}`. Inclusion is immediate. Conversely if
   y!=0, take u=y and v=x/y; the polynomial equality gives v²=z.
   If y=0, F=0 forces x=0; take u=0 and v=sqrt(z). Note that
   grad F=(2x,-2yz,-y²) vanishes on the ENTIRE z-axis, while
   the parametrisation's differential rank drops only at (u,v)=(0,0).
   This separates implicit algebraic singularities, real image and
   source-parameter immersion defects.
2. **Simons cone spherical link.** On the link with |x|²+|y|²=1
   and |x|²-|y|²=0, necessarily |x|²=|y|²=1/2.
   Thus its link is exactly S³(1/sqrt(2)) x S³(1/sqrt(2))
   as a subset of S⁷. Its minimality is a completely independent
   and still open formal target.

The typed Agda consumers above are source-written and have NOT been
typechecked in this environment.


## CW prior-art correction and decisive Mathlib reuse (2026-10-25)

User was correct that genuine CW-related work is already in DASHI;
earlier inventory was incomplete. In particular:

- `DASHI/Mathematics/AlgebraicGeometry/ProjectiveLineCellularH2Exact.agda`
  already constructs rational cellular degree-two cochains from the standard
  0-cell/2-cell CW decomposition of S²=CP¹, proves `H²=Q` in the
  FINITE CELLULAR MODEL, and welds its generator to projective-line
  cycle classes. **The module explicitly disclaims a cellular-to-singular
  comparison for an actual topological CP¹.**
- `DASHI/Reasoning/TernarySynthesisCellComplexExact.agda` has literal
  0/1/2 cell incidence and triangle-boundary laws, plus a proof-carrying
  PNF realisation interface.
- `DASHI/Mathematics/Topology/FiniteCochainComplexExact.agda` already proves
  differential-squared-zero, identity/composition cochain map laws,
  closed/exact transport, and homotopy-related statements.
- `DASHI/Topology/VisualPersistentHomologyCore.agda` has typed finite
  persistence signatures, although it does not construct topological
  cubical complexes.
- `DASHI/Topology/TernaryPantsFrontierExact.agda` and
  `TernaryCylinderPantsGeometryExact.agda` provide ternary 3/6/9
  frontier indexing and a **COMPOSED 1-to-3 cobordism** combinatorial
  correspondence. That is a four-boundary surface at the geometric
  level, not one conventional three-boundary pair of pants; the
  existing code denies a Euclidean embedding theorem.

Critical external prior-art found at **Mathlib Topology/CWComplex**:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CWComplex/Classical/Basic.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CWComplex/Classical/Finite.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CWComplex/Abstract/Basic.html

Mathlib DOES already implement genuine classical `Topology.CWComplex` and
relative CW structures (maps from finite-dimensional real disks, attaching
boundaries, closure finiteness and weak topology), finite construction
helpers `CWComplex.mkFinite` and related constructors, and categorical
`TopCat.CWComplex` via colimits. Thus do **not** rebuild a universal
CW library here. `proofs/horned_c3_lean/HornedC3/ExoticCWMathlibReuse.lean`
now imports these sources, records that a recognized space carries
actual `Topology.CWComplex` data, and rejects a finite-incidence
receipt as an authority substitute. No claim the supplied Mathlib
dependencies on the currently pinned Hatcher project compile this
consumer until run on that exact revision.

`ExoticCWExistingDonorWeldExact.agda` creates an ACTUAL typed
instance of the existing generic three-term cochain complex by reusing the
already-proved CP¹ degree-two cellular cochains. It uses the original
CP¹ `H²` round trips and point-cycle generator theorem, rather
than manufacturing a new cohomology quotient. Agda typecheck OPEN.

`scripts/exotic_topology_cw_donor_reuse.py` uses exact integer boundary
matrices and Smith normal forms. Verified locally: 11 canonical finite
cell complexes (point, circle, sphere, torus, pinched torus, RP²,
Moore Z/3, pants spine, handle spine, interval, filled triangle);
`∂₁∂₂=0`; rational Betti numbers; **integer torsion in H₁** when
the differential to C₀ vanishes. For example, point and RP² share
rational Betti numbers (1,0,0), but only RP² has Z/2 in H₁. A
homology coincidence therefore DOES NOT make a CW/homeomorphism or
Whitehead theorem. Finite surface-stage Euler identities are reconciled
with one-vertex 1D CW spines of rank `2g+b-1`, depths 0..12, WITHOUT
promoting a topological deformation retraction proof.

## Reuse between binary Cantor and 3/6/9 pants frontiers

`ExoticBinaryTernaryPantsCodecExact.agda` imports the existing
`TernaryPantsFrontierExact` and `CantorProjectiveCylinderMeasureExact`
(and existing 369 ultrametric address carrier). It establishes a
prefix-free **finite word code** `3 ↦ 0,` `6 ↦ 10,` `9 ↦ 11`
with an Agda source-written decode-after-encode round-trip, explicitly
rejecting a dangling leading `1`. The resulting binary words are the
literal original Cantor-cylinder representation. This is not a
depth-preserving map.

The infinite prefix-code maps constitute a **mathematical Cantor-space
homeomorphism**: concatenate each source ternary digit's finite code for
ternary-to-binary; greedily parse binary prefixes `0,10,11` for the inverse.
Every infinite binary stream admits a unique infinite parsing, with one
ternary digit requiring at most two input bits; conversely the first m
binary bits depend on at most m ternary symbols. These prefix bounds prove
continuity of both inverse maps in the product/cylinder topologies.
This topological argument is written, not a kernel-verified infinite-stream
map or continuity proof.

`scripts/exotic_topology_binary_ternary_pants.py` PASSED all finite
prefix-code antichains and exact dyadic Kraft sums through depth 8
(6561 words). The **crucial negative discriminator** is measure:
the ordinary fair-bit Cantor cylinder measure pushes to the nonuniform
ternary Bernoulli weights (1/2,1/4,1/4), **not**
the uniform ternary distribution (1/3,1/3,1/3).
For example, ternary word (3,6) maps to binary 010 of dyadic
mass 1/8, versus uniform ternary mass 1/9. Thus the canonical
Cantor end spaces can be homeomorphic while their selected measures
do NOT match under this map. No metric/isometric equivalence is
inferred. The 3-fold symmetry does not automatically commute with this
specific non-symmetric code.

## Local regression authority

`python -m unittest discover -s tests -p 'test_exotic_topology_maxcut.py' -v`
ran locally with 8/8 tests passing. These explicitly include a
non-chain-complex (∂² ≠ 0) rejection, an RP²-versus-point
torsion counterexample, an Ida seam, a no-false-GMT-minimality guard,
a no-false-Warsaw-homotopy guard, and biased binary/ternary measure.
No Agda or Lean kernel execution has been observed; draft PR remains
draft. Pinned Mathlib API compatibility must be checked before merging.


## 2026-10-25 dashi_lean4 actual topology donor audit

Companion native Lean draft: https://github.com/chboishabba/dashi_lean4/pull/86
Source branch: `agent/exotic-topology-cw-sphere-reuse-20261025`.

**Correction to earlier Agda-only inventory:** direct reads of the separate
`chboishabba/dashi_lean4` repository found genuine theorem-bearing objects:
- `Synthesis/MillenniumHodgeCP1Quotient.lean`: actual Mathlib
  `Projectivization ℂ (Fin 2 → ℂ)`, explicit quotient/charts.
- `Synthesis/MillenniumHodgeCP1TopologicalSphere.lean`: native
  `CP1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.
- `Synthesis/MillenniumHodgeCP1SingularTransport.lean`: actual
  `TopCat` singular chain and `H₂` functorial isomorphisms.
- `Synthesis/MillenniumHodgeSphereSimplicialBoundaryH2.lean`: literal
  `SSet.boundary 3`, finite tetrahedral cycle-space = Q.
- `Synthesis/MillenniumHodgeCP1CellularH2.lean`: finite cellular
  **cohomology** H² = Q on separate cochains.
- `Integration/UltrametricCensus.lean`, `Spine/FiniteReindex.lean`,
  `Integration/ObserverQuotient.lean`: existing exact finite donors.

`dashi_lean4` GitHub code search is unindexed; empty results in previous
repository-wide string searches are therefore NOT evidence of absence.

**New cross-repo completion:** Native Lean #86 now builds a source-written
homeomorphism from the ALREADY-PROVED `CP1 ≃ₜ UnitSphere2` to the
**literal** Mathlib `TopCat.sphere 2` carrier by ULift.
`Mathlib/Topology/Category/TopCat/Sphere.lean` (v4.28.0) defines
`sphere n = diskBoundary (n+1)`, where `diskBoundary n` is
`TopCat.of (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))`.
The exact existing `CP1` sphere is the n=2 case. Lean #86 also adds
a finite nondegenerate evaluation pairing on the original CP1-cellular
H² and tetrahedral H₂ providers; that is **not** the singular comparison.

**Exact pinned Mathlib check:** `dashi_lean4/lakefile.toml` declares
mathlib v4.28.0, and its tracked manifest pins
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
The *actual source* contains `Topology.CWComplex` and constructors
`Topology.CWComplex.mkFinite`, `Topology.CWComplex.mkFiniteType`;
the earlier `CWComplex.mkFinite_map` name was wrong.
Native Lean #86 now consumes these exact classes rather than building
a new general CW layer. The repo's `lean-toolchain` currently reads
`v4.35.0-rc3`, which must be reconciled/preflight-checked against its
mathlib v4.28 pin; no silent package retargeting.

**Higher-value Hatcher donor:** `Deicyde/hatcher-at/Hatcher/Sphere/Homology.lean`,
original Lean author **Jack McCarthy**, contains
`Hatcher.Sphere.reducedHomology_sphere`, supplying reduced homology
on literal `TopCat.sphere n`, source-attributed to Hatcher's
Corollary 2.14. The upstream hatcher-at environment is Mathlib/Lean
v4.34.1; do NOT directly import its proof in Lean v4.28.0 or
promote external source metadata to an actual target-revision theorem.
Use explicit pin-consistent dual-environment acceptance.

Native Lean #86 additionally constructs the real Whitney polynomial
and Simons cone unit-link algebra and a *genuine topological* Wada
three-domain frontier acceptance type, distinguishing actual
`frontier (U i)` from the finite Agda three-sector incidence shadow.

**Remaining decisive join:** choose a compatible, actual homology/cohomology
comparison on `TopCat.sphere 2`, then connect the native tetrahedral
normalized chains and the CP1 cellular cochain model to that SAME
singular complex; do not identify `H²` and `H₂` merely because
both have coefficient rank one. A source-owned actual Wada example,
Fox-Artin local wildness, and Richards end-space realisations remain
separate geometric obligations. Native Lean #86 is draft and NOT
freshly kernel typechecked in this environment.


### Native Lean #86 final additions (same dated cut)

On actual `dashi_lean4` carriers, not reconstructed in Agda:
- `Synthesis/ExoticTopologyWhitneyRealImage.lean`: source-written
  complete real semialgebraic image iff `x²=y²z ∧ z≥0`, with
  explicit inverse parameters in the two `y=0/y≠0` cases.
- `Synthesis/ExoticTopologyCP1SphereH2Acceptance.lean`: the
  literal rational ordinary-singular-H₂ hypothesis for
  `TopCat.sphere 2` compiles via existing native functorial
  transport into an exact conditional CP¹ H₂ isomorphism.
- `scripts/exotic_topology_lean_donor_audit.py`: local SymPy PASS,
  including 225 rational Whitney-inverse checks, integral tetrahedral
  boundary-matrix rank, rational pairing and negative controls.

All added Lean proof sources remain uncompiled in this runtime, and
the Hatcher reduced-homology donor still needs a matched ordinary/reduced
chain comparison plus source pin reconciliation. Existing Agda
CW-cellular and pants modules remain authoritative for their respective
finite carriers; neither repository's proof is automatically the other's.


### 2026-10-25 native Lean #86: actual quotient / Warsaw / end-profile expansion

The separate Lean repo now has **real point-set source constructions**
in draft PR https://github.com/chboishabba/dashi_lean4/pull/86 :

- `Synthesis/ExoticTopologyPinchedTorusQuotient.lean` defines a
  genuine topological quotient of `S¹×S¹`, collapsing one selected
  meridian. It source-writes a continuous quotient-map proof,
  meridian collapse and off-meridian separation. Our earlier
  Agda/Python pinched-torus cellular Betti vector (1,1,1) is
  still a DIFFERENT object until a cellular/singular same-object
  comparison is supplied.
- `Synthesis/ExoticTopologyWarsawCircle.lean` defines the
  actual closure of the topologist's sine graph in `ℝ²`,
  adjoins the selected polygonal closing arc and makes a
  subspace carrier. The vertical-limit formula was checked
  symbolically but still needs kernel proof of closure membership;
  weak contractibility, noncontractibility and failure of CW
  type are independent OPEN acceptance theorems.
- `Synthesis/ExoticTopologySurfaceExhaustions.lean` reuses
  `Integration.Address.Addr n Bool` for literal finite Cantor
  boundaries and supplies source-written finite-stage
  Euler/genus/graph-spine theorems for Cantor tree, Loch Ness
  monster and Jacob's ladder. This is NOT Richards classification,
  a global collared surface or a homeomorphism of end spaces.
- `Synthesis/ExoticTopologySeashellParametric.lean` reuses the
  existing Lean real `Point3`, imports Mathlib trigonometry,
  and source-writes radial and seam identities.

Thus the revised classification of the original twenty objects is:
`CP1/S2` topologically realised in preexisting Lean main,
`pinched torus` has a new literal quotient-topology carrier,
`Warsaw circle` has a new literal planar closed-set construction,
`Whitney` and `Seashell` have source-specific coordinate
realisations, and `Simons` has exact algebraic link data.
The other requested spaces, including the full infinite-type
surfaces, remain finite models or stated acceptance contracts
where no same-object geometrical proof was supplied.

All newly authored Lean theorem sources remain uncompiled in
this environment. The companion Agda branch is stacked and stale
relative to parent #1244, and no kernel cross-prover identity
is asserted. The original authors and external Mathlib/Hatcher
proof owners are retained.


## 2026-10-25 reconciled stack, corrected ancestry and Richards theorem cut

The child PR #1254 was merged **non-destructively** with the
inspected parent #1244 head `97cda338ed87c70304135fddd62093a8f78852a2`
in merge commit `f0a45715e976b34512b311667b51c02c425b0639`
without overlapping path edits. Direct compare at that point:
35 commits ahead, zero behind parent, 17 changed topology paths.
The parent may advance after this snapshot; do not infer
permanent merge readiness from this receipt. PR remains draft.

The earlier first-loop Cantor scheduler was insufficient:
same finite manifold invariants and b=2^n need not
mean every old branch split. The repaired
`exotic_topology_pl_frontier_lineage.py` uses EXACT marked boundary
vertices and maps through existing oriented PL gluing.
It enforces `p->p0,p1` on every old boundary *once*,
and deliberately tests a genuine valid four-boundary PL
counterexample with incorrect ancestry. Old count-only
checks remain useful geometry regression, not end-space proof.

`Docs/topology/ExoticInfiniteSurfaceEndSpaceConditionalTheorem20261025.md`
now gives the eight-step mathematical conditional route
from collared nested finite PL surfaces through
Richards' nested proper unbounded complementary region
end topology and planar/nonplanar end data to the
three canonical surface types. Each still-open geometric
hypothesis and kernel obligation is explicit. Companion
Lean #86 source-writes the tower-to-stream two-sided
equivalence on existing `Integration.Address` carriers.

Attribution: compact bordered-surface classification
Brahana (1921); ideal-boundary predecessor Kerékjártó
(1923); full triangulable noncompact surface theorem and
realization Richards (1963). The paper route is a
mathematical conditional argument, not a new Lean/Agda
kernel receipt. The new tests have **NOT** been freshly
run on the exact updated SHA.


## Latest 2026-10-25 PR re-audit and source-scoped discriminator

Latest relevant donors inspected at their actual heads:
- Horned #1244: `ThreeArmCollarCoverAssembly.lean` already supplies
  conditional central-region / three-satellite van Kampen cover
  assembly; `AlexanderHornedBinaryTernaryExistingCodecWeldExact`
  already imports canonical 2/3 refinement and older ternary codecs.
  Do not duplicate or call it a geometric Fox--Artin embedding.
- Braid/modular #1239: genuine Artin (B_3) modular `SL₂ℤ`
  matrix shadow and separately typed C3 framing-loss and finite T9
  actions. Source first: Artin (1925, DOI 10.1007/BF02950718);
  Artin (1947, DOI 10.2307/1969218), not the repository PR.
- Newest biology #1259: `QueryIndexedProjectionAdequacyExact`
  already uses `IntersectionalNonFactorability`; the original
  `ExoticAmbientLinkingNoGoExact` has been WELDED to that exact
  generic witness, to show sector-query adequacy versus linking-query
  inadequacy and all-rechart nonrecoverability.

New finite regressions:
`scripts/exotic_topology_braid_crosspr_discriminator.py`,
`scripts/exotic_topology_cantor_measure_obstruction.py`.
The first proves, at the exact group-matrix level, that endpoint
permutation and modular images have different nontrivial kernels.
The second isolates a STRONGER topological obstruction than a biased
chosen code: **no measure-preserving homeomorphism** between
the fair binary Cantor product and uniform three-letter Cantor
product because clopen measures on the former are dyadic and
the latter has a clopen set of measure 1/3.
Mathematical compactness/cylinder lemma is documented, all-depth
prime-divisibility source-written in Lean #86, kernel pending.
Two extra unit regressions were added to the existing focused suite.

`.github/workflows/exotic-topology-focused.yml` follows the
parent #1244 dedicated-workflow pattern and can execute the
finite Python audit at a specific GitHub SHA. Merely committing
this workflow is NOT a passing run; independent local algebra
checks passed, but no executed exact-head workflow receipt
is represented as present here. All prior major geometric
acceptance conditions remain open.


## 2026-10-26 balanced-ternary/SSP369 exact geometric cross-owner max-cut

The user's already-in-repository balanced/ternary conjectural carrier
is now directly used, rather than restated from first principles:

- `DASHI.Algebra.Trit`, `Codec.BalancedTritBitFibre`:
  **three distinct signed/zero trit states**, zero support fibre;
- `Geometry.SSP369Ultrametric`,
  `Foundations.BalancedTernaryUltrametricExact`:
  **already-proved** finite ternary-prefix and agreement types;
- `Topology.TernaryCylinderPantsGeometryExact` and
  `Topology.TernaryPantsFrontierExact`:
  the exact already-composed **TWO-pants 1→3**
  branch-slot/finite-prefix append laws;
- `ExoticBalancedTernaryPantsWeldExact.agda` (new):
  two-sided address/path translation and reuse of exact
  ternary-prefix agreement and pants append naturality,
  explicitly **choosing** digit3↔negative, digit6↔zero,
  digit9↔positive. Sign inversion is order two with
  fixed zero, not the order-three C3 rotation;
- `scripts/exotic_topology_balanced_ternary_pl.py` (new):
  **ACTUAL FINITE ORIENTED PL** 1→3 branch as TWO
  copies of the existing three-holed genus-zero pants.
  It does not confuse a four-boundary branching
  cobordism with one ordinary three-boundary pants.
  It imports original `MarkedSurface`, `attach`,
  vertex-link manifold and complementary dual-component
  checkers. Bounded source regression through depth
  three gives boundary counts 1/3/9/27, genus zero,
  external attached-component counts 1/3/9, and zero
  retained as a real final outgoing boundary.
- Existing variable-length `3→0,6→10,9→11` binary
  prefix codec is reused EXACTLY. The geometric
  two-pants tree realises this branching decision tree
  at finite stages; natural binary codeword weights
  1/2,1/4,1/4 are not uniform ternary 1/3 each.

**Executed receipt:** Independent local implementation of
the same finite PL triangulation and dual-edge/complement
conditions actually PASSED at depth three; the final
mesh has 7,723 triangles and 27 live outgoing boundary
circles. New source-specific test methods on #1254
are committed but NOT verified by an exact-GitHub-head
Actions or Agda kernel receipt.

**Original author separation:** compact-surface topology
Brahana (1921); noncompact end classification
Kerékjártó (1923), Richards (1963); TQFT/cobordism
vocabulary Atiyah (1988); mathematical finite-prefix
and coding notions belong to their classical sources.
The explicit balanced↔369 sign-chart selection and
this particular finite PL audit are user-directed,
AI-assisted implementation choices in DASHI,
not discoveries attributed to those historical authors.
Source module authorship and paper source provenance
remain distinct.

**Same-type frontier:** a properly collared infinite
3-child genus-zero surface has Cantor-space planar
ends, hence the SAME homeomorphism type as the binary
Cantor-tree surface under Richards' theorem.
That infinite geometric hypothesis is still OPEN
in the repo. Binary/ternary topology equivalence
does NOT imply measure-preservation, group
isomorphism, an isometric ultrametric identification,
or a homotopy equivalence of a totally disconnected
address tree and its connected 2D pair-of-pants pieces.

**Wrong-object controls from newest PRs:** #1261's
26-point punctured balanced T³ / thirteen antipodal
directions and #1260's 81×243 additive Eisenstein
quotient remain categorically different carriers;
no equality follows from having ternary symbols or
27/3⁹-related counts. #1239's Artin braid and #1244's
Alexander horn C3 remain separate from balanced
sign reflection and this 2D surface exhaustor.

Full original twenty-space proof completion remains
bounded by actual infinite 2-manifold, Richards ends,
Fox-Artin/Wada/Warsaw/Hatcher/Simons and all other
source-specific unproved geometric theorems.


## 27 October — actual same-graph spherical caps pay genus-zero finite planarity

NEW `scripts/exotic_topology_genus_zero_sphere_caps.py`
consumes the ORIGINAL oriented triangle meshes and labelled
frontiers, with no new triangulation engine. For every
positive-depth binary Cantor or balanced-ternary source
stage tested, each outgoing boundary circle has EXACTLY
three edges. The script adds its REVERSE-ORIENTED
missing triangle. This does not add a vertex or edge.
It checks no 2-simplex is duplicated, and runs the
original full oriented manifold vertex-link checker
on the resulting CLOSED (g,b)=(0,0) surface.

The result is a genuine same-graph **finite simplicial
sphere capping witness** at depths one and two:
- binary original stage counts b=2,4; capped is
  a closed orientable genus-zero triangulation;
- balanced original stage counts b=3,9; same result.
A source-independent locally run reconstruction
verified all four caps plus unchanged 1-skeleton.
These are mathematical FINITE receipts, not a Lean/Agda
kernel result or proof of any infinite realisation.

**Critical negative controls:**
- The initial disk is ONE 2-simplex. Simply adjoining
  the opposite-oriented face on the SAME three vertices
  duplicates a simplex, violating an abstract simplicial
  complex (though a Δ-complex might allow two face maps).
  The original 1-skeleton is directly the planar K3;
  this is treated separately, not called a two-simplex
  triangulation of S².
- Performing this operation on a positive-genus handled
  stage produces a CLOSED genus-g surface, NOT a sphere.
  The source checker correctly rejects its false
  genus-zero acceptance.

**Mathematical `(3,6)` conclusion with clearly typed sources:**
A graph of a finite triangulated genus-zero surface
with three-edge boundary circles is planar, and its
same-graph cap supplies an explicit planar embedding
for positive depths. Every subgraph on v≥3 vertices
therefore satisfies e≤3v−6 by the classical
simple planar-graph edge bound. Together with the
**general** proven-on-paper Euler–Maxwell identity
3V−E=6−6g and g=0, these selected finite genus-zero
graphs meet the (3,6)-tight DEFINITION.
This uses a standard topological planar-subgraph
inequality beyond the directly checked executable
numerical formula. No Graph theory kernel theorem
or Power-style minimal 3D rigidity statement is
claimed, nor is the all-depth closure established
by four bounded caps.

**Modern source first:** Stephen C. Power (2025),
DOI 10.1112/blms.70083, Theorems 4.5/6.4,
proves existence of specially chosen (3,6)-tight
and 3-rigid noncompact surface triangulations.
Our finite same-graph sphere caps are
user-directed repository-local implementation,
not authored by Power or a new proof of his
infinite rigidity theorem. Earlier compact
surface classification remains Brahana;
Kerékjártó/Richards own the noncompact genus/end
classification, and no classification priority
is revised by citing a newer proof.

The remaining highest-value formal cut is:
(1) instantiate `ExoticSimplicialStarTransportExact`
with the ORIGINAL uniform all-n surface gluing;
(2) construct the countable locally finite
geometric realisation as a single topological space;
(3) prove compact exhaustion and Richards actual
end-cylinders on that same object;
(4) optionally use Power's more specialised
vertex-split/0-extension construction to obtain
its (3,6)-tight/minimally-rigid infinite graph.

The exact-head focused suite has now gained six
Power/Maxwell/cap regression methods since
the earlier 32-test count (38 total).
The local reconstruction is independent;
the pushed GitHub test suite and new Lean
source still lack successful kernel/Actions receipts.


## 27 October continuation — original twenty-object acceptance and structural Power cut

The **original inquiry** now has its own authoritative phase-and-deliverable
matrix rather than being summarized by seven higher-fanout subproblems:

- `Docs/topology/ExoticTwentyOriginalInquiryPhaseDeliverables20261027.md`:
  **exactly 20 named source-selected objects**, each with its
  strongest honest current evidence and the SAME-OBJECT source-specific
  missing theorem. Six acceptance phases specify real mathematical
  and verified kernel gates, from reproducible SHA receipts through
  locally finite geometry, genuine Richards decorated end classification,
  to all remaining wild/homotopy/GMT example obligations.
- `scripts/exotic_topology_twenty_acceptance_ledger.py`:
  fail-closed original-inquiry inventory validator requiring
  20 unique names in the original order, six stages and a no-promotion
  status. A deliberate missing-row regression must fail. A passing
  bibliography checklist is explicitly NOT a theorem.
- The original 13-root historical provenance atlas and seven
  Pareto proof-dependency leaves are NOT replaced by 20 fabricated
  independent scientific sources or by an invented uniform
  mathematical proof. They have different jobs.

**NEW mathematical owner: the Power boundary SURPLUS NECESSITY.**
Power, 2025, `10.1112/blms.70083`, Theorem 4.5 and 6.4 are
CONSTRUCTIVE EXISTENCE theorems for selected noncompact-surface
triangulations; 2024 preprint `arXiv:2403.11986` is the same
intellectual root. Existing `3F=2E-L` and
`V-E+F=2-2g-b` give:

```text
3V-E = 6 - 6g - 3b + L
whole graph Maxwell equality 6  <=>  L = 3b + 6g
whole graph necessary sparsity >=6  =>  L >= 3b+6g
```

New Lean #86 source-written exact linear arithmetic theorems:
`tightWholeGraphIffBoundaryBudget`,
`sparseWholeGraphRequiresBoundaryBudget`,
`lochNessNecessaryBoundaryLength`,
`jacobLadderNecessaryBoundaryLength`.
These are NOT Agda/Lean kernel receipts. The current source
finite bordered Loch genus-n, b=1 stage needs L=3+6n;
Jacob genus-2n, b=2 stage needs L=6+12n to satisfy the global
Maxwell equality. Source triangles currently enforce L=3b,
which explains a 6-edge budget per handle.

**A MATERIAL NEGATIVE CONTROL PREVENTS FALSE COMPLETION.**
`scripts/exotic_topology_power_boundary_surgery_counterexample.py`
subdivides exactly 6g boundary edges in the original *source*
PL triangulation, preserving orientability/genus and attaining
whole-graph Maxwell =6. It then selects the **literal old
vertex set** and counts only the edges in its induced subgraph.
This produces a fully finite explicit witness to continued
(3,6)-sparsity failure:

| Selected stage, at one handle transition | Geometric repair | Whole-graph f | Induced old-core vertex count | Induced old-core edge count | **Core f** |
| --- | --- | ---: | ---: | ---: | ---: |
| Loch Ness g=1,b=1 | Six boundary edge subdivisions, L=9 | 6 | 36 | 107 | **1** |
| Jacob g=2,b=2 | Twelve subdivisions, L=18 | 6 | 218 | 659 | **-5** |

Both selected core subgraphs have at least three vertices, and
Power's definition requires f>=6 on **EVERY** such subgraph.
Thus a mere global boundary-length repair cannot imply
the target theorem. Source-equivalent *independent local
Python* triangulations actually passed both counts and
orientable-surface checks. They are NOT execution receipts of
the exact newly committed GitHub blob.

**Constructive next alternative:** use original Power §4
vertex-splitting, Henneberg 0-extension, and rigid-subgraph
substitution with the actual all-subgraph sparsity and
boundary girth constraints. Extending the present selected
mesh *only at the boundary* is ruled out by the explicit
core counterexample; it does NOT contradict the source
existence theorem or close the finite stage in the desired
sparse/rigid structure.

**Pareto revised order:** P0 fix/execute exact-head
kernels; P1 instantiate a genuine uniform gluing
`StarChain` on the real all-n PL carrier; P2 prove
countable simplicial realisation/compact cofinality and
true Richards decorated ends (three of twenty original
objects); P3 use Power's **selected special**
triangulation construction only if rigidity is an
additional deliverable; P4 wild source-geometric
Alex/Fox/Artin, Hatcher sphere, Wada, Warsaw, and
remaining source-specific hard theorems. Do not
let the elegant (3,6)-tightness *subgoal* displace
the original Richards/topological classification
goal, which does NOT require rigid frameworks.

Historical rights and source-claim separation remain:
Richards (1963) classifies noncompact surfaces;
Power (2025) adds special graph triangulation/rigidity
constructions and a streamlined argument; these are
different theorems. No DDC/QID guess, reused paper
as "independent corroboration", or finite run as
kernel check is allowed.
