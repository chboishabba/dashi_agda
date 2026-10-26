# Alexander/Hatcher C3 × SU3 inquiry: original question, max-cut and phase-gated deliverables
**Date:** 2026-10-27 (Brisbane). **Lane:** hyperfabric Agda PR #1249 and Lean4 PR #84.
**Related original owners:** horn topology PR #1244; selected neutrino/W PR #1247;
exotic-topology PR #1254 / Lean #86; original SU2 gauge simulator PR #1244.
**Do not copy, merge or recast another worker's theorem as an original result.**

## 0. Reconstruct the ORIGINAL inquiry before grading subclaims

**Topological question:** Does the specified same-object three-sector boundary-connected-sum
Alexander/Hatcher horned ball have an actual C3-equivariant wild exterior E whose
fundamental group is G_A * G_A * G_A, the commutator-marked perfect Hatcher
group in each sector, and an order-three OUTER action from ambient rotation?

**Mathematical-gauge question:** Can a genuinely marked nontrivial non-Abelian
representation of this full commutator tower be realized by a flat SU2/SU3
connection on the SAME E while respecting a physically meaningful **uniform
gauge regularity / shrinking-loop** condition? Is there an unavoidable
regularity obstruction at the wild boundary?

**Physical question (strictly downstream):** Is any physical SU3 Wilson
conjugacy class selected by an anomaly-safe matter action / renormalized
spectrum rather than hand-picked? Is there a distinguishing observable
beyond arbitrary free groups and ordinary loops? Could this lead to
neutrino/PMNS, KK/TOE, or gravity constraints that survive real data?

The root inquiry is NOT fulfilled by a finite SU3 matrix, one nontrivial
Wilson fringe, a 120-element 2I section, a tame C3/Cantor endpoint, or a
synthetic gate circuit.

## 1. First-link attribution graph

| Source root / implementation owner | Actual ownership | Evidence status |
|---|---|---|
| J. W. Alexander, 1924, DOI 10.1073/pnas.10.1.8 | Original wild sphere | Classical source; NOT authored by the repo |
| Allen Hatcher, Algebraic Topology Example 2B.2 printed pp171–172, original PDF https://pi.math.cornell.edu/~hatcher/AT/AT.pdf | Nested X_n, increasing Y_n, free F_(2^n) stage groups, parent-to-child commutator monomorphisms, trivial abelianization | Original mathematical exposition, original pages visually checked; NO Euclidean short-loop rate supplied |
| Morikuni Gotô, 1949, DOI 10.2969/jmsj/00130270 | Every SU3 element a commutator | Classical commutator-existence theorem, not a representation geometry, not a selected W |
| Classical van Kampen / Hatcher §1.2 Example 1.21, upstream Deicyde/hatcher-at | π₁(rose_r)=F_r and cover free-product consumers | Existing published/library mathematical/formal donor, re-used |
| Hatcher paper-to-geometry horn PR #1244 | 3-sector C3 cap/tubes, source-written radius open cover, central basing, conditional Hatcher-at homotopy/path group transport, tame controls and original 2I simulator | Paper geometry + exact finite tests + source-written Lean; actual wild relative satellite equivalence and exact-head kernel pending |
| Original selected W / neutrino PR #1247 | Explicit cyclotomic post-hoc W, exact rational trace and qutrit fringe; NuFIT falsification and ring controls | Selected synthetic matrix and executable tests; NOT physical selection or measured lepton properties |
| This hyperfabric #1249 / Lean #84 work | Sharp unitary sibling arc, W exact spectral cubic, selected child-gap thresholds, source-conditional Stokes and marked-systole bounds, F2/Hopf/ribbon discriminators and finite-observability no-go | Mathematical derivations and finite exact tests; conditional Lean/Agda SOURCE files NOT kernel checked |
| Exotic #1254 and Lean #86 | Generic chronological Cantor event and finite PL surfaces/controlled negative models | Separate mathematical owners; DOES NOT prove horn wild complement |
| Yutaka Hosotani 1989 DOI 10.1016/0003-4916(89)90015-8 | Dynamical Wilson-line one-loop potential on specified compact/smooth gauge background with matter | Original mechanism reference, NOT a computation on the Alexander wild exterior |

**Attribution implementation convention:** original research/theorem priorities, later expository
interpretation, original GitHub file owner, user-directed DASHI changes, AI assistance,
local exact checks, native kernel receipts, physical experiments are DISTINCT claim types.
No unverified DOI, QID, Dewey, compiler success, physical selection or independent
experiment is invented.

## 2. The NEW MAX-CUT: every finite Wilson-word test has a tame replica

**Exact mathematical theorem (conditional on correct finite geometric stage marking):**
Fix n, the genuine Hatcher stage group in 3 C3 sectors is F_(3*2^n).
Let e_n identify its marked generators with those of the tame bouquet
R_n=∨_(3*2^n) S1. For ANY group-target representation
ρ_n:F_(3*2^n)→SU3, let the tame rose assign the SAME
receiver matrix to the corresponding circle generator.

For EVERY word w at this stage, and ANY receiver observable
f:SU3→V (including spectrum, Wilson trace, even full receiver
matrix up to the usual gauge covariance),

    f(ρ_n(w)) = f(ρ_tame,n(e_n(w))).

This is an identity of group homomorphisms by the universal
property of the free group. It holds for every number of finite
word queries, every ancestor/leaf commutator and every consistent
three-sector relabelling by C3. **NO FINITE STAGE WORD OBSERVATION,
however accurate, determines ambient wildness.**

It emphatically does NOT say the spaces are homeomorphic,
that meridian geometrical lengths/curvature areas match,
that a tame replica realizes ALL levels in a single uniformly
regular source gauge, or that a finite experimental device
has identical noise/transport error.

**Original donors:** Hatcher Ex2B2 finite stage/word maps and
Hatcher Example1.21 rose group, already formalized as
Hatcher.fundamentalGroupEquivWedgeCircles in the pinned
Deicyde/hatcher-at theorem library.
**Current contribution:** select the right observation class
and make the exact factorization/no-go into a cross-prover consumer.
Do not attribute free group theory as a newly discovered theorem.

**Executable exact local receipt:**
`scripts/check_horn_finite_wilson_word_nonidentifiability.py`;
the independently executed
`/mnt/data/check_horn_finite_wilson_indistinguishability.py`
checks all source free-word ancestor expansions and coherent C3
transport through depth6, exact SU3 SU2-block matrix readings of
all three sectors and ancestors through depth4, and word size
L_n=4^n per root. PASS. The identical code bytes committed to
GitHub have not separately been executed unless separately checked.
An unoptimized three-root circuit has 3*4^n elementary-letter
appearances: 3072 at n5 and 3145728 at n10.
**These are word lengths, NOT a proved minimum gate complexity.**

**Lean conditional formalisation**:
`Integration/DASHITOE/HornFiniteDepthWilsonWordNonidentifiabilityCut.lean`
composes an explicit finite-stage group equivalence with an
arbitrary receiver homomorphism and any receiver observable.
The actual Hatcher relative wild geometric source-to-rose stage
marking is an EXTERNAL input and Lean kernel NOT RUN.

## 3. PARETO PHASE TABLE: WHAT IS ACTUALLY PAID?

| Phase and acceptance | Currently established | Missing/stop gate | Deliverable |
|---|---|---|---|
| **P0 — Original roots & exact data** | Alexander/Hatcher/Gotô/Hosotani roots, distinct repo owners, Hatcher's free stages and original selected W source | None for SOURCES; no claim of full original PDF edition priority | `source_attribution.md`, DOI/path/PR ledger (this document) |
| **P1 — Abstract topology/algebra** | G_A injective free commutator tower, perfectness, abstract C3 external factor action, abstract non-Abelian SU3/2I representation, finite C3 word model | Some repo-specific native Lean/Agda exact kernel compiles outstanding; no physical identification | Source-typed algebraic specification and focused compiler receipts |
| **P2 — Actual same-object three-copy wild geometry** | Paper-level supported wild 3-ball gluing and explicit C3 radial cover; pinned Hatcher-at van Kampen and new #1244 conditional based path/homotopy transport | Actual Hatcher-relative collared satellite ↔ actual cover-member equivalence, central/member connectedness and π1 witnesses, native kernel | A named meridian + punctured-torus peripheral annulus, inclusion on π1, actual relative source maps and C3 naturality |
| **P3 — Real metric + flat regularity** | Exact W spectral bound ||W-I||op²>517/250, first child d>781/1000, sibling-tail c(31/60)²<1, conditional local marked-systole no-bounded-gauge | SAME Hatcher source marked meridian loop with whole-stage avoidance, Euclidean L or Lipschitz Λ bound, compatible physical/gauge regularity | One explicit local-short-loop certificate and then branchwise flat-gauge no-go or a counterexample |
| **P4 — Curved gauge dynamics and selection** | Conditional direct one-step W rejection from child d<=3/4 with TRUE based eta<=23/500, synthetic qutrit/fringe, classical flat YM F=0 action=0 | Actual based Stokes homotopy/area, curvature norm, source manifold domain, renormalized matter spectrum, anomaly cancellation and genuine W selection | Source-specific dynamic action + calibrated parameter-free/predeclared prediction; none currently validated |
| **P5 — Experimental identifiability** | Existing finite 2I and SU3 ideal/noisy simulator, paired C3/commuting/F2 controls, exact finite-word nonidentifiability proof | Physical platform, source-associated calibration/geometry, multisale regularity or topological observable NOT reproducible by tame free-stage model | Publishable nonabelian benchmark distinct from a WILDNESS detection; only latter can claim topology |
| **P6 — Formal/publication/reporting** | In-repo source-written Lean/Agda, executable exact finite controls and attribution docs | Exact-head native kernel proofs + verified geometric assumptions, physical likelihood against NuFIT/etc where relevant | Two separate papers/reports: conditional mathematics vs testable physics (not one unsupported TOE claim) |

This is NOT a declaration that P2/P3 geometry/physics are complete.
The mathematical object can be interesting even when the selected
physical W is not dynamically selected.

## 4. Ranked max-cut next actions (not wish-list snowball)

**First same-object gate (highest fan-out):**
Use original #1244 `ThreeArmHatcherHomotopyTransport` and
`ThreeArmHatcherPathTransport`, not new duplicate Hatcher-at
group representations. Construct supported wild satellite W_i
with explicit relative cap/collar maps into actual U_i, a
marked π1 F₂ attachment whose incoming one-boundary annulus
reads [a,b], stage-to-stage commuting inclusions and true C3
transport. The previous finite Hopf clasp is a beautiful
metric linked model but WRONG GROUP (π1 Z²); the correct F₂
finite two-tube model with ribbon order is STILL NOT the
actual infinite Hatcher source. Reject either substitution.

**Second gate (high analytic fan-out):**
For this SAME source identify one branch of marked meridians
gamma_w with L(gamma_w)→0 in the actual exterior and real
common-gauge connection bound ||A||<=M. Source-dependent chart
L(gamma_w)<=2πΛ_w b_w is sufficient if Λ_w b_w→0.
The root source-selected flat gap immediately rejects
a first child if M*L<=781/1000; the generic infinite branch
gives necessary repeated d(sibling)>31/60.
A topological homeomorphism or shrinking cylinder diameter
WITHOUT meridian length control does NOT pay this step.

**Third gate (curved physical branch):**
Obtain the actual based parent-word homotopy and estimate
eta through transported F_A integration; use source-verified
gauge fields and same basepoints. If curved fields escape
the flat regularity no-go, quantify their curvature/area cost
and stress; NO inference from pure gauge coefficient
blowup to gauge-invariant energy.

**Independent engineering lane:** run existing #1244
2I simulator and #1247 SU3 two-arm qutrit with paired
commuting, F2, tame free-stage and C3 controls; report it as
non-Abelian interferometry, NOT wildness. A finite Wilson
sequence alone cannot discriminate by theorem above.

**Physical selection lane (strictly last):** fixed matter
content, anomaly-safe representation, source self-adjoint
domain/renormalization, Hosotani-like one-loop potential;
predict Wilson eigenphases/PMNS before checking NuFIT and
compute an honestly source-validated likelihood. If
post hoc fit, explicitly classify as fit, NOT prediction.

## 5. Sharp stopping/falsification rules

- If the purported local Hatcher source group is Hopf π1 Z²
  instead of F₂, STOP: its parent commutator vanishes.
- If it has F₂ but only a three-boundary pants ribbon
  instead of a one-boundary punctured-torus attaching
  annulus, STOP: peripheral source map missing.
- If geometric loop lengths are inferred from a mere
  HOMEOMORPHISM or end-cylinder diameter, STOP:
  metric distortion is uncontrolled.
- If a finite Wilson trace/word circuit is claimed as
  a wildness detector, STOP: the tame rose reproduces
  the entire finite-stage word system.
- If flat F=0 is invoked to dynamically select a
  particular W or source local curvature stress,
  STOP: pure classical flat Yang-Mills does not select it.
- If a source-written conditional Lean/Agda theorem
  is called kernel-verified without exact-head
  compiler receipts, STOP.
- If any physical lepton/TOE/neutrino claim has
  no independent calibrated prediction and
  anomaly-safe coupling, STOP.
- Never count a reprint, an unmerged PR, one
  source repeated three times, or an analogy as
  independent mathematical/experimental evidence.

## 6. Concrete report packaging / status

**D1:** Source/owner evidence ledger and original scientific
question — THIS FILE, committed on existing Agda #1249.
**D2:** Conditional abstract/algebraic theorem and sharp W
numerical certificates — in #1249/#84 already;
native kernel still open.
**D3:** New finite word-only observer no-go,
committed Python + conditional Lean;
local exact independent tests PASS.
**D4:** Actual same-object meridian/annulus/collar geometry,
not yet certified.
**D5:** Actual geometric shrinking/systolic and curved
Stokes certificates, not yet certified.
**D6:** Independent finite SU2/SU3 simulator and
honest ordinary-graph/F₂ wildness-negative control;
software precedent exists, no physical device built.
**D7:** Actual source-derived physical prediction and
predeclared test/likelihood, not yet available.

**Original-inquiry assessment:** abstract possibility of
nonabelian source-holonomy PAID mathematically; topology
same-object partly constructed but not fully certified;
a strong conditional regularity obstruction exists;
finite holonomy-word observations cannot detect
wildness; the selected W is POST-HOC and not dynamically
selected. The research is currently in **P2/P3
source-geometric bridge**, not final P4/P5 predictive physics.


## 7. Finite horizon versus ONE-STEP EXTENDABILITY (important source firewall)

Each **individual** finite Hatcher stage has a free group
and permits nontrivial homomorphisms F_r→U(1).
Yet the original Hatcher inclusion takes EACH old
generator to a commutator of two next-stage
generators. Any target abelian character of the
next stage sends that commutator to identity.
Therefore a nontrivial abelian representation of
the current stage **cannot extend even a single
level** compatibly with the true Hatcher stage map.

This is a direct consequence of the ORIGINAL
Hatcher commutator inclusion, and the existing
Agda horn owner #1244
`AlexanderHornedAbelianHolonomyBIDIExact.agda`
already formalises the all-depth abelian
triviality. The hyperfabric finite-word script
now checks source exponent-sum zero at depths
1..6 in all three C3 sectors; this is a new
regression consumer, **not a new theorem owner**.

By contrast, a nontrivial SU3 root can be
abstractly recursively split into commutators
by the ORIGINAL Gotô 1949 theorem, with choices
at every node and depth. This establishes
group-theoretic extendability, not bounded
flat gauge potentials on the actual metric
wild exterior. The two results sharpen the
experimental roadmap: checking ONE finite
horizon or its entire Wilson table cannot
detect wildness; checking compatible extension
and geometric/regularity constraints is
materially more demanding.

The original physical proposed SU3 W and
finite 2I simulator are NOT implied by
the abelian extension theorem, and an
artificial finite rose graph assignment
is NOT a wild-specific hardware effect.


## 8. Late LIVE source-owner refinement: member connectivity reduced, not invented

The final cross-PR check found the original horn geometry
owner #1244 had advanced to
`e2f63fd512c76ce4bf3a174b118c475398c27f79`,
adding
`proofs/horned_c3_lean/HornedC3/ThreeArmRadiusConnectedAssembly.lean`.
That ORIGINAL-OWNER source now uses Mathlib
`IsPathConnected.union` to derive each radius
cover member's path connectivity from:
(1) true path-connected central region C in
the ACTUAL exterior E; (2) true path-connected
satellite intersection S_i in E; (3) a real
exterior point p_i in the actual C∩S_i.
The intended rational p_i=13e_i and
sphere placement are in the paper-level
owner construction, but the lemma does not
pretend ambient R³ points are automatically
elements of the exterior E.

This pays a NONDUPLICATE formal assembly
step and reduces (does not eliminate)
the source topological P2 witness count.
Open are the actual central connectedness,
central fundamental-group triviality,
each satellite region's connectedness,
overlap point membership in the true
wild exterior, supported Hatcher relative
wild satellite equivalence, and native
Lean kernel check. Nothing here changes
the finite all-Wilson-WORD tame replica
no-go, or supplies a short source meridian.

The stacked exotic topology #1254 additionally
made PL simplicial star stability improvements;
its proper infinite-surface realization and
ambient wild linking remain independent,
unpaid source claims. Do not merge sources
by adjacency in the PR list.

Under Ibrahim first-link accounting, #1244 owns
this new union theorem consumer; Mathlib owns
the original theorem, and this #1249 note
only records dependency reuse. No independent
mathematical discovery or completed kernel
proof is claimed on behalf of the owner.


## 9. Independent general observer-owner reuse (#1266), without false merge

A final source-proximal snowball inspected
Agda PR #1266 `agent/revisable-observer-proofsearch-maxcut-20261026`,
which owns
`DASHI/Core/RevisableObserverConsumerFactorizationExact.agda`.
Its source-written generic
`collisionObstructsConsumerFactorization` proves
the correct decoder principle:
if two histories/models yield the SAME observed
output but DIFFERENT intended consumer answers,
the answer cannot factor through that observation.

Our finite-Hatcher-vs-tame-rose all-Wilson-word
construction supplies a concrete source-specialized
COLLISION of this kind, for the
answer "is the actual embedding wild?"
and observation "all finite-stage Wilson
group-word receiver values." This is a
derived WILD TOPOLOGY consumer of #1266's
general factorization framework and original
Hatcher free-group theorem, not new attribution
of the original generic no-decoder principle.

**Important branch boundary:** #1266 is a
different OPEN branch, so no direct Agda import,
implicit merge, or kernel proof of the new
collision is claimed on #1249. The Lean
finite-stage word equality on #84 is
source-written separately and concrete, and
the same-object wildness label relies on
original geometric Hatcher/topology rather
than a finite free presentation alone.

The proof-search interpretation:
the false decoder is a precise *failed
identifiability* result; target experiments
must add an observable coordinate not
factorable through a single finite-stage
free-group representation—e.g. a source
metric shrinking-loop / gauge regularity
constraint or physically calibrated curvature.
A different finite list of Wilson traces
cannot overcome the no-go by increasing
precision or invoking a C3 permuted label.
Original owner credit #1266 and Blackwell/
Cousot as background remains intact.


## 10. Final owner-head update: actual ambient overlap-point certificate

Horn owner #1244 advanced again to
`11a1ea0ba81755b726f430d117a0c4f36eeeb170`.
Its NEW `scripts/alexander_horned_c3_radius_overlap_witness.py`
reuses the original explicit cover and basing-path
scripts, computing exact rational p_i=13e_i in
the central/arm overlaps with own squared
centre distance 16 and all foreign squared
distances 250, strict cut radii 15/4 and 17/4.
It also checks these p_i avoid prescribed
radius-one satellite envelopes, the central
unit ball and the three straight spoke-tube
boxes; wrong inner/outer point controls fail.
This is more specific than just an abstract
conditional point and should be reused as an
owner geometry donor.

However its own source states clearly that
this is an AMBIENT coordinate/envelope witness.
It is not an exact-head Lean proof of a
full wild satellite E, path-connected arms,
central pi1, source relative Hatcher
peripheral equivalence, or short actual
Hatcher meridian. The independent
`ThreeArmRadiusConnectedAssembly` can
then consume true X-valued points and
source connectedness once supplied.
No source status is upgraded by its
new focused workflow registration.

This pays part of P2's explicit overlap
coordinate check but does NOT move the
original inquiry to P4 physical selection.
The present finite word-observation no-go
remains valid in its explicitly marked
source/receiver scope.


## 11. NEW all-depth acyclic CW telescope comparator — stronger identifiability MAX-CUT

The previous result that any FINITE Hatcher stage is
matched by a tame rose has an all-depth classical
topological strengthening. Original Hatcher Example
2B.2 gives the injective free-stage child-commutator
tower; ORIGINAL Hatcher Section 3.F (printed p312)
gives the mapping telescope as countable CW mapping
cylinders, finite truncation retractions and homology
direct limits. Build R_n as a 3*2^n-circle bouquet;
f_n sends each old circle to its new sector-preserving
child commutator, strictly C3-equivariantly.
The ordinary mapping telescope T has

    pi1(T)=colim F_(3*2^n)=G_A*G_A*G_A,
    H_k(T;Z)=0 (k>=1), H0(T;Z)=Z.

Each finite truncation retracts to the last rose.
The induced map on H1 is ZERO, because each
old circle becomes a commutator; the directed
limit of these homology groups is zero. Injectivity
of Hatcher's original π1 maps leaves π1(T)
NONTRIVIAL. Height-compactness ensures any
sphere map lies in some finite truncation, so
π_k(T)=0 for k>=2. T is an aspherical acyclic
NONCONTRACTIBLE 2D CW K(G,1) with a cellular
C3 action, NOT a smooth/embedded 3D wild ball.

Thus **even ALL-DEPTH abstract SU3 group-holonomy
characters** can be transported from the true
source's group to this explicitly NON-3D
group-equivalent CW model. The group alone
does NOT select the ambient wild embedding.
The actual three-arm π1(E) equivalence remains
conditional on #1244's still-uninhabited
relative geometry. This derived consequence
does not claim novelty over the classical
mapping-telescope/acyclic-group literature.

New deliverables: Agda #1249
`scripts/check_horn_c3_acyclic_rose_telescope.py`
(verified pushed source), full exact/Pareto ledger
`docs/hyperfabric-horn-c3-acyclic-telescope-all-depth-source-cut-20261027.md`,
and Lean #84 source-written
`HornC3AcyclicMappingTelescopeCut.lean`
with finite scalar rank and explicitly
CONDITIONAL all-depth group/receiver equivalence.
Independent locally implemented finite audit
through n8 PASS; committed Python script
NOT byte-identically replayed and actual
2D CW geometry NOT Lean-kernel formalized.

Research decision update: the actual
wild-three-dimensional P2 G1/G4 source
geometry, plus P3 true Euclidean local
meridian lengths/regularity, are
MATHEMATICALLY NECESSARY to turn abstract
all-depth group representations into a
spatially distinctive result.
Any more finite (or abstract all-depth)
Wilson-only emulator is relevant to
non-Abelian engineering but cannot be
a wildness identifier by group data alone.
P4 source matter/quantum-action selection,
P5 calibrated physical discrimination
and P6 kernel/publication remain separate.


## 12. Latest #1244 compact exhaustion owner result

Original horn owner #1244 at head
`a5fb69cc24299e96b91145083cefaf09cdf8e32f`
now adds `HatcherOpenExhaustionCompactAbsorption.lean`
using Mathlib `IsCompact.elim_directed_cover`.
It proves, conditionally on an ACTUAL monotone
OPEN exhaustively covering sequence Y_n,
that a compact loop/homotopy image factors
through some one stage. Its exact locally
source finite controls show closed-only
or non-directed covers do NOT suffice.
The source geometry Y_n and stage
nonabelian π1 injections remain
separate and OPEN. This code is
original #1244/Mathlib donor work,
not an original theorem of #1249.

The new 2D telescope comparator likewise
has compact finite-height absorption,
but is **NOT THE SAME TOPOLOGICAL SPACE**
as the genuine exterior and cannot
instantiate #1244's 3D marked handlebody
geometry. This sharper dual-example
makes the actual wild source proof
even more important, not less.


## 13. Independent acyclic telescope local exact audit

Local independently implemented audit
`/mnt/data/horn_c3_acyclic_telescope_independent_audit.py`
SHA256 `e0340f7a7627bfe2271a276d2319e0ed43dcbac3a95426f61aa579cf28687241`
was ACTUALLY executed and PASS through n8.
It independently certifies exact symbolic C3
commutator words, zero H1 abelianization maps,
presentation-chain column ranks and finite
rose stage ranks. The separate GitHub committed
source `check_horn_c3_acyclic_rose_telescope.py`
was fetched but not byte-replayed from
the pushed blob. Full infinite 2D CW
telescope topology and Hatcher 3D wild
embedding are NOT Python-tested or
Lean/Agda kernel verified.


## 14. P1 strengthening: non-split free stages and residually solvable receivers

The original Hatcher Ex2B2 source stage map
`f_n:F_(3*2^n)→F_(3*2^(n+1))`
replaces EACH old marked generator with the
commutator of its two DISJOINT new child letters.
An exact word normal-form argument proves
`|f_n(w)|red=4|w|red` for every freely
reduced word w (and 4^k over k refinements),
not just one chosen root. Thus the original
source injection is ALGEBRAICALLY faithful.

However each stage H1 map is ZERO,
so no stage f_n has a group-homomorphic
left inverse: any old generator's nonzero
abelian character would become a
commutator and vanish. A genuine
topological stage retraction Y_(n+1)→Y_n
splitting the intended inclusion would
induce such a forbidden group retraction.
This derived non-splitting obstruction
is compatible with the previous 2D
acyclic CW mapping telescope and closes
a tempting false shortcut treating stages
as retracting nested rose subgraphs.

The nontrivial limiting group G_A is
PERFECT, and therefore ANY homomorphism
G_A→R into a RESIDUALLY SOLVABLE receiver
R is trivial: further solvable quotients
kill a perfect image, while residual
solvability separates nonidentity points.
Original free-group residual nilpotence
(Magnus and classical Iwasawa/Nielsen
Schreier lineage) thus implies in
particular `Hom(G_A,F_r)` is trivial.
A limit-group-to-finite-stage free-group
retraction is not merely unavailable:
even a nontrivial map in that direction
is impossible. This is original
group-theory inheritance, NOT a new
perfect-group discovery by DASHI.

A real finite SU3 receiver can ALSO
be a false positive for all-depth
extension. Classical 3×3 Weyl
clock/shift matrices X,Z in SU3 obey
`[X,Z]=ω²I ≠ I` yet generate a
two-step nilpotent order-27 Heisenberg
subgroup, so `[[a,b],[c,d]]=I`
for ALL a,b,c,d in that subgroup.
The independent locally EXECUTED
SymPy+finite-27-element exact audit
`/mnt/data/check_horn_nilpotent_clock_shift.py`
SHA256 16d709fbbe738b90b4fb7f7199075d4823ce5d5e80c5b52bddc40da1a4a54eee
PASS verifies all 729 pairs and the
nontrivial first commutator versus
trivial second-depth one.

NEW Agda #1249 committed:
`scripts/check_horn_stage_nielsen_injection_nonsplitting.py`,
`scripts/check_horn_su3_nilpotent_clock_shift_extension.py`,
and original-source/author ledger
`docs/hyperfabric-horn-hatcher-nonsplit-residually-solvable-20261027.md`.
Independent locally EXECUTED word test
`/mnt/data/check_horn_commutator_stage_nonsplit.py`
SHA256 73974d5b70f96772838d2be1226ffa4a74fc2a4ed84d73183a28ff28b95ec447
PASS on 4,687 F3 words and 17,569 F6
words, plus C3 and abelianization.
The GitHub uploaded files are NOT
claimed byte-identically replayed;
native Lean kernel not run.

Lean #84 now contains source-written
`HornHatcherStageNonsplittingCut.lean`
reusing the prior exact abelian commutator
detector, and
`HornNilpotentSU3ExtensionNoGoCut.lean`
requiring a TRUE depth-two source
Hatcher marking and a class-two receiver.
The original #1244 AbelianHolonomyBIDI
owns its earlier abelian-target
all-depth no-go; current solvable
extension is a classical derived
generalization, not replacement.

**Experimental acceptance revision:**
finite 2I/qutrit benchmarking must
test compatibility beyond depth1
and specify the RECEIVER SUBGROUP
generated by actual hardware gates.
A nontrivial first-level holonomy
in a two-step nilpotent subgroup
cannot witness the perfect Hatcher
all-depth group. Conversely nontrivial
all-depth abstract SU3 is possible by
original Gotô but still not spatially
wild or physically selected.
P2 remains true wild supported
satellite/punctured-torus Hatcher
meridian with same-source metric;
P3 Euclidean length; P4 real
curvature/matter, P5 physical
calibration; P6 native kernels.


## 2026-10-27 TOE normalized import convergence — O/R/C/S/L/P/G/F

**O — Objective:** Attach existing horn finite source gates to canonical
`DASHI.EverythingTOESymmetryResolved369`. The terminal TOE is not proved.

**R — Roots:** Alexander/Hatcher original wild topology; existing #1244
C3 geometric source and #1249 horn source-conditional Agda modules.
Existing `DASHI.Unifier`, `DASHI.Unified.PNFHyperfabric`, and
`DASHI.Unified.Physics` are the actual TOE carriers. Original
Deicyde/hatcher-at, meta-introspector, and source-repo authors retain
independent attribution; no code was copied from external repos.

**C — Preconditions:** existing file/module pairs at the chosen PR
branch; stage avoidance needs a true source stage and marked loop;
ribbon perimeter is finite dart algebra only. Original Hatcher
relative wild satellite map and Euclidean gauge connection absent.

**S — Invariants:** No ESD edits, no new generic theorem, no constructor
or default proof to imply a wild meridian, no imported experimental
evidence. Never call a source-written file kernel-verified.

**L — Lane:** One nonblocking import-edge lane on hyperfabric #1249.
The three TOE parent imports and the two existing horn exact modules
are imported by the existing top-level TOE aggregate. No other
module or cross-repo branch was edited.

**P — Postconditions:** The 369 aggregate now reaches the original
Unifier and Unified physics/PNF parents and already-existing
stage-clearance and ribbon boundary exact modules. It does NOT
turn conditional geometric source claims into a complete TOE.

**G — Gates:** Deterministic GitHub HEAD fetch confirmed all six
module names match their paths and all five imported target modules
exist at the same branch. The target import count is eight including
its original three imports. Local Python exact source tests pass.
The environment has no Agda executable or available local
dashi-agda-preflight index. Thus a kernel typecheck and local
related_symbols/discover/round_lineage receipt remain UNVERIFIED.
GitHub code search identified existing owner declarations and the
preflight API, but does not replace the local referee.

**F — Fail-closed:** If any import is absent from another PR head,
do not promote or merge. The original `DASHI.Unifier` contains
explicit abstract/axiomatized proof interfaces, and
`DASHI.Unified.Everything` contains an existing malformed tail
on this branch. Neither defect is fixed by a pure aggregate import.
Next work requires a reproducible local Agda build, branch-wide
preflight, then a separately scoped repair of the FIRST proven
import or syntax failure. No work was done on
`dashi_digital_esd`, `*digital_esd*`, or `*ESD*`.

**Management crosswalk:** ITIL change record = this one-path
import change. ISO 9000 = module existence and deterministic
acceptance. ISO 42001/NIST AI RMF = evidence and proof-state control.
ISO 27001/27701 = read-only external/IP-sensitive repositories and
ESD scope. ISO 23894 = failed-source promotion risk.
ISO 9241 = concise explicit proof status. Six Sigma = zero missing
target imports in the inspected head. C4/PlantUML conceptual flow:
TOE369 -> Unifier / Unified Physics / Unified PNF /
HornStageClearance / HatcherRibbon. No new architecture.
