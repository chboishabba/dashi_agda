# All-depth Hatcher C₃ mapping telescope: acyclic nonwild CW countermodel and phase-cut
**Date:** 2026-10-27 Australia/Brisbane.
**User-directed lane:** Agda hyperfabric #1249; Lean4 consumer #84.
**Independent owners:** actual 3D horn geometry #1244; selected W/neutrino #1247;
generic revisable observer factorization #1266; exotic PL topology #1254.

## 1. Original sources and strict claim attribution

- J. W. Alexander (1924), *An Example of a Simply Connected Surface
  Bounding a Region Which Is Not Simply Connected*, DOI
  10.1073/pnas.10.1.8: original wild embedded topological 3-ball.
- Allen Hatcher, *Algebraic Topology*, original author PDF
  https://pi.math.cornell.edu/~hatcher/AT/AT-doublepage.pdf:
  **Example 2B.2, printed pp171–172** (author-PDF doublepage pp89–90),
  gives actual embedded horn X_n, stage groups F_(2^n), injective
  child-commutator maps, and direct-limit fundamental group.
  **Section 3.F, printed p312**, mapping telescope for a sequence
  of cellular maps; finite truncations deform-retract onto the final
  stage and ordinary CW/direct-limit homology machinery.
  These are TWO classical original textbook sources, not a new
  discovery of mapping telescopes or Hatcher group.
- Classical van Kampen and CW compactness justify pi1(colimit)
  of the pointed telescope as direct limit of free-stage groups;
  induced H1 on each rose is the abelianized child word.
- Pinned Deicyde/hatcher-at formalization of Hatcher wedge-circle
  free groups belongs to UPSTREAM AUTHORS and should be
  imported by existing horn owner #1244, not rewritten in this lane.
- PR #1244 owns the specific outer C3 action, wild-sector geometric
  scaffolds and Hatcher-at source group/path glue. PR #1247 owns
  the selected cyclotomic SU3 matrix and prior finite qutrit signal.
  Earlier #1249/#84 own sharp arc, W spectral cubic, marked systoles,
  wrong-source Hopf/pants controls and the finite-word no-go.
  #1266 owns generic consumer nonfactorability principle.
  No reassignment or double-counting of that work.

## 2. Constructive abstract all-depth comparator

Let R_n be a finite *pointed bouquet* of 3*2^n circles, labelled
by (s,w), s∈Z/3 and w∈{0,1}^n. Define a pointed cellular map

    f_n:R_n→R_(n+1)
    e_(s,w)↦e_(s,w0) e_(s,w1)
                e_(s,w0)^(-1) e_(s,w1)^(-1).

This uses EXACTLY Hatcher's original group transition in all
three sectors. At every n the sector permutation
r(e_(s,w))=e_((s+1) mod 3,w) satisfies

    r∘f_n = f_n∘r,    r³=id.

Consequently the usual mapping telescope

    T = Tel(R_0 → R_1 → R_2 → ...)

is a countable **2-dimensional CW complex** with a cellular C3
action. By van Kampen and ordinary compactness of loop/homotopy
images in a bounded-height truncation,

    π1(T) ≅ colim_n F_(3*2^n)
          ≅ G_A * G_A * G_A.

The latter equality is as ABSTRACT groups and uses
Hatcher original injective transition plus the ordinary
finite free product/direct-limit decomposition.
The original geometric source #1244 still needs to
certify π1(E) ≅ that same abstract group for the literal
three-copy wild exterior. NO homeomorphism E≅T is asserted.

### Acyclic but noncontractible (derived from classical theory)

Every finite truncation T_≤n deformation retracts onto R_n,
so H_k(T_≤n)=0 for k≥2 and H1(T_≤n)=Z^(3*2^n).
The induced map

    H1(R_n) → H1(R_(n+1))

is the ZERO map because each e_(s,w) is a commutator.
Thus by the classical direct-limit theorem for CW homology,

    H_k(T;Z)=0  for EVERY k≥1,
    H0(T;Z)=Z.

The telescope is therefore **ACYCLIC**. Nevertheless,
its fundamental group is NONTRIVIAL: each old free generator
persists under Hatcher's original injective commutator
homomorphism. So T is NOT contractible. Its higher
homotopy groups also vanish: a sphere map into T has
compact bounded telescope height, factors into a
finite truncation, and that truncation retracts
onto an aspherical bouquet of circles. Therefore T
is a **2D acyclic aspherical K(G_A*G_A*G_A,1)** CW model.

These are classical CW consequences applied to a
source-selected group tower, not newly discovered
acyclic groups or a 3D wild sphere. Compare the real
source exterior in S3, whose reduced homology is
already trivial by Alexander duality for an embedded
closed ball; acyclicity does not prove 3D embedding
or Euclidean loop regularity.

### Finite cellular receipt, exact rational/integer checks

In the finite cellular mapping-telescope presentation
through n, there are

    1-cell generator occurrences =
       3*(2^(n+1)-1);
    2-cell mapping-cylinder relations =
       3*(2^n-1);
    free rank after eliminating old generators =
       3*2^n.

The cellular boundary of each relation 2-cell has
coefficient +1 on the UNIQUE old parent and ZERO
on each new child in the abelianization, since the
commutator exponent sums cancel. So the d2 columns
are independent, giving H2=0 and
rank H1=3*2^n; higher degree cells absent.

**Implementation:**
- Agda PR #1249
  `scripts/check_horn_c3_acyclic_rose_telescope.py`:
  verifies exact free reductions, C3 naturality, finite
  word length 4^(k-n), all 3-sector stage counts,
  cellular matrix rank and H1 zero transition
  n≤7, with nontrivial reduced root words through n8.
- Independently implemented locally in Python:
  stage counts, exact commutator expansions,
  C3 rotations and nontrivial root words PASS.
  The pushed GitHub file was verified by blob, but
  NOT byte-identically replayed from that blob
  in a local Python interpreter; the classical
  all-depth conclusion is source-text reasoning,
  not proved by finite execution.
- Lean PR #84
  `Integration/DASHITOE/HornC3AcyclicMappingTelescopeCut.lean`:
  scalar finite cell counts and a conditional
  all-depth group-isomorphism-to-receiver theorem.
  The actual CW telescope construction, its
  homology, the geometric Hatcher exterior group
  equivalence, and native Lean kernel checks are
  EXTERNAL; we do not invent library declarations.

## 3. All-depth receiver nonidentifiability — stronger than finite horizon

If the source wild exterior E has the claimed
abstract π1, a true abstract equivalence
α:π1(E)≃π1(T) transports ANY group representation
ρ:π1(E)→SU3 to a representation

    ρ_T = ρ∘α^(-1):π1(T)→SU3.

Thus for ALL words g, ALL stages and ALL receiver
functions F (including a Wilson trace/spectrum),

    F(ρ_T(α(g)))=F(ρ(g)).

The same group-level C3 automorphism can be
conjugated across α. This does NOT produce
the original spatial R³ rotational isometry
on T; it produces a cellular/permutation C3
action on an abstract 2D complex.

An SU3 representation of T yields a flat
topological principal SU3 bundle / local
system by the classical universal-cover
construction. It does NOT yield a bounded
smooth R³ connection, finite-energy field,
or physical wild horn experiment, since T
is not an open 3-manifold at all.

Consequently even **ALL-DEPTH ABSTRACT GROUP
HOLONOMY** cannot, on its own, recover wild
three-dimensional embedding from a labeled
group. No finite or infinite inventory of
abstract Wilson characters alone is a wildness
detector. Actual ambient/metric geometry, small
marked loops, compatible gauge regularity, a
spatial 3D manifold structure or a physically
calibrated curvature response must enter the
consumer.

This is exactly a higher-value source example
of #1266's generic `ConsumerFactorization`
collision/no-decoder theorem (source-written,
on a separate OPEN PR). Reuse that theorem
by reference; DO NOT merge #1266 silently,
reclaim original observer authorship, or
promote source-written kernels.

## 4. Severe source controls

1. A finite rose agrees at a chosen n but
   does NOT carry the same all-depth group
   unless its embeddings/relations are
   included in a telescope. Our earlier
   finite-word no-go is true yet WEAKER
   than this classical all-depth comparator.
2. A pure Hopf-link exterior has π1=Z²
   and kills child commutators; cannot
   replace Hatcher's local F2 attachment.
3. A two-generator F2 pants thickening
   has the WRONG three-boundary peripheral
   structure relative to Hatcher's required
   one-boundary punctured torus.
4. The correct F2 punctured-torus finite
   model still needs SAME-OBJECT embedding
   and relative map to a genuine wild
   satellite in actual 3D Euclidean space.
5. The acyclic CW telescope is not a
   3D-embedded wild sphere or even a
   smooth 3-manifold. Its abstract π1
   and zero homology do NOT pay a Euclidean
   meridian length or bounded-gauge source.
6. Flat classical YM local action F=0
   cannot dynamically select the chosen W;
   Hosotani matter spectrum and genuine
   renormalized model are separately open.

## 5. Revised max-cut / Pareto / Ibrahim phase priority

| Phase | Current result | Next ACCEPTANCE |
|---|---|---|
| P0 historical sources | Original Alexander/Hatcher/Gotô/Hosotani and repo owners audited | Keep direct first-link provenance, never invent DOI/QID |
| P1 abstract group/W | Comm tower, C3 group action, selected SU3 W, ALL-DEPTH telescope and acyclic CW comparator | Exact-head kernel for missing telescope CW and group-isomorphism proof, separately from original classical textbook facts |
| P2 actual 3D wild embedding | #1244 C3 envelope, collar and radius-cut, Hatcher-at gluing adapters | G1/G4 real relative Hatcher wild satellite, named F2 peripheral annulus and C3 naturality |
| P3 Euclidean/gauge regularity | Source-conditional marked systole bound and flat no-bounded-gauge theorem | One correctly marked actual short meridian or quantitative Λ_w b_w bound in full finite-stage exterior |
| P4 curved physical dynamics | True based eta>=0 concept, selected W one-stage exact threshold | Real Hatcher based curvature/Stokes source, matter/gauge action, renormalized selection, anomaly checks |
| P5 experiment/identifiability | Synthetic nonabelian qutrit/2I works in mathematical simulation; finite AND all-depth abstract Wilson characters are topology-nonidentifying | Source-specific geometric/regularity observable and separately calibrated physical platform |
| P6 publication/kernel | Source-written Agda/Lean and independent exact finite tests, original attribution ledger | Exact-head Lean/Agda build, real linked embedding proof, source-specific physical prediction before NuFIT likelihood |

The **Pareto frontier has sharpened**:
The topological P2 source-to-metric join is not just an
implementation inconvenience — it is mathematically
indispensable to recover the ORIGINAL spatial research
question from an acyclic all-depth group-equivalent CW
counterexample. Stop creating finite word/trace
models as proxies for wildness. Concentrate on
actual marked meridian geometry and same-source
regularity/curvature, with P4 dynamical selection
strictly downstream.

## 6. Falsification and final statuses

**DONE in this cut:** one explicit ALL-DEPTH CW
telescope construction and classical proof of
acyclicity, noncontractibility, asphericity,
group-level C3 equivariance and abstract
all-word receiver matching; exact finite
stage audit source and conditional Lean
group/scalar module; reconciled original
source roots and repository owners.

**NOT DONE:** native Lean/Agda kernel theorem
of telescope construction; exact same-object
3D wild exterior relative satellite equivalence;
Euclidean Hatcher meridian loops/length rates;
a smooth bounded field or genuine based
curved Stokes surface; physically selected
SU3 Wilson class; anomaly-safe matter;
laboratory observation or neutrino mass
prediction. No physical experiment is
claimed to have occurred.

**Reference and source-method discipline:**
Original theorems belong to original mathematicians.
Current finite scripted model and derived inquiry
analysis are user-directed work with OpenAI ChatGPT
assistance, not original ownership of mapping
telescopes, perfect groups or acyclic K(G,1).
One source quoted repeatedly is ONE source root;
models sharing π1 are not the same spatial 3D object;
a source-written theorem is not a kernel receipt.
