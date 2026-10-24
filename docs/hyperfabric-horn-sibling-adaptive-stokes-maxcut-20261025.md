# Hatcher horn: sibling-adaptive holonomy and source Stokes budget (2026-10-25)

## Attribution and actual prior-art reuse

* **Allen Hatcher**, *Algebraic Topology*, Example 2B.2, pp. 170–172,
  https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, is the original source for
  the linked Z-block topology, injections F_(2^n) -> F_(2^(n+1)),
  and parent generator represented by a commutator of its two children.
  **Hatcher does not assert any metric rate for selected descendant loops.**
* **Morikuni Gotô**, *A theorem on compact semi-simple groups*, *J. Math. Soc.
  Japan* **1** (1949), 270–272, DOI 10.2969/jmsj/00130270, supplies the
  original compact semisimple group commutator-surjectivity theorem.
* Existing DASHI **Agda PR #1247**, including
  `tests/test_neutrino_horned_su3_positive_bridge.py`, already uses Gotô
  and Hatcher to establish **abstract existence** of a compatible SU(3)
  homomorphism with its selected infinite-order W at the root. That existence
  is NOT a new claim of this PR, and is not a physical selection mechanism.
* Original linked C3/finite simulator and geometry owner: Agda **PR #1244**.
  Original chosen exact W trace/norm source: Agda **PR #1247**.
  The previous sharp universal coefficient 2, one-fast-branch cut and
  arbitrary curvature defect recurrence: Agda **PR #1249**, Lean **PR #84**.
* Non-Abelian holonomy/curvature variation is standard connection theory.
  An accessible derivation of the surface dependence is *Alternative
  Derivation of the Non-Abelian Stokes Theorem in Two Dimensions*,
  *Symmetry* **15** (2023), 2000, DOI 10.3390/sym15112000. The analytic
  integral estimate below assumes a **smooth based unitary homotopy**;
  its applicability to a horn Z-block is NOT verified by that paper.

## New elementary improvement: control the sibling, not only the leaf

For unitary U put d(U)=||U-I||_op. For unitary A,B,
```
d([A,B]) = ||AB-BA||_op
         <= 2*d(A)
         <= 2*d(A)*max(1,d(B))   [we do NOT use this weaker line]
d([A,B]) <= 2*d(A)*d(B)
```
because AB-BA=[A-I,B-I] as an additive commutator.
Combine these as
```
d([A,B]) <= c(B)*d(A),   c(B)=2*min(1,d(B)).
```
The symmetric result holds if the branch chooses B instead.
This refines the *already established* universal factor 2, without
asserting a new optimal all-unitary constant.

For an actually marked branch, let B_k be the sibling at depth k,
U_k the chosen path holonomy, and eta_k the curved parent-to-child-word
defect. The exact iterated inequality is
```
d(U_root)
 <= [product_(i=0..n-1) c(B_i)] * d(U_leaf)
    + sum_(j=0..n-1) [product_(i=0..j-1) c(B_i)] * eta_j .
```
Empty products equal 1. Existing 2^n and weighted-eta envelopes
are immediate weaker upper bounds since 0<=c(B_i)<=2.

### New FLAT consequence (no shrinking leaf needed)

For any unitary leaf, d(U_leaf)<=2. If the SOURCE really supplies
**sibling local representatives** of lengths
```
L(B_k) <= L0*q^k ,  0<q<1,
```
with one uniform finite bound M on the source connection norm along
these local loops in compatible gauge frames, then
```
d(U_root) <= 2 * (2*M*L0)^n * q^[n(n-1)/2] -> 0.
```
Hence the root holonomy is exactly I. No leaf length hypothesis, no
q<1/2 cutoff and no finite group image assumption are needed in this
**conditional geometric theorem**. This DOES NOT assert that Hatcher's
specific three-copy horned embedding has such genuinely marked short
sibling loops. Mere shrinking diameters or unlinked surrogate collars
cannot fill the source obligation.

Unbased local sibling loops are enough for the norm *if* they genuinely
represent the selected based child classes: arbitrary basepoint whiskers
conjugate unitary holonomy and preserve d. This does NOT eliminate the
topological requirement to verify which class each local meridian marks.
For flat connections the homotopy word equality is valid; for curved
connections it is not.

### CURVED acceptance bridge: replace arbitrary eta with actual area

For a smooth based homotopy H_k(s,t) between the parent source loop
and the **actual concatenated commutator** of transported children,
the unitary holonomy variation identity gives a conditional estimate
```
eta_k <= integral_[0,1]^2 ||F_A(H_s,H_t)||_op ds dt
      <= K_k * Area_param(H_k)
```
where the last K_k is an actual uniform curvature-form operator bound,
and Area_param is the corresponding absolute Jacobian area in the chosen
metric. The first bound uses isometric parallel transport for unitary
connections; it is not an assertion that these homotopy strips exist
with small area in the source horn geometry. Source supports must avoid
the removed wild set, and loops/basepoint must be coherently based.

The selected neutrino W from PR #1247 has independently certified
`d(W)^2 >= 854996726408/648677790003 > 1`. Thus the actual marked
geometry/connection is incompatible with selected W whenever a finite
sibling/curvature budget gives the displayed RHS <=1.

## Exact tests and deliberate negative controls

New Agda #1249 executable:
`scripts/check_horn_sibling_adaptive_stokes_maxcut.py`.

* 33 heterogeneous rational product/error envelope identities and
  dominance of the old 2^n envelope.
* Illustrative q=3/4 sibling gaps, root flat contradiction at depth 7
  with **uncontrolled terminal gap bounded only by 2**.
* Illustrative curvature budget K=1/100, area_k=(1/2)^k, same depth 7.
* Failure to reject when sibling gaps are uncontrolled, or eta_root=2.
* SU3 exact-family numerical matrix sanity checks when numpy is present.

These are synthetic acceptance fixtures, not actual horn arclengths,
calibrated gauge curvature or experiments. They provide regression
discriminators for any future source candidate.

New Lean #84
`Integration/DASHITOE/HornAdaptiveSiblingStokesCut.lean`
source-writes the sibling amplifier, certified heterogeneous rational
chains, envelope propagation and selected-root rejection. The operator
norm-to-coefficient lemma and real Stokes surface-to-eta construction
remain EXTERNAL premises; Lean/Lake and Agda kernel were not executed.

## Pareto / snowball / Ibrahim source-to-proof queue

1. **Highest-value topology source producer:** actual Hatcher Z-block
   linked embedding, genuine child/sibling generator labels, local
   sibling-loop arclengths and nonzero clearance from later horns.
   A single coherent geometrically decaying *sibling family* is now
   enough for a uniform bounded FLAT no-go, regardless of leaf rate.
2. **High-value curvature producer:** based homotopy surfaces wholly
   inside the open exterior, parametric Jacobian-area and transported
   curvature estimates; then evaluate the adaptive product/error
   budget. The geometry cannot be replaced by a Cantor address or
   symbolic commutator word.
3. **Existing positive-control reuse:** PR #1247's abstract Gotô
   representation and standard flat-bundle existence; PR #1244's
   simulator; existing DASHI `FlatFormalDiskHolonomySurface` is a
   target/authority socket, NOT yet an analytic Stokes proof.
4. **Physical selection and measurement:** candidate bundle/domain,
   matter and gauge action, anomaly/spectrum check, actual observable
   and comparison to ordinary-ring interferometry. Until built, no
   new neutrino prediction, wild-horn topology detection, Witten/Monster
   identity, finite-energy theorem or TOE claim.
5. **Stop rule:** do not promote an abstract group representation into
   a uniformly bounded gauge potential, nor synthetic q/K/area values
   into claims about Hatcher's actual embedding.

## Status

| Gate | Status |
| --- | --- |
| Hatcher marked commutator algebra | Established original source |
| Selected infinite-order W group representation | **Already addressed by #1247**, Gotô-based |
| Sibling-adaptive exact rational envelope | New source-written mathematical result; local Python PASS |
| Decaying siblings imply flat bounded root triviality | Mathematical conditional consequence, geometry still OPEN |
| Curvature eta <= transported Stokes integral | Standard analytic result subject to actual based homotopy; source OPEN |
| True linked geometric length+area certificate | OPEN |
| Physical SU3 selection/prediction, full topological observable | OPEN |
| Lean/Agda kernel verification | NOT RUN |


## Snowball source-discriminator (2026-10-25 literature pass)

The related **Antoine necklace** literature does provide nested *linked*
solid-torus models and some explicit iterated-function-system coordinate
data (see Rushing, *Topological Embeddings*; Daverman & Venema,
*Embeddings in Manifolds*, §2.1; and
https://ifsdb.github.io/ifs/antoines-necklace/).
These are useful candidate **geometric test controls**, not an identified
source for Hatcher's exact marked once-punctured-torus generator injections.
The Antoine-necklace meridian/winding system must NOT silently be
substituted for the Alexander-horned-sphere Hatcher Z-block group.
The new audit should apply three discriminators to every candidate:
(1) actual ambient link/isotopy class; (2) induced based parent word in
the complementary pi1; (3) arclength and clearance for the SAME
marked sibling representatives. A contracting IFS satisfies neither
(1) nor (2) merely by being contracting. This prevents a geometric
picture from being promoted into the required same-object theorem.


## 2026-10-25 FOLLOW-UP: finite sparse sibling and inverse-source budget

### Primary source visual/text recheck

We separately inspected Allen Hatcher's **original PDF** at printed pp.171–172
(PDF pages 179–180). The full embedded Z-block source states that parent
annulus boundary maps to a commutator in the free group generated by TWO
linked-handle loops and that the stage map is injective. It does NOT
supply measured Euclidean meridian arclengths, collar radii or curved
Stokes homotopy areas. This corrects an overly broad summary saying
that the geometric construction itself is absent. Existing sibling
Agda PR **#1244** now has source-backed PAPER-level three-copy gluing
(in `Docs/topology/AlexanderHornedC3SameObjectGluingTheorem20261025.md`),
an actual sphere/cap coordinate atlas, stagewise group transport and a
conditional Lean collar cover. These are IMPORTANT positive donors;
they are not a fully coded infinite Hatcher longitude/meridian metric.

### Strictly finite 3-level acceptance theorem

Let c_k=2 min(1,d(B_k)). From the prior sibling-adaptive source result
for FLAT monodromy, for any depth-three marked path

    d(root) <= c_0*c_1*c_2*d(leaf) <= 2*c_0*c_1*c_2.

If ANY TWO of B_0,B_1,B_2 satisfy d(B)<=1/4, and the other is
uncontrolled (unitary d<=2), then c_good<=1/2 and c_bad<=2.
Consequently d(root)<=2*(1/2)^2*2=1. This contradicts
the independently certified selected W, for which d(W)>1.
Three placements were checked exactly; ONE short sibling gives only
the too-weak bound 4. No selected leaf must itself be short.

At depth 3m, if >=2m sibling gaps are <=1/4 among the FIRST 3m
stages, the other m gaps may all be the unitary worst case.
The exact bound is

    d(root) <= 2*(1/2)^(2m)*2^m = 2^(1-m).

The count is over prefixes rooted at the original selected W.
Do NOT apply a single deep three-stage block in isolation: up to
2^k amplification by uncontrolled ancestors can erase its effect.
These are universal inequalities conditional on correct Hatcher group
marking, not evidence that a given physical horn has these gaps.

### New inverse gauge regularity requirement

If a source geometric hypothesis provides local sibling arclength
L(B_k)<=L0*q^k for all k<n, with 0<q<1, and a flat compatible
gauge connection coefficient bound M_n over THOSE first n loops,
then necessarily

    d(root) <= 2*(2*M_n*L0)^n*q^[n(n-1)/2].

For any realization of the selected root d(W)>1, the right side
MUST be >1, giving the exact source necessary condition

    (2*M_n*L0)^n*q^[n(n-1)/2] > 1/2.

Equivalently (without claiming a pointwise singular exponent),

    M_n > 2^(-1-1/n) * L0^(-1) * q^(-(n-1)/2).

Thus a fixed uniform M_n is IMPOSSIBLE as n grows when the geometric
siblings genuinely contract with any fixed q<1. This only certifies
unboundedness of the supremum over a growing union of sibling loops;
it does NOT show a precise blow-up rate at any particular point or
a physical curvature singularity. A nontrivial FLAT bundle still
exists on the OPEN exterior by the classical representation quotient;
a globally bounded gauge-potential presentation near the excluded
wild set is the rejected consumer.

### Exact curved-source maximum curvature budget

When an actual based source homotopy H_k gives eta_k <= K A0 r^k,
let P_j=prod_(k<j) c_k (P_0=1). At finite depth n the exact bound is

    d(root) <= 2*P_n + K*A0*sum_(j<n) P_j*r^j.

For a selected d(root)>1, a finite source contradiction is available
whenever 2P_n<1 and

    K <= (1-2P_n)/(A0*sum_(j<n) P_j*r^j).

The expression is a **source acceptance threshold**, not measured
curvature. For illustrative c_k=2*(3/4)^k, A0=1, r=1/2, n=7,
the exact threshold is

    K_crit = 6719515981 / 58747086512 ~ 0.11438.

The previously used K=1/100 is BELOW it, and the source-gated
nonflat conclusion would contradict the selected W. As always, NO
based Hatcher homotopy surfaces, physical F_A, or real Jacobian
area have been supplied. A large eta_root defeats the conclusion.

### Implemented / tested

* New Python: `scripts/check_horn_sibling_density_singularity_maxcut.py`
  (source-conditional finite bounds, sparse-density counts, inverse
  gauge budget and 4 exact critical curvature thresholds).
* Lean #84 existing `HornAdaptiveSiblingStokesCut.lean` extended with
  three source-written exact two-small positions, one-short negative
  control and rational necessary-gauge-growth lemma.
* An independent equivalent local Fraction audit completed PASS.
  No claim of byte-execution of the committed GitHub script; no
  Lean/Agda kernel run. File existence/heads will be read back.

### Updated Pareto cut, without inventing further hypotheses

P0: in **PR #1244's actual same-object satellite/C3 collars**, choose
real Hatcher parent/child/sibling meridian representatives and show
source word, exterior clearance, and length *in the same metric*.
This is the only geometry capable of turning the two-short or
density tests into an unconditional source-specific result.
P1: genuine based homotopies for parent and commutator-word loops,
curvature transport, actual area and K; feed the calculated rational
acceptance threshold. P2: physical source action/charged matter and
multi-scale discriminator; ordinary punctured-ring Wilson loops
are negative controls. Explicitly retain Gotô/Hatcher/Alexander/Lippert,
#1244 and #1247 ownership; never promote linked-picture analogy,
numerical simulation, conditional type theory or citation into
kernel/source physics.
