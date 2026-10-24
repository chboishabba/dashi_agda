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
