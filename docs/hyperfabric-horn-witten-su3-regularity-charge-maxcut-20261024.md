# Integrated 2026-10-24 horned-geometry × Witten SU(3)₁ max-cut

**Canonical existing PRs (unmerged and independently owned)**:
- [Agda horn topology PR #1244](https://github.com/chboishabba/dashi_agda/pull/1244): original geometry, algebraic Hatcher commutator group, C3 semidirect/VOA quotient and the NEW geometry/regularity probe.
- [Agda neutrino/Wilson PR #1247](https://github.com/chboishabba/dashi_agda/pull/1247): ORIGINAL selected source matrix W=T S1, exact rational cyclotomic Wilson character, interferometry, ordinary-ring spectrum and physical source/regularity roadmap.
- [Agda hyperfabric PR #1249](https://github.com/chboishabba/dashi_agda/pull/1249): Witten 1989 WZW/CS, 1989 Lacki/Zaugg SU2_4⊂SU3_1 conformal D4 extension, actual nonflat 26D WZW sigma/gerbe.
- [Lean cross-prover PR #84](https://github.com/chboishabba/dashi_lean4/pull/84): typed finite conformal embedding, WZW/gerbe and selected mathematical obstruction identities.
- [Agda KK/holonomy #1241](https://github.com/chboishabba/dashi_agda/pull/1241), [Monster/braid #1239](https://github.com/chboishabba/dashi_agda/pull/1239), [Lean Albert #52](https://github.com/chboishabba/dashi_lean4/pull/52), and [TOE #1217/#80](https://github.com/chboishabba/dashi_agda/pull/1217) are distinct physical/mathematical consumers, not silently available typed imports.

**Integrated worker attachment**: the contributed 139-line "biggest payoff geometry–regularity" report is user-provided contemporary work. Its original **50/50** test receipt is recorded on #1247 as a claim with 42 Git-blob-matched committed-source and eight exploratory local tests; the current cut independently checks the selected exact character and norm/depth table, but does NOT claim to have rerun all 50. Original worker-owned mathematical and script files remain on their branches—do not duplicate their routines, move their original authorship or alter their receipts.

## Correct source genealogy and proof authority

1. **J. W. Alexander (1924)**: original horned sphere, nontrivially embedded sphere.
2. **Allen Hatcher**, *Algebraic Topology*, Example 2B.2, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf : `π1` of classical Alexander horned ball exterior is the injective binary colimit, with meridians `m_w=[m_w0,m_w1]`. Group presentation is ORIGINAL TOPOLOGICAL PRIOR ART; it is not by itself a proof that chosen representative LOOP LENGTHS converge uniformly to zero or that the proposed three-copy model is physically realized.
3. **Ordinary group theory**: abelianization of the horned complement `G_ab=0`, as all generators are commutators at the next level; `G` is perfect. The three-copy source algebra `G^3 ⋊ C3` has `G^3` in the commutator kernel of every hom into an abelian group.
4. **Morikuni Gotô (1949)**, DOI 10.2969/jmsj/00130270: commutator surjectivity for ambient compact connected semisimple SU3(C), not the countable SU3(Q(zeta3)) subgroup, nor a selected smooth geometric gauge bundle. An abstract non-Abelian representation remains possible even if a bounded smooth gauge-connection version fails.
5. **Witten (1989)** CS–WZW, original **Lacki & Zaugg (1989)** DOI 10.1016/0370-2693(89)90662-X: genuine affine conformal inclusion `SU2_4 ⊂ SU3_1`; its `SU3_1` simple objects `1,3,3bar` form a **pointed C3 FUSION CATEGORY** after the `SU2_4` bosonic Z2 simple-current extension. This is not a horn-meridian group map, a 3×3 physical SU3 holonomy, or the external geometric C3 rotation.
6. **Hosotani (1989)** DOI 10.1016/0003-4916(89)90015-8: quantum selection of gauge Wilson phases on specified circle compactifications with particular fermions, boundary conditions and a computed renormalized effective potential; NOT an automatically transferable horned-wild-complement physical potential.
7. **Exact source audit**: the user's W in #1247 gives an *ordinary circle* counterexample to topology specificity, and the free group F2 reproduces a chosen non-Abelian one-step commutator. Neutrino and 5D KK mass/stress/likelihood claims are not licensed by this synthetic qutrit test.

## Integration 1: the serious GEOMETRY / REGULARITY condition

For unitary holonomy `U`, let `d(U)=||U-I||op`. Algebraically,
```text
[X,Y]-I = ((X-I)(Y-I)-(Y-I)(X-I)) X^-1 Y^-1
||[X,Y]-I|| <= 2 ||X-I|| ||Y-I||.
```
If `d(U_w)<=eps_n` uniformly over all 2^n depth-n meridians,
induction along the Hatcher commutator tree gives
```text
delta := d(U_root) <= 1/2 * (2eps_n)^(2^n).
If delta>0, max_leaf d(U_w) >=
  1/2 * (2delta)^(1/(2^n)) -> 1/2.
```
This proves: **a fixed nontrivial root holonomy requires non-identity
holonomy at arbitrarily deep horn levels**. The bound is a MATHEMATICAL
implication, independent of the chosen SU3 matrices. It is not
a statement that all horn embeddings have chosen short representative loops.

**Extra, UNPAID geometric and analytic hypotheses**: there must exist
physical representatives `gamma_w` for the EXACT Hatcher generators,
based/parallel-transported compatibly, with
`length(gamma_w) <= ell_n -> 0` *uniformly* at depth n; and
a uniform bound `||A||<=M` in compatible unitary frames along them.
Unitary parallel transport then gives
`||Hol(gamma_w)-I||<=M length(gamma_w)`.
Hence nontrivial delta forces
```text
M >= (2delta)^(1/(2^n)) / (2 ell_n).
```
If `ell_n=L0 q^n` this diverges at least as
`q^(-n)/(2L0)`. This is a **conditional selected
regularity no-go**, not an unconditional wild-horn or
topological flat SU3 prohibition. Gauge conjugation at
the common base point preserves `d(U)`. The original
Agda `DASHI.Geometry.FlatFormalDiskHolonomySurface`
holds explicitly uninhabited operator-norm/holonomy-to-
identity, Stokes, geometric-summability and completion
interfaces; use that canonical analytic producer.

**Source-specific selected root in neutrino #1247**:
`W=TS1`, `delta≈1.4381884752669252`. The separate
worker's original `alexander_horned_c3_su3_regularization_no_go_probe.py`
and `HornedSU3ObservableRegularityParetoMaxCut20261024.md`
already own the numerical lower-bound diagnostic; do not
vendor or falsely relabel their authorship.

**New source-bridging regression** in #1249:
`scripts/check_horn_witten_su3_holonomy_regularity_discriminator.py`
recomputes the exact selected Q(zeta3) character, unitary
root gap and finite-depth envelope, and tests an
**illustrative** loop sequence `ell_n=2^-n`; at
n=12, `max_leaf d >= 0.500128987765` and therefore
`M >= 2048.528334`. That rate applies ONLY IF that loop
length actually describes the geometry. Independent local
equivalent source run PASS. Does not rerun worker's 50 tests.

## Integration 2: NEW stronger direct **WITTEN C3 / PERFECT HORN GROUP NO-GO**

Because each `m_w` is a commutator of its children,
any group homomorphism `q:G→A` to an abelian group A
obeys `q(m_w)=1` at every depth. Since meridians
generate the horn group, **EVERY such group homomorphism
is trivial**, i.e. `G_ab=0`. In particular, *the
SU3_1 pointed fusion simple-object group* `C3` cannot
receive a NONTRIVIAL horn-meridian GROUP HOMOMORPHISM.
A map from `K=G^3 ⋊ C3` to C3 can detect the
EXTERNAL C3 rotation quotient; it kills all of G^3.
It therefore cannot turn the three rotation phases
into three distinguishable original horn meridian charges.
This is an actual algebraic proof obligation and negative
result, NOT a claim about all possible categorical actions:
nonabelian braid/defect data might be richer than an
ordinary group homomorphism and needs an explicit
constructive functor.

New Lean source theorem owner
`Integration/DASHITOE/HornWittenRegularityAndChargeCut.lean`
defines the exact `eps→2eps²` envelope,
proves its 1/2 fixed point and finite-depth
conditional selected-root contradiction, and gives
a GENERIC homomorphism-to-abelian commutator theorem
and its application to each recursive meridian.
`ZMod3` charge commutator zero is a direct consumer.
These are **source written; Lean/Lake kernel NOT RUN**.
Neither the metric loop hypotheses nor the entire
Hatcher direct-limit group is constructed by this file.

## Integration 3: SU3 *gauge holonomy* ≠ SU3₁ chiral pointed C3

Original sibling #1247 has exactly
```text
Tr(W) = (176093404722400 - 19836986431118 zeta3)
        / 181846007130841.
```
An honest SU3 **central** holonomy is `zeta3^j I_3`,
with traces `3,3zeta3,3zeta3²`. Since
`zeta3²=-1-zeta3`, their independent
`(1,zeta3)` coefficients are
`(3,0), (0,3), (-3,-3)`, none matching
the selected W's exact coefficients.
So **W is NONCENTRAL** and cannot be
made a central matrix by gauge conjugation.

An unpolarized vectorlike 3-path comparison at zero
relative phase has `P+(0,W)=0.67048481558`,
visibility `|TrW|/3=0.3424207192`,
while the hypothetical central `zeta3 I_3` has
`P+(0)=1/4`, visibility1. These are honest
**gauge-invariant, ordinary-circle reproducible**
model discriminators, not horn-specific measurements.
Moreover, even identifying SU3₁ 3 simple-object labels
with centre holonomies is a NEW physical/categorical
assumption, not something implied by conformal embedding.
The centre counterfactual is deliberately just a
control for that invalid shortcut.

New source script uses 9 abelian commutator cases
and all 81 two-stage Z3 assignments to confirm the
trivial charge; and recomputes the numerical selected
root from the ORIGINAL #1247 six rational trigonometric
inputs and zeta3. Source-owner citation attached;
no nonexisting sibling Agda module is imported.

## Integrated roadmap: Pareto geometry gate before new representations

- **H0 DONE audit** — different root authors, exact GitHub PRs,
  mathematical/analytic/physical/measurement authority.
- **H1 DONE abstract finite math** — source actual horn infinite
  commutator group; SU3 Wilson representation possible
  abstractly by Gotô; all-depth norm obstruction as conditional
  general analytic theorem; selected exact Wilson character;
  SU3₁ conformal D4 C3 and existing Monster/Albert remain
  distinct; `Hom(G,C3)=0` as group theoretic consequence.
- **H2 HIGHEST-ROI OPEN** — show or refute
  `sup_{|w|=n} length(gamma_w)→0`
  for the *literal intended three-copy wild exterior*
  with generators matched to Hatcher words, compatible
  stems/trivializations and physical spatial metric.
  This cannot be paid by group presentation or 27-site
  hypervoxel cardinality.
- **H3 OPEN selected regularity** — build a bona-fide
  smooth/unitary SU3 bundle with connection whose
  holonomy is the chosen W; either identify a
  nonshrinking geometric escape, or prove the
  necessary nonuniform gauge/defect boundary
  data without inventing finite action/stress.
- **H4 OPEN dynamical selection** — Hosotani's
  actual source field content/compactification/
  boundary and one-loop spectrum on a verified
  geometry; no arbitrary hand-picked W or
  ordinary-circle toy promoted to horn physics.
- **H5 OPEN empirics** — measured distinct
  gauge-invariant Wilson observables that
  separate horn tower from ordinary circle/F2;
  anomalies, coherent charged probe, source
  stress, KK/EMD coupling and held-out likelihood.
- **H6 optional Witten/TOE** — integrate only an
  actual operator/state preserving functor
  between group representation, source
  physical SU3 bundle, `SU2_4⊂SU3_1`
  affine chiral algebra, 26D WZW sigma
  target and optional Monster. Direct C3
  horn-character path fails algebraically.
  Does not pay any YM/NS/RH/other Clay estimate.

**Proof status:** externally established Hatcher/Gotô/Witten
and elementary unitary/group facts ≠ kernel checked DASHI
proofs. Current selected exact-rational finite script
PASSED on locally equivalent source; Lean theorem source
UNVERIFIED; geometry, quantum effective potential and
physical experiment OPEN. No CI used. Keep draft PRs.


## 2026-10-25 stronger NEW geometric max-cut: exact source Wilson norm and diameter countercontrol

Canonically grounded continuation:
`docs/hyperfabric-horn-finite-length-trace-regularity-maxcut-20261025.md`.
**Exact no-eigensolver selected SU3 certificate** from the original
sibling #1247 Q(zeta3) trace:
`ReTr(W)=221179426799/216225930001`;
`||W-I||_op²>= (6-2ReTrW)/3
=854996726408/648677790003 >1`.
This is source arithmetic plus the standard
unitary Frobenius/operator inequality. Thus the
fixed physical representative W would have
delta_op>1 without numerical eigenvalue software.

**Finite-depth no-go rather than only asymptotic**:
the universal commutator envelope
`E_(n+1)(eps)=2(E_n(eps))²` has
`E_n(1/2)=1/2` exactly for EVERY finite n.
If at any complete Hatcher depth all true
holonomy leaves have norm-gap <=1/2,
the selected root delta>1 is impossible.
A concrete analytic source-geometric witness
would be `sup_len_depth(n)=ell_n`,
`sup_compatible_connection_norm=M`,
and `M ell_n<=1/2` with genuinely
matched, whisker-conjugated source generators.
Neither `ell_n` nor M is already certified
for the 3-copy wild exterior; Euclidean
handle *diameters* alone do not supply
path-length bounds.

**Strong new counterexample proving need for LENGTH**:
on smooth Euclidean R², take SU3 gauge
`A=(i diag(1,-1,0)/2)(-y dx + x dy)`
with nonzero bounded constant curvature
and the radius 1/n circle traversed n² times.
Image diameter 2/n->0, pointwise norm
||A|| <=1/(2n)->0, but length=2pi*n,
and holonomy diag(-1,-1,1) at every n.
The original ordinary smooth SU3 gauge
theory is prior art; our concrete exact
high-winding negative control is the new
selected regression. It is NONFLAT
and HIGHLY REPEATED, NOT an actual simple
Hatcher meridian nor a flat-horn countermodel.
Do not infer physical singularity from it.

**New source discrepancy explicitly quarantined:**
Hatcher, *Algebraic Topology* Example 2B.2,
p.172 explicitly states the direct-limit
horn complement is nontrivial with TRIVIAL
abelianization and “highly nonfree”.
The 1968 N. W. Riebe institutional
abstract describes its `G^k` groups as
free countably infinite rank. They cannot
refer to one isomorphic nontrivial marked
group because a free group has nonzero
abelianization; Riebe's full thesis PDF is
access-restricted, so differing spaces/
constructions/abstract wording remain
UNRESOLVED, not an error proved.

**Executed receipt**: new
`scripts/check_horn_geometry_length_trace_maxcut.py`
local source PASS: exact rational trace and
operator-gap bound, 33 exact fixed-depth
envelope checks, numeric consistency for
seven selected depths, seven exact high-winding
negative controls. GitHub committed file exists
and math source is locally reproduced;
**byte-exact Git blob execution is not claimed**.
Lean #84 `HornWittenRegularityAndChargeCut.lean`
appends source-written rational selected
gap/cutoff and radius/winding source lemmas.
Lean/Lake KERNEL UNVERIFIED.

**True Pareto** is to construct/verify an
actual source MARKED meridian loop family
with unitary whisker/basepoint compatibility,
controlled tube clearance and rigorous
metric *length* bounds (or exhibit a
nonshrinking escape), before promoting
any horn-specific Witten/Neutrino/KK
physical claims. D4 SU2_4⊂SU3_1 and
Hatcher's perfect group no-abelian
charge map remain independent mathematical
constraints; no new CS, Monster, Clay or
experiment theorem is paid by this regression.


## 2026-10-25 final horn/Witten source correction and highest-alpha frontier

Canonical focused owner: https://github.com/chboishabba/dashi_agda/blob/chatgpt/hyperfabric-wave-spacetime-cut-20261024/docs/hyperfabric-horn-a5-flat-bundle-onebranch-maxcut-20261025.md

Historical owners: Hatcher's Alexander horn fundamental group; independent Agda horn #1244 owns the nontrivial A5 quotient and finite c=0 VOA; independent Agda neutrino/Wilson #1247 owns the selected noncentral W. Standard icosahedral A5 and flat-principal-bundle monodromy reconstruction are published prior mathematics.

A new finite-image theorem gives a strictly stronger geometric filter for the A5 quotient: every nonidentity element of the standard faithful icosahedral A5 < SO3 < SU3 has operator-gap at least sqrt((5-sqrt5)/2)>1. A nontrivial root commutator forces both children nontrivial recursively, hence ONE sequence of genuinely marked descendant meridians with lengths tending to zero contradicts a compatible uniformly bounded FLAT connection realizing that finite-image representation. This is NOT the unrestricted SU3 result, which required a stronger full-depth small-leaf condition.

A positive independent result is also necessary: the nontrivial representation of the classical Hatcher exterior's pi1 into SU3 automatically yields a smooth FLAT SU3 principal bundle with that holonomy on the OPEN exterior via the standard universal-cover construction. It need not have connection coefficients uniformly bounded near the excluded wild boundary. Thus abstract smooth-flat existence is positive, and the physical regularity requirement is the live issue. The SU3 principal bundle over this 3-manifold is topologically trivial by standard low-dimensional obstruction theory.

Three genuine exact source regressions have passed locally with byte-for-byte Git blob hash verification:
(A) A5 60 elements / 3600 commutator pairs / 8 synthetic collar stages / 127 topological parent-child WINDING mismatch controls; Git blob bce4f345d18912687bcf2d4a99d469376db39754.
(B) smooth FLAT punctured-plane order-five single winding loops, shrinking length and connection coefficient norm growing as 1/r; Git blob b15a80bc228f213f3918c2fd3509499034620f34.
(C) smooth bounded NONFLAT SU3 on simply connected R2 with different Wilson holonomies on homotopic contractible loops; Git blob 4876fffbcc823aebf929c6b0bd6ef29b42591ece.

The synthetic geometric collar is explicitly NOT Hatcher marked: each of 127 parent circles has child-core winding (1,0) versus (0,0) for the required commutator, proving a literal topological rejection instead of a decorative failure flag.

The selected separate #1247 W has nonzero imaginary trace because its exact zeta3 coefficient is nonzero. Every element, and every SU3 conjugate, of the chosen REAL icosahedral A5 < SO3 subgroup has real trace. Thus W cannot be identified with the A5-root holonomy in that representation. The original two selected math programmes must remain separately typed.

MOST IMPORTANT PHYSICAL PRECONDITION: Hatcher's pi1 relation between meridians implies a relation between holonomies automatically ONLY for FLAT monodromy representations. With nonflat connection, Wilson holonomy depends on the geometric representative; a controlled non-Abelian Stokes/homotopy/curvature-defect estimate is essential. Earlier loose wording about arbitrary bounded nonflat connections is superseded. The original FlatFormalDiskHolonomySurface mathematical interface owns the unresolved Stokes/analytic terms.

Lean #84 adds SOURCE-WRITTEN generic all-descendant-nontrivial, one-short-marked-descendant/finite-gap contradiction and selected Wilson nonreal trace certificate. Lean/Lake and Agda kernels not run; no actual source-coordinate three-copy Hatcher collars or uniform physical connection, no Witten/Monster/TOE identification and no Clay theorem.

Current Pareto: construct genuinely linked Hatcher Z-block collars with van Kampen parent-as-commutator marking, collar clearance, arclength and compatible whisker/gauge data for ONE descending branch; if that exists, the finite A5 uniformly bounded flat realization fails. For general curved gauge fields, separately quantify homotopy-surface curvature defects.

## 2026-10-25 worker attribution correction: W infinite order ALREADY belongs to #1247

The strongest finite-image exclusion is NOT a new original #1249 discovery. Agda sibling #1247 already owns `NeutrinoExistingCPFiniteResidualNoGoExact.agda` and its exact Galois-trace certificate `442358853598/216225930001` in (2,3), with the standard algebraic-integer theorem stated as an external prerequisite. Original `NeutrinoHornedExteriorFifthPowerNoGoExact.agda` additionally owns the specific A5 fifth-power transfer. Our #1249 reproduces the exact rational certificate and adds the *independent* Q(zeta3) field norm `34895555697482945411132133124/33067970309429875820893367281` in (1,2). This second noninteger norm corroborates the original mathematical W-INFINITE-ORDER conclusion, ruling out ALL finite-image group representations of the selected W; it does not pretend to be first to that theorem.

The original Agda horn #1244 A5 quotient/c0 VOA remains a separate positive finite-image construction. A new complete 60/60 A5 inverse-conjugacy witness proves all unitary A5 characters real and also rejects the nonreal-trace W; this narrower result is strictly SUBSUMED by the original infinite-order no-go. Exact Agda #1249 scripts source-written and byte-for-byte locally executed, source hashes `b4a23effa02df27fe66c5e001f88f057cec3c8ea` and `4cb2aaf316ed28207d66a5f516c9d8bbbddeb30d`.

The correct positive compact-SU3 distinction: infinite order does NOT give a positive identity gap for all nontrivial powers. Standard two-eigenphase Dirichlet recurrence proves for all Q≥2 some m≤Q² with `||W^m-I||op≤4π/Q`; selected source W shows `||W^458-I||op≈0.04449169165` in a NUMERICAL regression (six Q values). Committed/equal blob `5de01046b58a8bd73fb9ac0681e9576b0a930619`. The finite A5 one-short-branch obstruction does NOT transfer to this W; the general full-depth commutator envelope remains conditional on FLAT source holonomy and true marked geometric lengths.

The Hatcher p171 source `Z` marking is once-punctured-torus boundary word `[a,b]`; the new exact finite free-group word test checks eight substitutions (2^n generators, 4^n nontrivial reduced word, zero abelianization), and rejects the original synthetic unlinked tube mark by its nonzero winding. Source executable blob `7a73fc6d68f55105de93ee416798f59127c03391` locally byte-tested. This is topological COMBINATORIAL marking, not a linked 3D Z-block coordinate/metric proof. Next actual producer remains a geometric marked meridian/collar with all-stage complement clearance, lengths and whisker compatibility, or a rigorous counterexample.

Canonical new source and stage roadmap:
`docs/hyperfabric-wilson-infinite-order-eisenstein-source-maxcut-20261025.md`.
Lean #84 `Integration/DASHITOE/HornWilsonInfiniteOrderEisensteinNormCut.lean` source-writes the distinct field-norm certificate, exact trace ranges and generic ambivalent-character lemma, with number-theory integrality as an explicitly identified standard external premise. **Lean/Lake kernel UNVERIFIED**. No observed lepton/TOE/Monster/Clay result.


## 2026-10-25 sharper Hatcher one-branch SU3 theorem: 2^n rather than 4^n

**New canonical source/implementation:** docs/hyperfabric-horn-onefastbranch-sharp-unitary-maxcut-20261025.md and scripts/check_horn_single_fast_branch_unitary_cut.py in Agda #1249; Integration/DASHITOE/HornSingleFastBranchUnitaryCut.lean in Lean #84. Original Hatcher Example 2B.2 (printed pp.171–172), original horn A5/VOA #1244, original selected W/noninteger trace #1247 and existing FlatFormalDiskHolonomySurface retain authorship/ownership.

For any UNITARY A,B, the elementary exact identity ||[A,B]-I||op=||AB-BA||op gives the stronger d([A,B])<=2 min(d(A),d(B)); previous valid bound 2 d(A)d(B) <=4d(A) is nonoptimal for a chosen child. Thus for ANY selected TRUE FLAT Hatcher horn group representation G→SU3, and ANY one depth-n descendant w, d(Uroot)<=2^n d(Uw). Given a genuinely source-marked local meridian length L_w and compatible uniform connection bound M, d(Uroot)<=2^n M L_w. Exact previously checked selected W source character certifies d(W)>1. Therefore ANY chosen depth with 2^n M L_w<=1 contradicts W, without finite-image or full-depth-smallness assumptions. A geometrically marked path shrinking as L0*q^n with q<1/2 and M bounded would settle the bounded-FLAT-selected-W case conditionally. **Source-true linked marked geometry and loop LENGTH are STILL UNPROVED**; do not promote Hatcher's topological picture into metric q<1/2.

Exact local rational rates for hypothetical M=100,L0=1: q=1/8 depth4, q=1/5 depth6, q=1/4 depth7, q=1/3 depth12; q>=1/2 gives no crossing. Additional heterogenous *complete* binary tree certificate 2 d(root)<=∏(2 epsilon_leaf), checked across nine exact test trees, complements one-branch criterion. Agda Python reference PASS; current remote Git script exists. Lean new native theorem source conditional on explicit normed-commutator/flatness premises, **Lean/Lake kernel UNVERIFIED**.

For CURVED connections, π1 group relations do not imply equality of Wilson matrices on homotopic loops unless a curvature/homotopy (non-Abelian Stokes) error is controlled; a genuine literal loop concatenation is another possible source but must match the independently selected root loop. No claim of actual linked three-dimensional Z-block, Witten/Monster/TOE source action or Clay estimate.


## New nonflat physical-interface cut: exact curvature/homotopy defect propagation

For a CURVED unitary gauge connection, the fundamental-group equality m_w=[m_w0,m_w1] does NOT establish equal holonomy matrices for independently selected geometric representatives. On an actual linked, based Hatcher Z-block let

    eta_w = ||Hol(gamma_w) - [Hol(gamma_w0),Hol(gamma_w1)]||op.

The eta_w must be independently produced from a genuine geometric homotopy plus transported curvature/non-Abelian-Stokes estimate, not set to zero because of the group relation. The optimal unitary commutator bound then implies for ANY chosen descendant branch of depth n

    d(Uroot) <= 2^n d(Uleaf) + sum_{k=0}^{n-1} 2^k eta_(ancestor at depth k).

If d(Uleaf)<=M Lleaf, the exact rejection condition for the previously certified selected d(W)>1 is

    2^n M Lleaf + sum_{k=0}^{n-1} 2^k eta_k <= 1.

This is a concrete acceptance test for either (i) a FLAT connection with eta=0, or (ii) a curved connection with REAL source-controlled homotopy defects. It prevents the prior physically invalid promotion of pi1 identities into arbitrary Wilson-loop equalities.

New committed exact Fraction script: scripts/check_horn_curved_branch_stokes_defect_cut.py checks the recurrence equals the explicitly weighted sum for 21 arbitrary heterogeneous depth fixtures; rejects a HYPOTHETICAL n=12 source with q=1/3, M=100, L0=1, eta_k=(1/100)(1/3)^k, whose exact bound is 8508407/10628820 ≈0.80050 <1. It also deliberately FAILS CLOSED for eta_root=2 and for the critical q=1/2. No selected geometric homotopy area, curvature, flatness, connection stress or physical source bound was constructed.

Lean #84 new Integration/DASHITOE/HornCurvedBranchDefectCut.lean source-writes an arbitrary branch error-envelope induction, proves monotonicity, and derives the finite source conditional curved-rejection theorem. The matrix norm/Stokes-to-eta analytical bridge is EXTERNAL/UNPAID and Lean/Lake kernel/typecheck NOT RUN.

The logical next producer is now a geometry+connection DOUBLE certificate: genuinely linked/marked Hatcher loops of quantitative length together with explicit based homotopy surfaces and their area/transported-curvature error, or a genuine failure of these in the selected three-copy embedding. Simply matching lengths or a symbolic commutator is not enough for nonflat physics.
