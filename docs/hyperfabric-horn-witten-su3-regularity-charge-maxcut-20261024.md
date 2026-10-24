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
