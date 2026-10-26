# Selected horn Wilson max-cut: infinite-order provenance, Eisenstein-norm audit, and SU(3) recurrence

**Date**: 2026-10-25 (Brisbane). **PRs**: [Agda hyperfabric #1249](https://github.com/chboishabba/dashi_agda/pull/1249) and [Lean cross-prover #84](https://github.com/chboishabba/dashi_lean4/pull/84). These are CROSS-PR consumers, not new original PMNS/neutrino results.

## Attribution and original mathematical authority

- **Original selected source object**: sibling [Agda neutrino #1247](https://github.com/chboishabba/dashi_agda/pull/1247), `DASHI/Physics/QFT/NeutrinoHornedSU3RootExact.agda`, defines the matrix `W=T S1`, `T=diag(1,ζ,ζ²)`, `S1=2|u1><u1|−I`. Its `NeutrinoExistingCPFiniteResidualNoGoExact.agda` ALREADY records the same exact noninteger Galois field trace and its **infinite-order consequence** from standard algebraic-integer theory. The accompanying `NeutrinoHornedExteriorFifthPowerNoGoExact.agda` ALREADY states the weaker fifth-power no-go for the source A5 quotient. **Do not relabel those original results as discoveries of #1249.**
- **Other original owner**: [Agda horn topology #1244](https://github.com/chboishabba/dashi_agda/pull/1244) constructs a source-specific nontrivial `G→A5`, all 60 commutator antecedents, three-copy `A5³⋊C3` and a 180-dimensional c0 finite commutative VOA. A separate mathematical option, NOT a realization of the original selected W.
- **Algebraic-number prior art**: finite-order matrix eigenvalues are roots of unity, whose sums are algebraic integers; field trace/norm of algebraic integers in `K=Q(ζ3)` lie in `Z`; `O_K=Z[ζ3]` with `N(a+bζ)=a²−ab+b²`. Sources: Stanford number field trace/norm notes https://crypto.stanford.edu/pbc/notes/numberfield/tracenorm.html ; Trifković, *Algebraic Theory of Quadratic Numbers*, §1.4, https://pi.math.cornell.edu/~hatcher/TN/Algebraic%20Theory%20of%20Quadratic%20Numbers%2C%20Trifkovic%2C%202013.pdf . This is external established mathematics.
- **A5 prior art**: every element of the alternating group A5 is conjugate to its inverse. For a finite-dimensional unitary representation the trace is constant on conjugacy classes and `tr(g^-1)=conj(tr(g))`, hence EVERY unitary A5 character is real-valued. Previous #1249 only excluded the chosen REAL icosahedral A5 embedding. This check generalises the character-based exclusion to arbitrary unitary A5 representations but is strictly SUBSUMED by the already original #1247 infinite-order result.
- **Compact group recurrence prior math**: Dirichlet's simultaneous Diophantine approximation on two independent eigenphases of a determinant-one SU3 matrix gives `∀Q≥2 ∃1≤m≤Q², ||W^m−I||op≤4π/Q`. This is prior harmonic/Diophantine theory, not a discovered finite cyclic period or horn representation.

## New independent arithmetic check: the selected source norm is also NONINTEGER

From the exact ORIGINAL #1247 character `t=tr_3(W)=(A+Bζ)/D`, where
```text
A = 176093404722400
B = -19836986431118
D = 181846007130841
ζ²+ζ+1=0.
```
Set `a=A/D, b=B/D`. Source field trace is
```text
Tr_(K/Q)(t) = 2a−b
  = 442358853598 / 216225930001
  = 372023795875918 / 181846007130841
  in (2,3).
```
Both last presentations agree EXACTLY; the second is the original owner's quoted rational. This was already the original #1247 mathematical no-go.

**Independent second certificate NEW to this integration**:
```text
N_(K/Q)(t) = a²−ab+b²
  = 34895555697482945411132133124
    /33067970309429875820893367281
  in (1,2), NONINTEGER.
```
If `W^n=I` for any positive integer `n`, then `t` is algebraic integer and both its field trace AND field norm are ordinary integers. Both exact certificates contradict that assumption. Consequently `W` has INFINITE ORDER and no finite-image representation can contain it. **The infinite-order conclusion is original #1247; the norm corroboration is the added independent calculation.**

**Executable**: new `scripts/check_wilson_infinite_order_eisenstein_norm.py` runs only exact Python Fraction arithmetic, independently recomputes both rational traces/norms and their nonintegral intervals; executed locally PASS and remote Git blob `4cb2aaf316ed28207d66a5f516c9d8bbbddeb30d` is byte-identical. New `scripts/check_horn_a5_all_real_characters_vs_selected_w.py` enumerates EXACT 60 even permutations and explicit inverse conjugators, checks nonzero original `Im(t)²`; executed and byte-identical remote Git blob `b4a23effa02df27fe66c5e001f88f057cec3c8ea`.

**Native Lean #84**: `Integration/DASHITOE/HornWilsonInfiniteOrderEisensteinNormCut.lean` source-writes exact field norm and trace arithmetic, noninteger intervals, generic inverse-conjugate unitary-character lemma, and explicit conditional integration of the source classical algebraic integrality theorem. Lean/Lake kernel **NOT RUN**; sibling Agda #1247 number-theory authority is NOT misrepresented as a locally kernel-certified proof.

## Consequence important to physical/geometric interpretation: NO finite image, yet near-identity POWERS

The original selected W cannot be carried by ANY finite group quotient, including A5, but it belongs to compact SU3. For any SU3 eigenphases `θ1, θ2, θ3=−θ1−θ2 (mod 2π)`, pigeonhole Dirichlet on the 2-torus gives
```text
for Q>=2: some 1<=m<=Q² satisfies
  |m θ1|mod2π <=2π/Q,  |m θ2|mod2π<=2π/Q,
  |m θ3|mod2π <=4π/Q,
hence ||W^m-I||op <=4π/Q.
```
This is an ESTABLISHED general compact-Lie fact; it says the infinite cyclic image has elements arbitrarily close to identity, unlike the finite A5 image with positive nonidentity gap `κ≈1.17557`.

The source-selected numerical regression `scripts/check_wilson_su3_infinite_cyclic_recurrence.py` recomputes the SAME rational-trigonometric W, tests its unitary/determinant constraints and the Dirichlet bound at `Q=4,8,16,32,64,128`, and finds
```text
||W^458−I||op ≈ 0.04449169165
```
in floating-point. This is a NUMBERIC REGRESSION with the original source, not an exact algebraic proof of the numerical norm. Locally executed; remote Git blob must be verified against source hash `5de01046b58a8bd73fb9ac0681e9576b0a930619`.

## Physical/analytic consequences and stop conditions

1. **NO finite quotient can reproduce original #1247 W.** The original #1244 A5 finite-image horn/VOA model and original #1247 SU3 selected W model are distinct, and source-positive in their own mathematical domains. Do not attempt to glue them into the same physical group action.
2. **A5 one-short-branch regularity criterion cannot be used on this W**: the finite A5 image has a positive gap for all nonidentity elements; an infinite cyclic subgroup generated by W has nonidentity elements arbitrarily close to I. The general unitary Hatcher *FULL-DEPTH* commutator-envelope criterion remains a correct conditional statement for a genuinely flat source representation with a root gap `>1`.
3. **Existence of an abstract compatible horn representation** from Gotô compact SU3 commutator surjectivity is independent of a source-selected finite quotient and does not require a finite image. The infinite-order test does not defeat such an abstract SU3 assignment, provided each infinite commutator stage and any required C3-equivariance are actually constructed and compatible.
4. **Geometry remains the true unfinished producer**: the actual source *marked* Hatcher meridian loop geometry, quantitative lengths, compatible physical connection and gauge trivializations. Flatness or quantified non-Abelian Stokes curvature correction is indispensable before promoting π1 commutator relations to holonomy identities.
5. **No new physical measurement or TOE**: the original SU2_4⊂SU3_1 Witten D4 conformal extension, Monster C27, signed-zero, 27-site hypervoxel, and actual 4D/5D lepton/gravity claims remain separately typed. Neither the norm certificate nor Dirichlet recurrence identifies their Hilbert/operator carriers, predicts neutrino masses or solves Clay problems.

## Pareto gates

| Phase | Status |
|---|---|
| Original CP/noninteger field trace ⇒ W infinite order | **ALREADY in Agda #1247** (original external theorem conditional, kernel unverified) |
| Independent noninteger Eisenstein field norm | **New exact rational pass** |
| All 60 A5 ambivalence witnesses / generic real unitary character | **New exact finite pass; subsumed by infinite order** |
| SU3 recurrence `m≤Q²`, norm `≤4π/Q` | **Existing mathematical theorem; new selected numeric pass** |
| Complete source marked wild geometry, lengths and trivializations | **OPEN** |
| Uniform bounded *flat* connection for selected W vs geometry | **OPEN, with conditional full-depth obstruction** |
| Curved physical gauge with Stokes error bounds | **OPEN** |
| Source-selected physical lepton/TOE/Monster and observational discriminator | **OPEN** |

**Highest alpha next**: in horn #1244 geometry source, prove a genuine marked nested Hatcher-tube meridian family, respecting the van Kampen parent-to-child commutator relation, with quantitative arclength in the chosen ambient metric; then apply the correct FULL-DEPTH norm criterion for infinite-image W, not the A5 single-branch finite-image shortcut. Original source papers and module attribution remain attached to all claims.


## Hatcher source Z-block: actual marking algebra certified, metric still open

Original source Hatcher *Algebraic Topology* Example 2B.2 pp.171–172, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, specifies a region `Z` with `π1(Z)=F(a,b)`, obtained topologically from an open ball with two tubes deleted, where the incoming annulus's core curve maps to the **boundary of a once-punctured torus**, namely the nontrivial free word `[a,b]=aba^-1b^-1`. This is not the original synthetic *unlinked* parent meridian with winding (1,0), which failed against the required commutator's (0,0).

New verified executable `scripts/check_hatcher_punctured_torus_marking_word.py`:
- checks that the punctured-torus boundary has REDUCED nontrivial word `aba^-1b^-1` but trivial abelianization; contrasts the unlinked generator's nonzero abelianization;
- checks **8 levels** of Hatcher's original binary free-group substitution: `2^n` distinct leaf generators, a nontrivial freely reduced root word of length `4^n`, zero abelianization;
- derives the purely CONDITIONAL arclength budget: if a length `L0*q^n` (for q=1/5 as an illustrative input) were obtained for each properly based leaf path with ZERO extra stems, then concatenating the `4^n` letters would give root representative length at most `L0*(4q)^n`. Such a length bound is NOT established for the physical horn, as whiskers, linkages and all future-stage avoidance must be accounted for.

Local exact test PASS and byte-equal Git blob `7a73fc6d68f55105de93ee416798f59127c03391`.
The output is a sourced **2D punctured-torus marking witness**, NOT the ambient Hatcher linked three-dimensional Z-block, and neither proves the full free-group injection nor supplies a wild-sphere metric. The earlier synthetic-cylinder winding mismatch remains a valid negative control. The next acceptance object is a TRUE linked source-coordinate Z-block chart with explicit complement clearance and an all-level embedding.

This is the same metric/homotopy gap whether the target is the worker's INFINITE-order W or the separate A5 finite-image representation; their geometric regularity criteria differ as the previous phase gates state.


## 2026-10-25 sharper Hatcher one-branch SU3 theorem: 2^n rather than 4^n

**New canonical source/implementation:** docs/hyperfabric-horn-onefastbranch-sharp-unitary-maxcut-20261025.md and scripts/check_horn_single_fast_branch_unitary_cut.py in Agda #1249; Integration/DASHITOE/HornSingleFastBranchUnitaryCut.lean in Lean #84. Original Hatcher Example 2B.2 (printed pp.171–172), original horn A5/VOA #1244, original selected W/noninteger trace #1247 and existing FlatFormalDiskHolonomySurface retain authorship/ownership.

For any UNITARY A,B, the elementary exact identity ||[A,B]-I||op=||AB-BA||op gives the stronger d([A,B])<=2 min(d(A),d(B)); previous valid bound 2 d(A)d(B) <=4d(A) is nonoptimal for a chosen child. Thus for ANY selected TRUE FLAT Hatcher horn group representation G→SU3, and ANY one depth-n descendant w, d(Uroot)<=2^n d(Uw). Given a genuinely source-marked local meridian length L_w and compatible uniform connection bound M, d(Uroot)<=2^n M L_w. Exact previously checked selected W source character certifies d(W)>1. Therefore ANY chosen depth with 2^n M L_w<=1 contradicts W, without finite-image or full-depth-smallness assumptions. A geometrically marked path shrinking as L0*q^n with q<1/2 and M bounded would settle the bounded-FLAT-selected-W case conditionally. **Source-true linked marked geometry and loop LENGTH are STILL UNPROVED**; do not promote Hatcher's topological picture into metric q<1/2.

Exact local rational rates for hypothetical M=100,L0=1: q=1/8 depth4, q=1/5 depth6, q=1/4 depth7, q=1/3 depth12; q>=1/2 gives no crossing. Additional heterogenous *complete* binary tree certificate 2 d(root)<=∏(2 epsilon_leaf), checked across nine exact test trees, complements one-branch criterion. Agda Python reference PASS; current remote Git script exists. Lean new native theorem source conditional on explicit normed-commutator/flatness premises, **Lean/Lake kernel UNVERIFIED**.

For CURVED connections, π1 group relations do not imply equality of Wilson matrices on homotopic loops unless a curvature/homotopy (non-Abelian Stokes) error is controlled; a genuine literal loop concatenation is another possible source but must match the independently selected root loop. No claim of actual linked three-dimensional Z-block, Witten/Monster/TOE source action or Clay estimate.
