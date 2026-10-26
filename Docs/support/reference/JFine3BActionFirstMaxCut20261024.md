> **25 OCTOBER 2026 — PRIMARY-SOURCE MAX-CUT CORRECTION (latest):** Barraclough–Wilson §5.1 permits *any* irreducible \(6.\mathrm{Suz}\) character as the inflated 729 tensor factor. Earlier faithful-78 **preselection** in the repository main-quotient GAP script was a local filter, NOT the Monster's proven selection. PR #1250 now scans **all** degree-78 outer families and requires the original full main-table split, exact MN3B descent, and positive occurrence in the restricted Monster character to select exactly one. The source-selected family's faithfulness and central C2 trace (either -90 or +66 for the 90-sector) are **OUTPUTS**, not preconditions. Nebe's Sym²78 and faithful78 remain different 6.Suz representations when their central C2 actions differ. Any earlier claim that the Monster *already selects* faithful78 is superseded. See [actual 6.Suz source-family ledger](./Monster3B6SuzExistingSourceFamilyMaxCut20261025.md). The matcher and its revised validator are source-written; no GAP/Agda execution receipt is available in this turn.\n\n> **25 October 2026 — source-family correction:** the existing full Monster-to-6.Suz quotient matcher selects *faithful* degree-78 characters, while Nebe's Sym²(faithful12)=78 descends to 3.Suz and is nonfaithful to 6.Suz. Matching C3 phases or norm8100 cannot identify these two families: their degree90 central C2 traces are -90 and +66, respectively. See [the source-family max-cut audit](./Monster3B6SuzExistingSourceFamilyMaxCut20261025.md). The actual selected Monster pair requires the unexecuted GAP quotient receipt; earlier geometric/Sym² predictions are separate conditional constructions.

# 24 OCTOBER 2026: D4 PRIOR-ART + 6.SUZ SYMMETRIC-SQUARE RESOLUTION (LATEST)

The current most productive result is the **D4-only** exact nine-cell (9+3→12→\mathrm{Sym}^2(12)=78→90) bridge, not the older geometric 90-point permutation or numerical 90=12+78. Of three exact 12-dimensional D4 symmetric-square candidates, exactly one contains the original raw nine-cell D4 module. An explicit rational intertwiner connects the (U_{12}\oplus\mathrm{Sym}^2(U_{12})) D4 representation to the prior signed 90-dimensional repair. See [JFine3BD4NineCellSuzukiSym2GF20261024.md](./JFine3BD4NineCellSuzukiSym2GF20261024.md).

**Scope firewall:** Faithful complex degree12 of 6.Suz has central involution -I; its symmetric square has central involution +I. Thus a faithful degree78 of full 6.Suz cannot be this Sym²; nonfaithful degree78 candidates must be included in the source character search. Corrected CTblLib producer/renderer/checker and a full Sym²/dual Sym² source-character screen are source-written but not GAP-executed. Historical Barraclough GF31/GF103/GF223 finite-field constructions are original work distinct from our local modular-rank tests. Monster 12G is an ATLAS conjugacy class, not a finite field.

---

# CURRENT DECISION — 24 OCTOBER 2026 (supersedes the exploratory cuts below)

**The originally proposed geometric D4 extension is mathematically ruled out** on the selected Monster 3B phase sector using the ordinary Monster character values on involutions and order-six elements. ATLAS power maps restrict every 3B-commuting involution's zeta trace to `{66,90,1458}`, whereas the original geometry demands half-turn `810` and reflections `2430`. There is no need for mmgroup, GAP, class-algebra fusion or actual Monster matrices to close this no-go.

**A conditional repaired signed-monomial 90-space D4 representation exists** with `23A1+5A2+13B1+13B2+18E`, keeping the same Heisenberg fibre and producing phase-sector character `[65610,1458,18,1458,1458]`. The order-four value 18 is forced by the ATLAS 4B/12G power pairing and q-series values 51/-3, under the fixed six-coordinate fibre lift. This does NOT prove an actual Monster D4 embedding or the full Suzuki normalizer 12+78 linear action.

**Authoritative current theorem/proof boundary:** [JFine3BInvolutionNoGoAndLinearRepair20261024.md](./JFine3BInvolutionNoGoAndLinearRepair20261024.md). New Python: `scripts/monster_3b_jfine_involution_character_nogo.py`, `scripts/jfine_3b_linear_multiplicity_d4_repair.py`; source-typed Agda owners: `Monster3BJFineGeometricD4InvolutionNoGoExact.agda` and `Monster3BJFineD4CandidateMultiplicityExact.agda` wired through `Monster3BActualKernelCharacterRound4Validation.agda`.

The following document remains as historical work/proof-ownership context. Its earlier proposal to seek a character match for the **old** geometric D4 via class-algebra screening is **superseded** by the direct no-go. The previous GAP and mmgroup scripts are optional source corroboration, not the active mathematical critical path.

---

# JFine / Monster 3B: action-first max-cut (24 October 2026)

## Source attribution and owner audit

- **Wilson 1988**, *The odd-local subgroups of the Monster*, DOI 10.1017/S1446788700031323: published N(3B) representation-theoretic restriction. Original authorship is Wilson's.
- **Barraclough and Wilson 2007**, *The Character Table of a Maximal Subgroup of the Monster*, DOI 10.1112/S1461157000001352: primary normalizer character table, extraspecial inertia/character construction and fusion.
- **Breuer CTblLib**, existing `scripts/monster_3b_normalizer_restriction.g`: class fusion, classwise 196883 restriction, extraspecial normal class carrier, phase split and 12+78 irreducible degree calculation. Code is not evidence a particular GAP run succeeded.
- **DASHI / merged PR #700**: `Monster3BWilsonPublishedRestrictionReconciliationExact.agda` already records the *published* `143+65520+(729+729')(12+78)` restriction. It prohibits a false Suz-stable `143=90+53` interpretation.
- **DASHI / merged PRs #464, #666, #974, #995**: normalizer character and Heisenberg generators/commutant, group laws, selected orbit-screen actions and specific no-promotion gates.
- **DASHI / prior actual-kernel owners**: `Monster3BActualKernelCharacterPromotionExact.agda`, `Monster3BFiniteHeisenbergCommutantExact.agda`, `Monster3BFiniteStoneVonNeumannMultiplicityExact.agda`, `Monster3BNormalizerCocycleCancellationExact.agda`, `Monster3BActualZetaPromotionPipelineExact.agda`. Reuse; do not define duplicate projectors or cocycles.
- **DASHI / open PR #1098**: `Monster3BActualLinearIsotypicTerminalCompilerExact.agda` already packages the generic FDRep/Schur/Maschke/Hom-normalizer interface, while explicitly leaving the SAME-object actual representation and lifted inertia action as obligations. Companion Lean theorem source status is not a verified Agda theorem.
- **DASHI / open PR #1148**: original source-typed `IITJFineFourOneFourS3ZetaGaugeExact.agda`, `IITJFineS3RegularMonsterCharacterExact.agda`, `IITJFineS3Heisenberg90x729CodecExact.agda` establish the JFine 90×729×3 chart and C3 character; they expressly do not assert a Weyl group action or Monster intertwiner.

## New: a genuine pointwise Heisenberg action on the pointed JFine carrier

The nine fine-site coordinates are recentered at the distinguished centre `c`. Split the eight relative positions into two label values `r=(N-c,E-c)` and six fibre values `u=(S-c,W-c,NW-c,NE-c,SW-c,SE-c)`; keep original coarse label `k ∈ {0,…,9}`. Then the original pointed source has an existing two-sided chart

  `P = {0,…,9} × F3^9 ≅ M × X × F3`, with `M={0,…,9}×F3²` (90 labels), `X=F3^6` (729 values).

Define on **basis points** (not on functions) the action

  `U(a,b,t)|(m,u,c)> = |(m,u+a,c+t+b·u)>`

for `a,b∈F3^6`, `t∈F3`. Composition is exactly

  `(a,b,t)*(a',b',t') = (a+a',b+b',t+t'+b·a')`.

It is the standard extraspecial Heisenberg `3^(1+12)` action, transported to the ORIGINAL pointed carrier by the previous chart. `B_b A_a = Z_(b·a) A_a B_b`, and `(a,b,t)^(-1)=(-a,-b,-t+b·a)`. The central generator shifts `c` and agrees with the original global value-C3 translation on all nine sites. Modulation is an actual state permutation on the pre-Fourier carrier rather than a symbolic dimensional label.

Fourier linearization along `c` gives for either nontrivial complex C3-character `λ`:

  `P_λ ≅ (C[X])^⊕90`, and `χ_(P_λ)|E = 90 χ_(H_λ)`.

The selected original value-reflection `R(m,u,c)=((-r),-u,-c)` (coarse `k` unchanged) implements

  `R U(a,b,t) R^(-1)= U(-a,b,-t)`.

This defines a concrete compatible `H ⋊ C2` action on the pointed JFine permutation carrier and exchanges the two nontrivial centre eigenspaces. It is NOT identified with the particular Monster N(3B) involution.

Executable and exhaustive:
- `scripts/jfine_3b_permutation_heisenberg_action.py`: 196830 JFine round trips; 2,361,960 generator inverse + reflection conjugation checks; 1,180,980 Weyl checks; nonzero modulation phase orthogonality; reflection fixed-point trace 10.
- The induced involution on the 90 multiplicity labels fixes 10 labels, giving `(+,-)=(50,40)` for this chosen C2 action. These numbers DO NOT supersede Wilson's irreducible dimensions 12 and 78.

## Actual Monster E restriction: strongest mathematical theorem and its prerequisite

Let `W` be the genuine degree-196883 complex Monster representation; assume the sourced subgroup `E=3_+^(1+12)` and `z∈Z(E)` are identified with the chosen Monster 3B centre. On the *actual* eigenspace `W_ζ = {v : ρ_W(z)v=ζv}`, degree 65610 follows from the published 3B character 53.

The extraspecial group has the nondegenerate commutator pairing `E/Z(E) × E/Z(E) → Z(E)`. For any `g∉Z(E)`, choose `h` with `hgh^-1=zg`. Hence on `W_ζ`,

  `χ_W(g)=χ_W(zg)=ζ χ_W(g)`, whence `χ_W(g)=0`.

On `z^t`, `χ_W(z^t)=65610 ζ^t`. The Schrödinger character has `χ_H(g)=0` off the centre and `χ_H(z^t)=729 ζ^t`. Thus

  `χ_(W_ζ|E) = 90 χ_H`.

By characteristic-zero representation character determination,

  `W_ζ|E ≅ H_ζ^⊕90 ≅ P_ζ`

as **abstract E modules**, after choosing an isomorphism from the model E to the actual E. This proof uses the actual W representation and the real extraspecial 3B inclusion from the cited sources, rather than assuming an arbitrary same-object numerical field. It does **not** select a basis or produce literal Monster generators and therefore does **not** construct a canonical or source-coordinate matrix `T`. It is mathematical deduction conditional on accurate subgroup/source identification, not a newly kernel-verified Agda result.

This short central-commutator route should be fed into the **existing** Agda/Lean action and character-transport owners, not rebuilt as a competing theorem family. This immediately discharges the ordinary mathematical character equality; it does not discharge its proof-assistant same-object certificate.

## Explicit intertwiner recovery algorithm and obstruction

If actual matrices for six Weyl translations `A_i`, modulations `B_i`, and the central generator are supplied in `W_ζ`, compute

  `P_0 = ∏_(i=1)^6 (I+B_i+B_i²)/3`

over the exact coefficient field containing ζ (where the B_i have eigenvalues 1,ζ,ζ²). `P_0` projects onto the zero-weight subspace, of dimension 90 when the source agrees. Pick an actual basis `s_1,...,s_90` for `im P_0`. Then define columns

  `T_(u,j) = A_1^(u_1) ... A_6^(u_6) s_j`.

This constructs the candidate actual `90×729 → W_ζ` intertwiner in `O(90×729)` *vectors*, without solving a dense `65610²` unknown system. Check `rank(T)=65610`, `A_iT=TA_i^model`, `B_iT=TB_i^model` and the central phase. A failed identity/rank becomes a negative certificate.

`scripts/jfine_3b_sparse_intertwiner_example.py` implements an independent exact toy instance on `F7` with primitive cube root `2`, `n=2`, multiplicity 2. It scrambles the target by an invertible shear, recovers an 18×18 intertwiner with rank 18 from the projector, and rejects a corrupted generator. This tests the algorithm; it does not supply actual Monster matrices.

## Normalizer multiplicity and cocycle

The **12+78 character-level split is already source-backed** by Wilson 1988 / merged PR #700 and the existing CTblLib normalizer restriction. Do not reopen it as mere arithmetic. The real remaining work is to transport the *same normalizer action* onto `S_ζ = Hom_E(H_ζ,W_ζ)`, which depends on source-derived lifts of the action on `H_ζ` and `W_ζ`. The canonical induced action is `n·f = ρ_W(n) f ρ_H(n)^(-1)`, with projective multiplier compensation as already proved in `Monster3BNormalizerCocycleCancellationExact.agda`. A source-attached cocycle and complete actual character on the induced Hom remain pending.

The 53-dimensional C3-trivial residual is **not an N(3B)-stable 53-dimensional summand** of W: Wilson's 143 constituent is irreducible at the indicated normalizer level. Likewise, the full pointed `P ⊕ 53·1` C3 match does not prove full E/N representation equivalence.

## Roadmap/phase and acceptance tests (max-cut)

1. **Closed at exact finite model level:** pointed Heisenberg group action, Weyl relations, value-reflection automorphism, `P_ζ` Schrödinger decomposition and finite explicit trace.
2. **Closed mathematically modulo primary-source subgroup identification:** character-theoretic existence of an abstract actual-`E` isomorphism `P_ζ ≅ W_ζ`. Not a concrete source-coordinate isomorphism or Agda kernel proof.
3. **Already known via sourced N-character work:** `12+78` paired-phase multiplicity pattern; central `53` trace residual; distinction from normalizer constituent `143`.
4. **Actual highest-value missing data:** source-defined *linear matrices* for generators on the 65610-dimensional W_ζ (or a compact equivalent action), with central ζ selection and class-fusion provenance. Feed those matrices to the projector/intertwiner compiler; verify rank and generator equality.
5. **Second missing data:** actual normalizer inertia lifts and projective cocycle for the 90-dimensional Hom; verify the SOURCE 12+78 character **on this same action**.
6. **Formalisation:** transport this new POINTED action through PR #1148's source types and integrate with PR #1098's existing linear FDRep/character/Hom code. The current PR uses standalone scripts to avoid a divergent second Heisenberg or Stone–von Neumann owner.
7. **Evidence discipline:** no Agda/Lean CI or GAP/AtlasRep success is claimed here. Do not promote an Agda source-written theorem to kernel proof without an exact-head receipt. Do not promote the group's mathematical identification into a physics/quantum/consciousness result without independent same-object physical data.


## Representation transport closes the *existence* question, not the explicit-data question

Given the abstract `E`-isomorphism `T:P_ζ→W_ζ` established by complete character equality above, let `I=C_{N(3B)}(z)` be the actual phase-preserving inertia group. Define

  `ρ_pointed^I(n) := T^(-1) ρ_W(n)|_(W_ζ) T`  for `n∈I`.

This is automatically an honest `I`-representation with all relations, and `T` is an exact `I` intertwiner *by construction*. This proves abstract existence of an inertia action on the JFine ζ-sector, not that the simple site-reflection/coordinate permutations previously constructed happen to realize it. Source-coordinate operators on `W_ζ` and `T` are still required to compute that transported action or compare it to a predefined geometric action. Full N(3B) inversion must act on the **paired** ζ/ζ² sectors, not separately on either.

The associated multiplicity space is canonically the **abstract** `Hom_E(H_ζ,W_ζ)` (dim 90). Choosing a projective lift of `I` to `H_ζ` induces the compensated projective action on the Hom space. Wilson's published `12+78` determines its relevant source character after the specific lift and central phase convention are fixed; it does not determine a preferred `Fin90` basis. This is the exact distinction between an existence theorem and a computationally explicit representation.

## Reusable theorem owners (do not duplicate)

| Mathematical primitive | Existing owner | New consumer |
|---|---|---|
| Heisenberg multiplication and nondegenerate commutator | `Monster3BFiniteHeisenbergCentralExtensionExact` and group-law/nondegeneracy siblings | Pointed chart action; character proof |
| Generator-level Weyl identities | `Monster3BFiniteHeisenbergGeneratorsExact` | Exhaustive pointed action and sparse projectors |
| Scalar commutant / Stone–von Neumann | `Monster3BFiniteHeisenbergCommutantExact`, `Monster3BFiniteStoneVonNeumannUniquenessBidiExact` | Abstract E-isomorphism |
| Point projectors, tensor coordinate recovery | `Monster3BFiniteProjectorModelExact`, `Monster3BMultiplicityEvaluationExact` | Sparse generator-intertwiner compiler |
| Projective inverse-cocycle tensor cancellation | `Monster3BNormalizerCocycleCancellationExact` | Source-derived inertia/Hom action |
| (S_3,D_4), nine-site orbit and Burnside counts | IIT PR #1148 `IITJFineFourOneFourS3ZetaGaugeExact`; earlier repository orbit techniques | Fixed-point and character discriminator |
| Finite linear FDRep, isotypic/Hom action | Open PR #1098 actual linear compiler and companion Lean #47 receipts | Source-coordinate proof boundary |

This ownership table **is the reusable interface extraction plan**: implement adapters only where an action is proven on the same source object. No duplicate general Burnside, Schur, Stone–von Neumann, or cocycle axioms are introduced into the Agda tree by this PR.


## Max-cut correction: existing owners, finite D4 no-go and equivariant repair

**Prior art:** Merged PRs #464, #666, #700, #974, #995 already own the Heisenberg group, Schrödinger action, 3B normalizer character restriction, 12+78 character data and original D4 subgroup screen. Existing actual-kernel structure, scalar commutant, Stone–von Neumann uniqueness/multiplicity, actual-sector recognition/evaluation, cocycle-cancellation and source linear-Hom owners remain the owners of these results. Open PR #1098 and companion Lean #47 source-write generic FDRep, Schur, Maschke, isotypic, tensor, character and induced normalizer-Hom theorems. Generic Heisenberg was not a missing theorem.

**Actual data boundary:** The AtlasRep producer constructs/tests the extraspecial group, not the 196883-dimensional Monster action. The type `ActualZetaSectorRecognition` and the `ActualLinearMultiplicityAcquisition` / `Selected3BNormalizerMonsterActionWeld` records are conditional proof contracts; none by themselves supplies selected Monster linear matrices, a concrete source-coordinate 65610-dimensional T, an actual inertia lift or its projective cocycle. The sourced 12+78 character split is owned, but its specific same-object Hom action/Fin90 transport remains unobserved. Do not promote a source-written interface to a kernel-verified inhabitant.

**Old-chart negative result:** The original chart `(N-C,E-C;S-C,W-C,NW-C,NE-C,SW-C,SE-C)` picks two adjacent edge coordinates as multiplicity labels. Six of eight spatial D4 elements mix label and fibre coordinates. Their conjugates of an E fibre translation move a multiplicity label, whereas every element of the selected E fixes that label. Therefore full positional D4 does **not** normalize the old selected E action. Its geometric D4 normalizer has order two. This does not refute abstract Monster E-isotypy.

**New D4-stable chart:** On centre-relative edge values N,E,S,W over F3 define
```
label a=(N-S)/2, b=(E-W)/2
fibre x=(N+S)/2, y=(E+W)/2, NW,NE,SW,SE
N=x+a, S=x-a, E=y+b, W=y-b.
```
Since 1/2=2 in F3, this is a concrete two-sided 2+6 split. The full square group D4 preserves the summands. On labels and fibre:
```
Q: (a,b;x,y,NW,NE,SW,SE) -> (-b,a;y,x,SW,NW,SE,NE)
M: (a,b;x,y,NW,NE,SW,SE) -> (a,-b;x,y,NE,NW,SE,SW)
```
The fibre transforms by six-coordinate permutations P, so the previously established Heisenberg action normalizes under `(a_H,b_H,t) -> (P a_H,P b_H,t)` and preserves its dot/cocycle. Global value-S3 also normalizes this E; C3 is the E centre and value inversion swaps nontrivial phases.

Source-typed Agda owner: `DASHI/Biology/IITJFineD4EquivariantHeisenbergGaugeExact.agda` on *existing* IIT PR #1148; imported by `IITPhiIntegrationEverything`. The module contains exhaustive base-F3 pair identities, two-sided chart, and Q/M equivariance proofs. No Agda kernel receipt claimed.

Exact finite Python owner: `scripts/jfine_3b_d4_equivariant_chart.py` on this PR. An independent local run enumerated all 196830 original states and 1574640 D4 conjugation equations, passed. The D4 character of its 90 label permutation module is (identity 90, quarter 10, half 10, reflection 30), with decomposition `30 A1 + 10 B1 + 10 B2 + 20 E2`. This is **not** Wilson's 12+78, and no actual Monster D4 subgroup is identified.

**Revised critical path:** obtain literal same-object Monster W_zeta / E / phase-preserving inertia action or source-coordinate generators; use existing recognition/projector/Hom/character compilers and test ranks, class characters, and projective cocycle. The existing `monster_3b_five_orbit_d4_n3b_screen.g` covers subgroup/fusion experiments but not this 90-dimensional same-object Hom action. Do not generate parallel Stone-von Neumann/Schur/Burnside or cocycle owners.


## Public source-operator acquisition: the next material cut has now narrowed

A targeted external primary-code check found:
- Martin Seysen, **mmgroup** (https://github.com/Martin-Seysen/mmgroup), provides vector-action operators for the original Conway Monster 196884-dimensional representation over GF(7), not dense matrices. Source and user documentation: https://mmgroup.readthedocs.io/en/latest/api.html . For the centre of order 3, GF(7) contains a primitive cube root `zeta=2`, so the phase projector works without characteristic-3 collapse.
- The published `applications/Hurwitz/hurwitz_monster_samples.py` at blob `f618df5f903b08d212e4d03b95617159f7fd5842` supplies an explicit **Monster 3B** word `M0<y_0dah*x_0c8bh*d_468h*p_45301176*l_2*p_79432320>`. The source's validation route searches in the 2B centralizer using the ordinary Monster 3B character value 53. The new `scripts/monster_3b_mmgroup_selected_phase_probe.py` imports this word with attribution; requires real mmgroup, checks order 3 and trace 53, and tests the exact modular projector `Pi_zeta(v)=5*(v+4*v*z+2*v*z^2)` using `v*z=right action`.
- ATLAS publishes an absolutely irreducible 12-dimensional representation of 6.Suz over GF(7) (https://brauer.maths.qmul.ac.uk/Atlas/v3/matrep/6SuzG1-f7r12aB0). This offers a possible standard-generator reference but still needs **source-word alignment**. An ATLAS 78-dimensional GF(3) representation of 3^(1+12).2Suz.2 is **indecomposable but reducible** and is explicitly `1.(64+12).1`; it is not Wilson's complex 78-dimensional multiplicity constituent (https://brauer.maths.qmul.ac.uk/Atlas/v3/matrep/Mmax7G0-f3r78B0).
- DASHI prior art explicitly identifies Barraclough's 2005 PhD section 5.3 `F31/F103/F223` finite-field 729/1458 construction and the `V6s2/`, `38/`, `factor.c` routes. These are source-acquisition leads already owned by `IbrahimMonster3B729ExtensionFiniteFieldProducerSnowballExact` and `IbrahimMonster3BT1WordT2ScalarRoutingSnowballExact`; no original historical matrix bytes are claimed.

**New stronger acquisition boundary:** A literal 3B **element word** and a computational 196884-dimensional *vector-action engine* are now located in public source. A real `zeta` eigenvector can be constructed by this interface when the package is present. This alone does not supply the 12 remaining Weyl generators of the SAME E subgroup, the 6.Suz inertia lifts or an explicit conjugation from the AtlasRep/Barraclough standard generators to Seysen's mmgroup generators. Therefore it is not a source-coordinate 90×729 Monster intertwiner.

The probe is FAIL CLOSED and has **not** been executed in this environment (mmgroup absent). GAP and Agda are also absent. The source-written module must not be promoted to a measured local runtime success. A future successful run should record mmgroup version, exact selected word hash, source blob SHA, eigenrelation samples and (only after computing E-generator words) the actual Weyl/intertwiner/cocycle checks. Any cross-characteristic inference must be checked: GF(7) is semisimple for E since 7 does not divide 3^13, but not for all of Monster.

 
## New decisive 2026 source: actual 3B normalizer and E words FOUND

- Dietrich, Lee, Pisani and Popiel, *Explicit construction of the maximal subgroups of the Monster*, Journal of Algebra 689 (2026), 862–895; DOI 10.1016/j.jalgebra.2025.10.016.
- The original computational authority is `https://github.com/melissa-maths/MonsterSubgroups/blob/main/subgroups.py`, original blob `c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2`, section `3^(1+12) · 2 · Suz:2` / Theorem 2.6.
- Literal `g3b,h3b` generate the ACTUAL Monster 3B normalizer. `x3b` is a verified central 3B element (order3, 196883 trace53). Literal `y3b`, `l=(r**(g3b**2)).reduce()` with `r=(g3b**28)*(g3b**28)**h3b`, and five each of `gs,hs` together with `x3b` generate ACTUAL extraspecial `E=3_+^(1+12)`. The original authors provide executable verification. This supersedes prior claims that actual 3B group words must still be discovered. It does NOT mean they have been executed in our runtime.

`scripts/monster_3b_mmgroup_source_symplectic_basis.py` now vendors only the literal source-defined group words, retaining DOI, original author attribution and source blob SHA. Its mmgroup runtime procedure calculates the 12×12 alternating commutator Gram matrix, fails unless nondegenerate, performs symplectic Gram-Schmidt to construct six exact translation and six exact modulation words, verifies all 36 Weyl pair relations, and reconstructs the action of the TWO source-defined normalizer generators on these new coordinates—including their 12×12 GSp action and central correction. It checks the resulting manifest again with `monster_3b_mmgroup_weyl_word_alignment.py` rather than creating a second independent group theory owner.

Pure F3 symplectic Gram-Schmidt self-test passed in local Python. Actual mmgroup runtime not observed (package not installed and package index DNS inaccessible); GAP/Agda unchecked. No source-coordinate Monster phase-eigenspace basis, literal Monster-to-JFine intertwiner T or `Hom_E` 90-dimensional character/cocycle has yet been constructed or certified. The concrete group-word inputs ARE available now. The next producer should use `MMV(7)` actual vector actions and the source-derived normalizer/E words on one selected 3B element; not the earlier unrelated Hurwitz g3 word unless a conjugator is supplied.

Current proof owner routing: generic Heisenberg/Stone–von Neumann/projectors/cocycle remain in pre-existing Monster owners; D4-symmetric JFine chart is on PR #1148; generic FDRep/Hom/Weil transport is on open PR #1098 and companion Lean #47; source-specific executable group-to-module seam belongs to this PR #1250. Preserve Wilson 1988 and Barraclough–Wilson 2007 character attribution independently from the new 2026 same-group construction.


## Matrix-free W_zeta↔JFine intertwiner producer (source-written, not executed)

`scripts/monster_3b_mmgroup_matrix_free_intertwiner.py` consumes the actual source-aligned E/N word manifest emitted by the new symplectic adapter. Over `GF(7)`, where `ζ=2`, it computes the joint idempotent
```
P = (1 + 4z + 2z²)/3 · product_{i=1}^6 (1+B_i+B_i²)/3
```
(the characteristic-7 inverse of 3 is 5). A deterministic scan of original mmgroup basis vectors builds exactly 90 linearly independent projections by vectorised **exact GF7 Gaussian elimination**; its stopping rule FAILS if rank90 is not reached. The source generator words act on those literal selected vectors. The implicit map `T(u,j) = s_j A_1^{-u_1}...A_6^{-u_6}` then supplies 65610 exact, constructible vectors. Because MMV uses right actions, the source module convention is `T(u,j)·A_i=T(u-e_i,j)`, `T(u,j)·B_i=ζ^{u_i}T(u,j)`; this reversal must not be silently confused with the left-set JFine action. A mathematically complete rank argument requires the verified 90 joint-weight multiplicity, Weyl isotypy and the source 65610-dimensional zeta sector, not just checking a handful of columns. The producer records that it has not formed a giant dense matrix nor tested all 65610 columns by brute force.

This new script is a real **algorithm for constructing** a same-source actual Monster E intertwiner with the JFine Heisenberg fibre, but without mmgroup execution it is NOT a completed numerical output and not an Agda/Lean kernel theorem.

**Important characteristic separation:** `GF7` contains primitive third roots and characteristic 7 is coprime to `|E|=3^13`, so E's representation is semisimple. However 7 divides `|Suz|`, so `GF7` reduction cannot on its own certify Wilson's characteristic-zero irreducible `12+78` normalizer factorisation or full normalizer semisimplicity. The `Hom_E` action and projective cocycle must be computed on the actual same-source lifts, then compared to published characteristic-zero character information with a valid lifting/independence argument.

**Final Pareto update:** Actual group word acquisition is CLOSED by the 2026 original source; a full symplectic E/N generator compiler and matrix-free 90×729 intertwiner **producers are implemented**; successful execution and characteristic-zero normalizer multiplicity/cocycle certification remain open. Do not label source-writing as having run those computations.


## 24 Oct backend-free max-cut: mmgroup optional, not a theorem prerequisite

The abstract/character-theoretic selected Monster 3B result needs **NO mmgroup, GAP matrices, or dense 65610-dimensional generator matrices**. For sourced actual extraspecial (E=3_+^{1+12}) and selected central class 3B (z), the full characteristic-zero Monster character has `chi_W(z)=chi_W(z²)=53` and `dim(W)=196883`, giving `dim(W_zeta)=65610=90×729`. Nondegenerate extraspecial commutator pairing implies each noncentral (g∈E) is conjugate inside E to (zg), so on the ζ-sector `chi(g)=ζ chi(g)`, i.e. zero. Central values are `65610 ζ^t`. Thus the **complete** E-character is `90 χ_H`. Character determination for finite complex representations yields an abstract E-equivariant isomorphism `W_zeta|E ≅ H_zeta⊗C^90`; this is a mathematical theorem under the actual subgroup/source restriction, not a concrete basis map of an independent Monster presentation. A basis-independent existence theorem is the correct product at this level.

The existing `Monster3BActualKernelCharacterPromotionExact`, `Monster3BFiniteStoneVonNeumann*`, `Monster3BFiniteProjectorModelExact`, `Monster3BMultiplicityEvaluationExact`, `Monster3BActualMultiplicityEvaluationFromRecognitionExact`, `Monster3BNormalizerCocycleCancellationExact`, open Agda #1098 and Lean #47 already own the corresponding **generic** construction. The new script `scripts/jfine_3b_backend_free_discriminator.py` is an exact finite *consumer*, not a new Stone–von Neumann or normalizer theorem owner.

### Stronger full-sector D4 character fingerprint, computed without mmgroup

Using the D4-stable JFine source chart on original pointed nine-site values, the geometric D4 representations on multiplicity S (dim 90), Heisenberg fibre H (dim 729), and their selected ζ-sector product P (dim 65610) have conjugacy-character rows (classes `[1,r²,r±,s,rs]`):

```
chi_S = [ 90, 10, 10,  30,  30 ]
       = 30 A1 + 0 A2 + 10 B1 + 10 B2 + 20 E2

chi_H = [729, 81,  9,  81,  81 ]
       = 144 A1 + 63 A2 + 99 B1 + 99 B2 + 162 E2

chi_P = [65610,810,90,2430,2430]
       = 9540 A1 + 7110 A2 + 8280 B1 + 8280 B2 + 16200 E2.
```

This is now an **independent exact obstruction/screen** for identifying a proposed Monster D4 subgroup and ζ-sector action: unless its classwise phase-restricted character matches the last five values under a proved class map, no D4-equivariant isomorphism from this specified JFine geometric model can exist. But because Wilson's 12+78 refers to a *different full 6.Suz/inertia representation*, the D4 fingerprint is NOT evidence that the 12/78 constituents individually split into these D4 irreps. A match of all five D4 character values is necessary and sufficient for isomorphism **as complex D4 modules only**, still not a full N(3B)-equivariant Monster action identification.

The new executable performs exact integer fixed-point counts for all eight D4 elements, complete D4 irreducible character inner products, and mixed Weyl+D4 traces in the ring `Z[ζ]` represented by integer pairs `(a,b)` for `a+bζ`, with `ζ²=-1-ζ`. It checks pure noncentral Heisenberg traces zero, central traces `65610 ζ, 65610 ζ²`, and the exact representation degrees. Locally tested successfully with Python standard library only, without GAP/mmgroup/CI. Historical sources for the *Monster* character remain Wilson and Barraclough--Wilson; geometric fingerprints are the repo's new computation.

### Exact revised roadmap / stop rule

1. **Already theorem/character scope:** extraspecial 3B inclusion from published Monster work, 729 irreducible Schrödinger type, 90-copy abstract E-sector isomorphism, Wilson's 12+78 N-character, projective Weil/Hom abstract compilers and correction that 53 is not N-stable.
2. **New fully finite/model scope:** pointed E action, D4-stable 2+6 coordinate chart, full 90/729/65610 geometric D4 character and mixed-character fingerprints. No mmgroup dependency.
3. **Only conditional/concrete same-object residual:** identify a PARTICULAR actual Monster D4 subgroup with geometric D4 generators and prove its ζ-phase-restricted character, or exhibit an explicit source-coordinate E/N intertwiner T and 90 multiplicity action. Existing class-fusion or generator-word engines are optional means of doing this, **not** necessary for the abstract representation-theory proof. A normalizer-compatible T cannot be inferred from the E-isomorphism alone; transporting an action through an arbitrary E-isomorphism defines a new action, not an identification with the pre-existing geometric D4 action.
4. **No false completion:** no successful actual Monster linear normalizer matrices, full classwise same-action Hom character, explicit N-intertwiner or formal typecheck receipt is claimed. Old mmgroup producers remain optional computational programs; their absence does not block mathematical E/isotypic or finite D4 outcomes.


### Crucial existing structural no-go: 90 labels cannot carry the full pure permutation action

This is **already owned**, not new: `DASHI/Wikimedia/IbrahimMonster3BSuzukiNinetyPermutationCharacterNoGoExact.agda`, plus `IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact.agda` and `DASHI/Reasoning/Trialectic369MonomialMultiplicityBasisSpecialisationExact.agda`.

Using the sourced nontrivial central order-three scalar in the degree-12 representation of (6.Suz), the `12+78` multiplicity character at that element is NOT rational/integer, for any permitted eigenphase of the 78 block. An honest 90-point permutation character would instead be a nonnegative integer counting fixed points. Therefore a full source-normalizer `Fin 90 -> Fin 90` permutation-basis identification is **mathematically impossible**, even though the restricted *geometric D4 subgroup* acts by permutations on our chosen coordinates. This is a decisive negative result. A genuine non-permutation linear (90)-dimensional action is required; a suitable monomial action carrying phases may still exist but is not established. This rules out a major false-positive route regardless of whether mmgroup can be run.

The strongest steelman consequently is: existing `E`-module equivalence with a 90-dimensional multiplicity **vector space**; geometric D4 action gives an exact separately testable character fingerprint; an actual normalizer extension must mix/phase the multiplicity coordinates consistently with the published nonintegral central character. A `D4` trace match would show D4 equivalence only. The abstract `12+78` isotypic type is source-backed, but its *same chosen geometric coordinate action* is not established. Stop demanding an mmgroup matrix for the former, and stop asserting the latter from a `Fin90` permutation chart.


### Cheapest remaining actual-D4 test: eight class triples, no Monster matrices

For any source-certified embedding `j:D4→C_N(3B)(z)`, the projector of the actual Monster degree-196883 character onto the selected ζ phase is

  `chi_zeta(j(g)) = (chi(j(g)) + zeta² chi(zj(g)) + zeta chi(z²j(g)))/3`.

If ordinary input trace values `A=chi(j(g))`, `B=chi(zj(g))`, `C=chi(z²j(g))` are integers, write `chi_zeta(j(g))` exactly in `Z[zeta]` as

  `((A-B)/3) + ((C-B)/3) zeta`.

Thus our geometric JFine D4 model passes the full classwise **D4-character test** iff, on each of the five class types with a realized eight-element mapping, `A-B=3·(65610,810,90,2430,2430)` respectively and `C=B`, with all three source-aligned group elements identified. Ordinary identity triple `(196883,53,53)` recovers `65610` exactly.

`scripts/monster_3b_d4_phase_character_certificate.py` is a BACKEND-INDEPENDENT arithmetic checker accepting eight actual group-element/class-position/trace triples with independent source and embedding witness references. It rejects missing class rows, malformed positions, nonintegral projected ζ values, wrong identity dimension and unequal D4 class inventories. It **cannot certify authenticity** of a claimed embedding or class position merely from a URL in JSON. The local `--selftest` passes identity arithmetic plus malformed-input negative controls; the source's actual other seven triple inputs are NOT currently provided or verified. Existing GAP/CTblLib `scripts/monster_3b_five_orbit_d4_n3b_screen.g` is the correct related subgroup discovery owner, but its old five-orbit signature is a DIFFERENT test.

### Explicit obstruction: E-character equality does not determine a normalizer lift

In the exact constructed `H6⋊D4` model, multiply D4's **multiplicity-space** representation by its orientation/sign character, leaving every E element's operator unchanged. Both group representations therefore have the literally SAME E action and complete E character. However their full phase-sector D4 characters are respectively
```
     geometric: [65610,810,90, 2430, 2430]
  sign-twisted: [65610,810,90,-2430,-2430].
```
A D4-equivariant intertwiner between them is impossible because character values differ. The sign-twisted irreducible multiplicities are `7110 A1+9540 A2+8280 B1+8280 B2+16200 E2`. The exact finite Python producer checks this negative control. The geometric D4 action on the Schrödinger fibre is implemented by honest six-coordinate permutations preserving the F3 bilinear pairing, so this CONSTRUCTED D4 Weil multiplier/cocycle is trivial. No conclusion about the actual Monster inertia Weil cocycle is inferred.

This sharply proves WHY the remaining source-selected normalizer action is genuine additional data rather than redundant. It is not a reason to demand mmgroup: a verified source character restriction on the chosen subgroup suffices for abstract D4 module equivalence, and a concrete source-coordinate map can be computed by any appropriate algebra backend if required.


## 24 Oct max-cut further closure: actual-table *class algebra* before a group model

The previous selected-C3-only screen for actual D4 actions remains a valid conditional route but over-asked for an AtlasRep group and class identification. We have now source-written a strictly stronger CHEAP first pass in `scripts/monster_3b_jfine_d4_class_algebra_screen.g` that needs only `CTblLib CharacterTable("MN3B")`, `CharacterTable("M")`, the stored fusion, and `MatClassMultCoeffsCharTable`. It does **not** require `mmgroup`, an AtlasRep group or a 196883-dimensional matrix. References: GAP Reference Manual §§71.12-7,71.12-9 (class structure coefficients); Thomas Breuer, CTblLib; Wilson 1988 and Barraclough–Wilson 2007 for original Monster normalizer work.

### Mathematical justification of the exact table-only test

In the full 3B normalizer, the two nonidentity elements `z,z²` of the actual E centre form one conjugacy class of size two `C_z`. For ANY conjugacy class `C_i` of N, the UNORDERED PAIR of ambient class indices of `z*g,z²*g` is invariant as `g` varies inside `C_i`: conjugation by N may swap z and z² but preserves their set. If the class algebra has
```
K_(C_z) K_(C_i) = Σ_k c_(z,i,k) K_(C_k),
```
then for a fixed `g in C_i` the exact multiplicity among the two products in class k is
```
    n_k = c_(z,i,k) * |C_k| / |C_i|  (integer 0,1,2; Σ_k n_k=2).
```
Hence the literal source character values at both products are reconstructible as an unordered pair using character-table entries alone.

For `g` of order 1, 2, or 4, *g centralizes z* iff both products `zg,z²g` have order `3*order(g)`. If g instead inverts z, the two product orders equal `order(g)`. This strictly separates a phase-preserving D4 from a phase-swapping D4 using ONLY class orders.

For a phase-preserving candidate class, let `A=χ_W(g)`, and `{B,C}={χ_W(zg),χ_W(z²g)}` from the class algebra. The required **integer-real** JFine D4 character forces `B=C`, in which case the ζ-phase projection reduces to the exact integer `(A-B)/3`. It must equal `[65610,810,90,2430,2430]` on the five canonical D4 classes. This is a strictly stronger screen than ordinary degree-196883 D4 character containment and does not require selecting absolute ζ versus ζ².

`PossibleClassFusions(CharacterTable(D4),MN3B)` enumerates candidate class maps. The screen returns all surviving literal maps; if the output is exhaustive, no unresolved source values remain, and none survive, there is a **table-level obstruction** to any D4 in `C_N(z)` carrying *this exact geometric JFine ζ-sector character*. Surviving fusions are only candidates: they are NOT actual subgroup constructions or normalizer-equivariant intertwiners. The producer FAILS on unknown character tables/fusion, missing central 3B class or nonintegral class-product multiplicities. It is not claimed to have run with GAP here.

### Independent exact local test of the class-algebra method

`scripts/check_monster_3b_jfine_class_algebra_principle.py` was executed locally against the concrete finite group `S3×C4` (order24) with normal size-two 3-cycle class. It directly built all 12 conjugacy classes, multiplied all class sums, checked `n_k=c_k|C_k|/|C_i|` against actual element products, and correctly separated 4 phase-preserving coprime-order classes from 4 phase-swapping ones. It also checked the projected degree-one ζ-sector character of the standard S3 two-dimensional representation. **This validates the algorithm on a real small group, not any Monster class triple.** Its local receipt is `monster_3b_jfine_class_algebra_principle_receipt.json`.

### Second, stronger route if table-only screening retains candidates

`scripts/monster_3b_jfine_phase_preserving_d4_screen.g` reuses the actual-3B/E GAP construction owner via a newly guarded exit; the original `monster_3b_actual_kernel_structure.g` behaves identically when run standalone. The downstream script searches **inside `Centralizer(G,z)` only** and checks all eight projected D4 characters against the geometric model using unambiguous ambient class values. On a search cap or ambiguous class data it reports INCONCLUSIVE, not a false no-go. This group route is optional *after* the table-only elimination.

### Material status and follow-up priority

1. Reused, not reconstructed: finite H, scalar commutant, Stone–von Neumann, source phase-resolved 8748 and 56862 dimension sectors, sourced 12+78, generic Hom/cocycle and JFine D4 gauge owner.
2. Executed locally: original exact finite JFine/D4/H certificate, selected phase arithmetic controls, and S3×C4 class-algebra algorithm positive/negative controls.
3. Source-written, NOT executed: CTblLib-only 3B centre class-algebra D4 screen; source-reused AtlasRep actual 3B centralizer screen; optional 2026 mmgroup generator / matrix-free T route.
4. Only source-specific missing outcome: actual MN3B class-fusion survivor/no-go receipt for THIS geometric D4 character, followed (only for a survivor) by an actual embedding and the same-object linear Hom/inertia intertwiner. Geometric full `Fin90` permutation remains ruled out for the source 6.Suz character regardless of D4 compatibility.
5. No claim of GAP, Agda or full N(3B) source-coordinate T execution is made. Keep original author attribution and do not turn a possible class fusion into an actual subgroup.
