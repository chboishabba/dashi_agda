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
