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
