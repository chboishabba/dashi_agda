# RH P0 — original 128 normalization to seven-bit / six-face Čech and native 3B×SSP C₂

**23 November 2026. Branch:** RH/GRH PR #1533. **Status:** executable finite mathematical construction; Agda source-written but **kernel NOT run**; **no RH/GRH strict signed bound**.

## 1. Actual source and prior-art owners (reuse, never duplicate)

1. `chboishabba/dashi_lean4`, `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierMass.lean`: `signedOrdinateTest_mass_eq_originDet` is original exact
   `∫ Ψ_t = 128 π/(t R M₀) OriginDet_W`. Source 128 factorizes **16** from actual physical `r=t/16`, **2π** from even Fourier inversion, **4** from original profile value `P_W(0)=4 OriginDet_W/(R M₀)`. The function `W` and `OriginDet_W` remain the original selected endpoints.
2. `...FourthOrderQuotient.lean`: original `∫ q² C_W(q)dq = -2π P_W''(0)` and exact `globalCubicModeDefect`; no free quartic/C₄ source is invented.
3. `DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda`, `Base369Ternary27BoundaryNerveExact.agda`, `Base369Ternary27CornerEightExact.agda`: six **actual** ternary cube outer face labels; 12 pairwise edge objects; eight outer corners.
4. `DASHI/Moonshine/Base369Ternary27FaceHypercubeCechGluingBidiExact.agda`, `DASHI/Reasoning/ActualFaceHypercubeGluingFromSharedSliceExact.agda`: original invertible Cech edge transports, corner cocycle and actual-state recognition requirements.
5. `DASHI/Foundations/TernaryThirteenPantsSheafGluingTransportExact.agda` and `DASHI/Moonshine/JInvariantSheafHyperformAdmissibleDescentExact.agda`: typed admissible overlap, matched neutral section and pants nonpromotion. These are **not** an identification of the RH coefficient with a topological surface.
6. `DASHI/Moonshine/Monster3BFiniteHeisenbergGeneratorsExact.agda`: actual **X6=F₃⁶** (729-state) Schrodinger coordinate; `negate3`. `DASHI/Biology/SignedSSPFRACTRANWeaveExact.agda`: actual signed multiplicity and `negateMultiplicity`, including fixed zero. `Monster369SignedSSPTauInversionSeamExact` already blocks uncontrolled modular Fricke/Monster identity.
7. Existing H05 [indexed cube roadmap on PR #1291](https://github.com/chboishabba/dashi_agda/pull/1291) distinguishes original **RH C₄ Fourier phase** from C₃ spatial phase and proves real-q / smoothing / winding information cannot be discarded. Our new finite chart does not supersede H05.

## 2. Exact 128 labelled factor carrier and 6-face sheaf

Define `BinarySeven = {0,1}^7` with ordered blocks `(a₀,a₁,a₂,a₃ | b₀ | c₀,c₁)`. Define **positive coefficient** `w(bit) = 2^(sum all seven bits)`, retaining source block weights `wA=2^(Σ a_i)`, `wB=2^b₀`, `wC=2^(c₀+c₁)`. At the all-one endpoint, `(wA,wB,wC)=(16,2,4)` and `w=128`. **Only this endpoint is identified with the original Fourier-mass theorem.** Intermediate bit states are formal factorizations of the original coefficient, not new physical samples or seven independent analytic actions.

Project to the literal Base369 corner with bits `(a₀,b₀,c₀)`; retain residual `(a₁,a₂,a₃,c₁)`. Exact split/join:
```
BinarySeven ↔ BoundaryCorner3 × ResidualBinary4
128 = 8 × 16.
```
For each of the original six face constructors, restrict to states whose corresponding selected corner bit equals that face's sign. This is an actual **cover** of the 128 address carrier, not a mere matching cardinality:
- 6 face subsets of 64 states;
- 12 non-opposite pairwise edge overlaps of 32 states;
- 8 triple-corner overlaps of 16 states;
- every state belongs to exactly three faces.

A local section is a value on an incident face; its chart expression may differ by an explicitly invertible rational gauge `λ_face`, with `T_{f→g}=λ_f/λ_g`. Matching requires `λ_f local_f(s)=λ_g local_g(s)` on every edge. At corners `T_{x→z}=T_{y→z} ∘ T_{x→y}`. For compatible families, pointwise gluing recovers the unique global value. Adversarially mismatched local data fails. **Zero and sign remain separate source labels**; a positive normalization coefficient is never allowed to force the original signed witness positive.

New [source-written Agda](../../DASHI/Analysis/RHQuartic128SevenBitFaceCechGluingExact.agda) constructs the two-sided split/join, literal source-corner `OnFace` inhabitants, seven-factor coefficient, actual admissible matching predicate, restrict/glue and uniqueness pointwise. Its three-source-leg scalar composition is only *pants-shaped*: it does NOT establish a 2D cobordism, real analytic stalk, a 27-point centre, or a nontrivial Grothendieck topos. In particular, the 8 corner atlas excludes the 19 non-corner points of the original 27-point ternary cube.

## 3. A further genuine action intertwiner on EXISTING Monster/SSP model carriers

Define a **chosen** finite map
```
ι : {0,1}^7 → H.X6 × SSP.SignedMultiplicity
ι(a₀,a₁,a₂,a₃,b₀,c₀,c₁)
 = (x6(τ(a₀),τ(a₁),τ(a₂),τ(a₃),τ(b₀),τ(c₀)), σ(c₁))
τ(0)=−1, τ(1)=+1 in F₃; σ(0)=negativeMultiplicity(1), σ(1)=positiveMultiplicity(1).
```
Original H.X6 has 729 states but this chosen *nonzero sign patch* has 64. Together with the 2-element signed SSP patch it has **128 distinct images**. The explicit decode is a LEFT inverse of ι; consequently ι is injective. Let `flip` complement all seven binary bits, `J` negate each X6 coordinate and the signed-SSP multiplicity. Then
```
ι(flip(bit)) = J(ι(bit)), J² = id on its full model carrier,
w(bit) w(flip(bit)) = 128.
```
This is an **actual C₂-equivariant map into the repository's existing finite Heisenberg coordinate and signed FRACTRAN carriers**, not just a 128-count coincidence. The complement is NOT a symmetry of the original positive RH mass coefficient: it sends `w → 128/w` and generally does not leave w unchanged. The **neutral X6 + zero SSP fixed point exists in the target but not in the binary image**; its inclusion requires a distinct extra branch. There is **no** established Monster group element realizing this C₂, and no analytic `sampleTest/paperFT/μ` or original ζ-zero intertwiner. New [source-written Agda intertwiner](../../DASHI/Analysis/RHQuartic128Monster3BSSPSignedC2IntertwinerExact.agda); import-only bridge wired into `DASHI/Unified/Relate369HyperfabricPantsTOEExact.agda`, `DASHI/EverythingTOESymmetryResolved369.agda` and `DASHI/Unifier.agda`, preserving original attribution and no ESD edits.

## 4. Dimensional flags: exact source meaning and no-go controls

| Observed scalar | Actual identity | Not licensed |
|---|---|---|
| 32 in `P_W''(0)/(32t)` | `(4/(πt))×(1/256)×(2π)=1/(32t)`: quadratic Fourier moment | 32 independent dimensions or BSD level-32 Fricke |
| `64 log N` | conductor `μ_{κ,N}-μ_{κ,1}=log N/(2π)`, times original 128π profile mass = `64 log N OriginDet/(t R M₀)` | prime power n or an unproved Fricke action |
| 800 in `800 M0_core/(πt³)` | `80×10`, from (8/t) bilateral prefactor, (4+4+2) Gamma Stirling errors and upstream `CΓ=10/π` | `800=log(9−1)`; numerical `800=100(9−1)` alone does not transport 9→8 punctured geometry |
| 768 in `||P_W⁽⁶⁾||₁/768` | `768=3×256=3×16²`, with `2∫₈^∞q^{-4}dq=1/768`; factor three comes from anti-derivative exponent | the three pants legs or 3 cube axes as source theorems |
| Six Fourier samples | values `q=2,8,12,20,24,32` from earlier diagnostic only | six admissibly glued cube-face sections |

**Decisive negative control:** assigning the six distinct original digamma responses at those frequencies to the six face charts violates matching on all 12 edges (at t=200). Moreover several frequencies share a C₄ phase but have different responses, confirming the existing H05 winding/continuous-q and smoothing no-descent. Numerical face count is not enough.

## 5. Local acceptance and the truly unpaid P0 cut

Independent local Python/SymPy 1.14 + mpmath test of the exact source-model algebra [`scripts/check_rh_128_sevenbit_face_cech_20261123.py`](../../scripts/check_rh_128_sevenbit_face_cech_20261123.py): **PASS 128/128** BIDI, **1,152/1,152** face restrictions, **1,152/1,152** reversible edge comparisons, **384/384** corner cocycles over three signed/zero polarities, hostile-section mismatch rejection, true underlying `F₃⁶ × SSP` C₂-equivariance and 128 weight-reciprocity, six-q no-glue control 12/12, exact constants 32/64/800/768. No Agda/Lean kernel executed; repository script text was committed and read back, not independently executed after upload.

The **analytic same-object theorem** still needs an actual map from the selected `W(t)` and original `sampleTest/paperFT` to a representation where the above seven operations act and commute on the SAME analytic test and zero source, including `q`, R, selected profile moments, C₄ winding, time, χ, conductor, source sign and zero multiplicities. Crucially the current C₂ flip exchanges coefficient `w↔128/w`, so it does NOT preserve the original fixed 128 normalization away from the endpoint. It cannot be used to prove `2 D_t+S_W<4 d_W(ρ)`: the original lower bound `D_t>=2 d_W(ρ)` and `S_W>=0` still obstruct proof by rearrangement. **No RH/GRH promotion**.
