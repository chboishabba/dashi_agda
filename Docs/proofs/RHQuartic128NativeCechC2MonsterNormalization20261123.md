## 23 November 2026 — P0 MAX-CUT: SEVEN genuine finite generators, original Gamma C2 reflection, full-tail and terminal audit

**LATEST live source recheck (do not reset heads):** RH #1533 at c9995e49 before this tranche, Lean #113 at 5b22b8f8, H05 indexed cube #1291 at 46bf5b9f. Source owners below are reused, not replaced. New code is AGDA **source-written**, NOT kernel-accepted; local SymPy/mpmath independent run PASS. No new RH/GRH/Monster-group theorem.

### A. Seven independent signed axes, actual original X6 and SSP labels (completed finite stage)

The earlier module \`DASHI/Analysis/RHQuartic128Monster3BSSPSignedC2IntertwinerExact.agda\` supplied a **single** simultaneous C2 negation. It now defines:
- seven-bit \`maskXor\` / \`maskAct\` with XOR associative and commutative, \`maskActLaw\` and \`maskActCommutes\`;
- **seven independent coordinate generators** acting on the actual existing \`Monster3BFiniteHeisenbergGeneratorsExact.X6=F3^6\` by six *separate* \`negate3\` automorphisms, and on \`SignedSSPFRACTRANWeaveExact.SignedMultiplicity\` by seventh \`negateMultiplicity\`;
- \`actOnNativeSignedX6Law\`, \`encodeIntertwinesAllSeven\` and \`nativeActionFaithfulOnEncodedPatch\`. A mask is recovered by acting on the all-false encoded state; 128 distinct masks, no unintended scalar-action kernel. Simultaneous inversion is the all-ones mask.
- the native X6 all-zero coordinate and signed zero survive as fixed points, but lie outside the nonzero binary image; no binary-forgets-sign move.
- precise source-ENDPOINT negative control: for any of the seven distinct singleton generators \`coefficient(maskAct(generator,allOnes))=64\`, not 128. Hence they are **not seven source-preserving transformations of the original fixed selected \`sampleTest\`**. The extra actions are actual finite-model coordinates, NOT known elements of the Monster 3-group (which has no involutions), nor an original seven-parameter physical scaling. The \`C2^7\` acts by coordinate sign automorphisms, not by the order-three Heisenberg translations.

The exact existing analytic RH intertwiner is *not missing or a Monster theorem*: \`DASHI/Analysis/RiemannG2CanonicalHXToHTCompilerExact.agda\` already compiles \`exp(i(b-t)u)=exp(-itu)exp(ibu)\` from the canonical \`RiemannAnalyticComplexCharacterExtensionExact\` H_X. \`RiemannG2GammaMellinProofRelevantActionCompilerExact.agda\` owns the proof-relevant implementation-to-Weil action seam; the original realized data/admissibility arguments are distinct from the new finite \`C2^7\` action.

### B. ACTUAL analytic same-object Gamma intertwiner, not the seven-bit model

For the ORIGINAL \`QuarticFourSignedPolePair W\` let \`r=t/16\`,
\`C_W(q)=integral P_W(v) cos(qv)dv\`,
\`Psi_t(x)=r^-2 C_W((x-t)/r)\`. Existing Lean \`FourthOrderQuotient.compactCosineTransform_even\` and \`signedOrdinateTestDeriv_center_reflection\` ensure the center-even test; \`FourierMass\` owns \`fullMuVariation\`, integrability and normalization, \`NMu\` the original \`signedOrdinateTest\`.

Define actual reflection \`R_q f(q)=f(-q)\`, physical-ordinate reflection \`R_x psi(x)=psi(2t-x)\`, and \`S_{t,r}f(x)=r^-2 f((x-t)/r)\`. Direct calculation proves
\`S_{t,r}∘R_q=R_x∘S_{t,r}\`, \`R_q C_W=C_W\`, \`R_x Psi_t=Psi_t\`, and (full-line absolutely integrable, no artificial support truncation)
\`\`\`
V_W(t) = integral_x Psi_t(x)(mu(x)-mu(t))dx
       = (1/2) integral_x Psi_t(x)[mu(x)+mu(2t-x)-2mu(t)] dx
       = (8/t) integral_q C_W(q)
           [mu(t+tq/16)+mu(t-tq/16)-2mu(t)]dq.
\`\`\`
**This is the real original source C2 analytic commutation square**. It cancels the odd first Taylor mode exactly. It is not seven commuting analytic actions; the binary factor axes remain a distinct model. Upstream Zeta23 \`muq κ N\` conductor shift is an exact **constant**, so it disappears from this second difference for fixed parity and survives only as \`64 log N/(t R M0) OriginDet_W\` in the center mode. It does NOT identify χ zero configurations or parity.

### C. NEW complete Gamma uniform-*coefficient* tail envelope, INCLUDING q=±16

Use REAL theorem-bearing upstream [Anthropic Zeta23 GammaFacts](https://github.com/anthropics/formal-math/blob/main/zeta23/Zeta23/GammaFacts/Mu.lean) \`mu\` even and monotone on the nonnegative ordinates, \`mu(0)>-1\`, and [\`GammaFactsChiProof\`](https://github.com/anthropics/formal-math/blob/main/zeta23/Zeta23/ThmE/GammaFactsChiProof.lean) \`|mu_{κ,1}(y)-log(|y|/2π)/(2π)|≤10/(π y²)\` for |y|≥1, both κ. For \`t≥200\` and any q,
\`\`\`
A=t(1+|q|/16),  mu_{κ,1}(0)≤mu_{κ,1}(t±tq/16)≤mu_{κ,1}(A);
|Delta² mu_{κ,1}(t,q)|≤2(mu_{κ,1}(A)-mu_{κ,1}(0))
                         ≤2(mu_{κ,1}(A)+1)
                         ≤2[1+log(t/(2π))/(2π)+|q|/(32π)+10/(π t²)].
\`\`\`
The last step applies Stirling ONLY at the upper ordinate \`A≥t≥200\` and uses \`log(1+|q|/16)≤|q|/16\`. It is therefore valid at **q=±16**, where one shifted ordinate is zero and the naive pointwise logarithmic approximation is invalid. The conductor cancels before applying this bound, so the same absolute *variation* bound holds for every N≥1 and both κ (with the same analytic W, not a character-specific constructed W).

For compact C∞ ORIGINAL \`P_W\`, integrate six times by parts in the cosine Fourier transform: \`|C_W(q)|≤L6/|q|^6\`, where \`L6=||P_W^(6)||_1\`. Let \`V_tail=(8/t)∫_|q|>8 C_W(q)Delta²mu(t,q)dq\`. The actual full-line estimate is
\`\`\`
|V_tail| ≤ (32 L6/t) [
  (1/163840) (1+log(t/(2π))/(2π)+10/(π t²))
  + 1/(524288 π)
].
\`\`\`
The exact antiderivatives are \`∫_8∞q^-6 dq=1/163840\`, \`∫_8∞q^-5 dq=1/16384\`; 1/524288π is the latter divided by 32π. This is **new source-specific quantitative control** of the whole exterior region, conditional on the same original selected W's finite \`L6\` and not uniform in t until \`L6(W(t))\` is paid.

With \`G_W=6π(t/16)P_W''(0)\`, \`M0_core=∫_|q|≤8 |C_W|\`, \`M4_core=∫_|q|≤8 q^4|C_W|\`, the already-verified core and full Fourier second moment imply
\`\`\`
|V_W-G_W/(12πt²)| ≤
   L6/(49152πt) + M4_core/(24576πt) + 800 M0_core/(πt³)
   + (32 L6/t)[(1/163840)(1+log(t/(2π))/(2π)+10/(πt²))
                 +1/(524288π)].
\`\`\`
No q-region, neutral crossing, or Fourier tail has been dropped. \`M2_tail\` exactly contributes the first \`L6/(49152πt)\` envelope using \`2∫_8∞q^-4 dq=1/768\`.

**Main remaining W(t) problem:** source \`PostSixthAbsorb.exists_quarticFourSignedPolePair_with_strength_floor_and_negative_origin\` chooses \`R=min(1,R0,dTarget(t),dOrigin(t))/2\`, where the small-radius thresholds can depend on t. The previous uniform fourth-Lipschitz \`K0\` does NOT by itself bound the sixth-derivative L1 norm of the independently chosen W(t) uniformly. A new selected-W quantitative derivative envelope or cancellation estimate must be proved before promoting to a height-uniform estimate. No new universal Gamma sign is asserted.

### D. Direct test against original TRUE post-sixth terminal: exact fail-closed floor

Reuse Lean \`Cutset.combinedCluster_eq_tsum\`, \`NMu.completedSignedResidual_eq_combinedCluster\` and \`FourierTerminal.postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack\`. With D_t original SAME-ordinate defect cluster, H_t full OFF-ordinate signed source, I_t full original Gamma/μ integral, S_t original nonnegative local budget slack, d_t the target defect:
\`\`\`
H_t-I_t=2D_t,
Gap := H_t + S_t - (4d_t+I_t) = 2D_t + S_t - 4d_t.
\`\`\`
If a target off-critical zero exists, the paired reflection has SAME t, multiplicity, positive defect; original theorem \`two_target_le_combinedCluster\` gives \`D_t≥2d_t>0\`. Thus \`Gap≥S_t≥0\`. The desired strict terminal would require \`Gap<0\`, so it **cannot be established by rearranging** the already-complete Gamma/zero equality. The new Gamma full-tail estimate is an independent control of the density functional but does NOT pay the strict zero-side cancellation or selected-W uniformity. This recovers precisely why proving the strict terminal would rule out off-critical zeros if derived independently. Do not claim RH or GRH from the lower bound.

### E. Flags, measured rather than pattern promoted

The original quadratic moment gives \`P_W''(0)/(32t)\`, where \`32=16²/8=2^5\` after the 4/(πt) log core and inverse-cosine moment. It does not produce the unrelated BSD level-32 Fricke transformation. \`64 log N\` is conductor \`log N\` times the exact 128/2 density conversion, not \`log n\` prime powers. \`80=8×10\` and \`800=8×10²\`; therefore \`log_10 80=1+log_10 8\` and \`log_10 800=2+log_10 8\`, but original 80=8×(4+4+2) and 800=80×(10/π) after factoring 1/π from upstream Stirling. This is a legitimate scientific-notation conversion **not** the source of a \`log8\` contribution to μ or zero counts. \`768=3×16²\` from the exact sixth-derivative Fourier-tail primitive; no pants or source-geometry factor was inferred from 3 alone.

**Local acceptance:** independent \`/tmp/rh_128_7_gamma_full.py\` (SymPy/mpmath) PASS: all 128 mask C2^7 actions, 128×128 mask combinations on the chosen encoded source state, 128×128 source equivariance matrix, 21 generator pairs, exact logarithm/ratio constants, both κ, T=200/800/2000, 12 q including 16 and four conductor values, strict signed terminal gap. Committed regression [\`scripts/check_rh_128_seven_independent_gamma_fulltail_20261123.py\`](../../scripts/check_rh_128_seven_independent_gamma_fulltail_20261123.py) is source-equivalent but not separately executed after GitHub upload. No Agda/Lean kernel / CI.

**STATUS:** finite C2^7 action and actual original analytic Gamma-C2 involution mathematics established at source/independent local level; connecting the 7 factor model to 7 independent *physical* source operations is demonstrably not a symmetry of the fixed 128 coefficient. No Monster group action, no analytic selected-W group action, no GRH all-character zero-source weld, and no strict signed P0 proof.

---

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
