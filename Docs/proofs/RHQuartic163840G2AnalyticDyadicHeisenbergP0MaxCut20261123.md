# RH/GRH P0 — genuine G2 H_X test, 163840 continuous dyadic tail, paired H6 and strict no-go (23 Nov 2026)

**Status:** local independent SymPy 1.14 + mpmath 1.3 and exact F₃ matrix tests **PASS**. New Agda proof sources **written, NOT typechecked**. No Lean/Agda/CI run. Original RH PR #1533 branch; crosslink H05 PR #1291. **RH/GRH remain open.**

## 1. Source-first audit, no duplicate analytic intertwiner

**Existing authoritative owners:** \`DASHI/Analysis/RiemannAnalyticComplexCharacterExtensionExact.agda\` defines the dependent \`H_X\` complex character; \`RiemannCanonicalComplexCharacterAttachmentExact.agda\` compiles the H_X package from an actual canonical-carrier attachment; \`RiemannG2CanonicalHXToHTCompilerExact.agda\` proves the source \`e^{i(b-t)u}=e^{-itu}e^{ibu}\` translation/modulation law **conditional on that H_X**. \`RiemannG2SourceNativePhiHatModulationAdapterExact.agda\`, \`RiemannG2GammaMellinProofRelevantActionCompilerExact.agda\` and \`RiemannG2HASingleSourceProducerBidiExact.agda\` require source Test identity, admissibility, and SAME RiemannExplicitFormula spectral shift on one proof-relevant producer. No concrete producer for the ORIGINAL selected quartic W(t) has been established by these import-only compilers. H_X is **not** supplied by the finite Monster source; do not rebuild it.

Lean original: \`Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierMass.lean\` owns \`Psi_t(x)=r^-2 C_W((x-t)/r)\`, \`r=t/16\`, center origin mass 128π/(tRM₀)OriginDet_W and full mu integral. \`...FourthOrderQuotient.lean\` owns even \`C_W\`, profile moment, original selected cubic \`G_W\`. \`...NMu.lean\`, \`...Cutset.lean\`, \`...FourierTerminal.lean\` own actual-zero sums and strict terminal.

**Actual analytic test.** For any original real-even compact smooth P_W, F_P(b)=∫P_W(u)e^{ibu}du and M_tP_W(u)=P_W(u)e^{-itu}. Then by character multiplication F_{M_tP}(b)=F_P(b-t). This is the same ordinary H_X analytic law in the original transform notation, but M_tP generally becomes nonreal and noneven. The real-even projection E_tP=P_W(u)cos(tu) IS another legitimate compact even test with exact
\`\`\`
C_{E_tP}(q) = [C_W(q-t)+C_W(q+t)] / 2,
(E_tP)(0)=P_W(0),
(E_tP)''(0)=P_W''(0)-t² P_W(0).
\`\`\`
Seven such multipliers at independently chosen real frequencies a_j commute, preserve P_W(0) and hence 128 mass, but change cubic G_W by -6π(t/16)P_W(0)∑a_j². They are **NOT C₂ involutions**: cos²(a u)≠1. Their products generally leave the specially selected original four-window family and need new witnesses before entering the original terminal. This is a real source-relevant analytic operation with a decisive failure of symmetry, not a Monster-on-zeros claim.

**Original Gamma reflection:** S_{t,r}f(x)=r^-2 f((x-t)/r), R_qf(q)=f(-q), R_xg(x)=g(2t-x). Then S R_q = R_x S, and C_W is even. For the exact original mu, the full untruncated variation V_W=(8/t)∫ C_W(q)[mu(t+tq/16)+mu(t-tq/16)-2mu(t)]dq. The local numerical check used an *explicitly separate real-even Gaussian fixture* P(u)=exp(-u²/2)cos(16u), concentrated on q≈±16. At t=200, direct full-line Gamma integral and bilateral form agreed with absolute residual ≈1.23e-32. This checks the original transformation formula but is NOT an original existentially selected W.

**Actual zeros negative control:** independently evaluated the first four actual ζ zero ordinates with mpmath.zetazero and checked their finite transform response before/after a q shift. Those finite responses differ. This is not the completed infinite explicit formula or evidence of off-axis zeros; it shows no assumed zero-functional invariance under translation. All prime powers stay absent for the original selected support when any bounded complex phase/cosine multiplier is used: t≥200, R<1 imply 16(π+R)/t < 16(π+1)/200 < log2, and a multiplier cannot enlarge support. Thus no prime channel is revived by these seven multipliers.

## 2. Nontrivial 163840 continuous tail BIDI (not just a count)

**Existing 15-bit owners:** \`DASHI/Analysis/NonArchimedeanMonster3BActionSeparationExact.agda\` proves source order 2^15=32768 for *odd-residue multiplication by three at n=17*, and explicitly blocks identification with Monster 3B order-three; \`DASHI/Biology/DASHIQuantumLikeEntropyOscillatorExact.agda\` proves actual 15-bit capacity 32768. The original RH tail 163840 has different source semantics:
\`\`\`
∫_8∞q^-6 dq = (5*8^5)^-1 = (5*32768)^-1 = 1/163840.
u=(8/q)^5: q^-6 dq= -du/(5*8^5).
\`\`\`
**ACTUAL continuous measure-intertwining map:** for q>8 put k=floor(32768 u) and θ=32768u−k. Recover u=(k+θ)/32768, q=8*(32768/(k+θ))^(1/5), for 0≤k<32768 and 0≤θ<1 (omit the measure-zero end/tie cases). The pushforward of q^-6 dq is constant-density Lebesgue du/163840. For every integrable F:
\`\`\`
∫_8∞ F(q)q^-6 dq
 = (1/(163840*32768)) ∑_(k=0)^32767
       ∫_0^1 F(8*(32768/(k+θ))^(1/5))dθ.
\`\`\`
The first 15 bits form a genuine reversible coarse atlas **only with θ retained**, not a finite truncation. This is an exact weighted-integral normal form, not a claim that a 15-bit dyadic arithmetic permutation acts on the original q-tail. The original physical μ zero-ordinate crossing q=16 maps to u=1/32, hence **k=1024**, separating 1,024 address cells beyond q16 from 31,744 before it. Strict q>16 holds 1/32 of the *q^-6 reference-envelope measure*, not necessarily 1/32 of the signed Gamma variation. The source crossing itself is retained as an exact boundary; no Stirling substitution at its zero ordinate.

The same envelope geometry shows ratios between ≥16 and ≥8 for q^-4, q^-5, q^-6 are 1/8, 1/16, 1/32 respectively. Existing Gamma tail bound from previous tranche remains conditional on L6(W)=||P_W^(6)||₁, with external q tail fully covered. The source-selected W(t) has R=min(1,R0,dTarget(t),dOrigin(t))/2, so without a t-uniform lower bound on R and a source derivative envelope, no uniform L6 is produced. A 4th-Lipschitz bound does not automatically yield a 6th-derivative norm bound.

**New Agda source crosswalk:** \`DASHI/Analysis/RHQuartic163840DyadicTailHXIntertwinerExact.agda\` imports original dyadic-order, capacity and **conditional** H_X→H_T owners; proves the exact integer 5×2^15 and k=1024/31744 ledger definitionally. Its analytic chart/Jacobian is only locally tested and documented, **not kernel-proved in Agda**. That distinction is intentional.

## 3. Native Monster 3B Heisenberg action: stronger than an X6 sign patch

Native \`DASHI/Moonshine/Monster3BFiniteHeisenbergCentralExtensionExact.agda\` explicitly defines 12D (x,ξ) and the 13D central extension H6=(x,ξ,c), with
\`\`\`
(x,ξ,c) ⋅ (y,η,d) = (x+y, ξ+η, c+d+ξ⋅y).
Ω((x,ξ),(y,η)) = x⋅η − y⋅ξ (mod 3).
\`\`\`
For any 6-bit mask m, let D_m=diag((-1)^m_i) in F3 and T_m(x,ξ,c)=(D_m x,D_m ξ,c). Then D_mᵀD_m=I and
\`\`\`
Ω(T_m u,T_m v)=Ω(u,v),
T_m(g⋅h)=T_m(g)⋅T_m(h),
T_m T_n=T_{m xor n}=T_n T_m.
\`\`\`
This is a real \`C₂⁶\` subgroup of the automorphism group of the **native finite Heisenberg model**, not merely an injection of a 128-state binary patch. The seventh external \`SignedSSPFRACTRANWeaveExact.SignedMultiplicity\` sign reversal extends the model to \`C₂⁷\` while keeping neutral/zero fixed. A **primal-only** sign flip fails the central cocycle, which is a valuable negative control: paired dual action is compulsory. These automorphisms are not asserted to arise from actual Monster normalizer group elements, and none is an RH ζ-zero action.

[Agda source-written paired automorphism theorem](../../DASHI/Analysis/RHQuartic128HeisenbergPairedSixSymplecticExact.agda) imports the *original* H6 \`compose\`, \`symplecticPair\`, and the previous seven-mask owner; states explicit \`maskX6Adds\`, \`maskDotInvariant\`, \`maskSymplecticInvariant\`, \`maskHeisenbergCompose\`, \`maskSignedHeisenbergLaw\`. Still no kernel acceptance. [Independent local exact finite-field regression](../../scripts/check_rh_128_native_heisenberg_pair_sign_20261123.py) PASS: all 64 paired 12×12 symplectic matrices, 4096 composed mask pairs, 19200 actual F3 group-law and symplectic tests, explicit failed unpaired case. No ESD changes; new modules imported in TOE roots.

## 4. True same-object seven-mask gauge is mathematically trivial

Represent the *same* source analytic observable as (b,A)↦A w(b)/128 Ψ_W with w(b)=2^(sum seven bits). Then
\`\`\`
(b,A) ↦ (b xor m, A*w(b)/w(b xor m))
\`\`\`
is a faithful C₂⁷ action on the extended labels and a real same-object gauge realization. It leaves Ψ_W and every zero/Gamma evaluation exactly unchanged, **hence cannot improve any signed terminal**. The local exact rational check covered all 128×128=16384 mask-source pairs and round-trip recovery. Without amplitude compensation, each singleton generator sends selected all-ones coefficient 128→64 and is not a symmetry of the original test. No nontrivial physical seven-axis realization is licensed.

## 5. Exact RH/GRH obstruction remains separate

With actual original Lean \`completedSignedResidual_eq_combinedCluster\`, \`combinedCluster_eq_tsum\`, \`postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack\`, for hypothetical off-critical target and its pair,
\`\`\`
Gap=H_t+S_t−(4d_t+I_t)=2(D_t−2d_t)+S_t≥0
\`\`\`
under original nonnegative local slack and D_t≥2d_t. A **new independent** upper bound proving Gap<0 would contradict existence; no finite/analytic modulation or dyadic decomposition above supplies this. This audit narrows P0 to (1) actual source-selected W analytic test/action admission and height-uniform derivative/tail, (2) original signed zero distribution comparison, (3) χ-indexed actual GRH source identity and conductor/parity.

## Acceptance and attribution

- Independently executed local Python/SymPy+mpmath, full script \`/mnt/data/rh_analytic_163840_local.py\`: character identity, seven cosine curvature and no-C2, 15-bit 32768×2 exact rational chart samples, q16 crossing, actual Γ reflection both parities/four conductors, Gaussian crossing-focused full integral residual 1.23e−32, first four actual ζ ordinate finite shift control, 16384 gauge checks and original prime-silent support, completed terminal obstruction — **PASS**.
- Independently executed local \`/mnt/data/rh_heisenberg_6mask_local.py\`: 64 symplectic matrices, 4096 mask pairs, 19200 actual H6 finite-group spot checks, failing unpaired sign — **PASS**.
- Repository companion scripts \`scripts/check_rh_g2_analytic_163840_native_dyadic_20261123.py\` and \`scripts/check_rh_128_native_heisenberg_pair_sign_20261123.py\` committed/read-back pending; they were **not run separately from their fetched GitHub blobs**.
- Original sources: Zeta23/Anthropic \`GammaFacts/Mu\`, \`ThmE/GammaFactsChiProof\`; original dashi_lean4 selected quartic Fourier mass and terminal; original DASHI H_X/H_T, Monster H6, signed SSP, dyadic order. DASHI contribution is the above cross-source tests, analytic algebra, typed crosswalk and no-promotion ledger.


---

## 23 November — seven EXACT measure-space actions and compact Fourier obstruction (next tranche)

**New locally tested code:** `scripts/check_rh_163840_signed_dyadic_analytic_closure_20261123.py` (separate from the previous 163840 chart regression). This strengthens the previous **number/chart** correspondence to a faithful action on the **actual weighted Gamma-tail integration domain**. It is NOT a physical C2^7 action on the selected original Weil test, not an SSP generator identification, not a Monster group action, and not a zero-distribution estimate.

Set `T={q∈R: |q|>8}`, `dν(q)=|q|^-6 dq`. On either signed ray write `s=sgn(q)∈{±1}`, `u=(8/|q|)^5∈(0,1)`, `N=32768=2^15`, `k=floor(Nu)` and `θ=Nu−k∈[0,1)`. Thus `q=s 8(N/(k+θ))^(1/5)` (away from null boundaries). The **exact signed full-tail** measure relation is

```text
∫_{|q|>8} F(q) |q|^-6 dq
 = 1/(163840 · 32768)
   Σ_{s=±1} Σ_{k=0}^{32767} ∫₀¹
     F(s · 8 · (32768/(k+θ))^(1/5)) dθ .
```

For `m∈{0,...,63}` and `ε∈{0,1}`, the operations

```text
T_(m,ε) : (s,k,θ) ↦ ((-1)^ε s, k XOR m, θ)
T_a T_b = T_(a XOR b) = T_b T_a ; T_a² = identity .
```

form a faithful `C₂⁶×C₂=C₂⁷` **measure-preserving** action on this signed weighted tail. The 15-bit address retains its continuous residual θ; six of the fifteen cell bits carry the selected dyadic toggles; the seventh sign is the **physical ordinate reflection**. The separate signed SSP carrier is an analogy/possible bookkeeping donor only: no same-source correspondence between its signed multiplicity and `sgn(q)` has been proved. Nor is this cell action the native Heisenberg six-sign action. Original `q=±16` crossing remains at `k=1024` on each ray. The q^-6 reference measure beyond |q|>16 is 1/32 of the positive-ray (or two-sided) reference mass, NOT the signed Gamma or zeta mass.

For the **actual** original even `C_W` and exact bilateral `Δ²μ_{κ,N}(t,q)`, `q↦−q` fixes the integrand; six bit operators preserve the integral by measure reindexing **only if the entire transformed integrand is pulled back**. They do NOT preserve `C_W(q)` or `Δ²μ(t,q)` separately, nor the physical selected test.

### Strict test-space closure no-go

For each `j=0,...,5`, set `k_j=N−2^j`. At the cell boundary `u_j=k_j/N`, the left and right `u` image limits under XOR `2^j` are, **exactly**, `1` and `1−2^(j+1)/N` (different by `2^(j+1)/N`). Their inverse q-image limits lie in [8,8.1] and differ. Choose **any smooth even nonnegative nonzero compact bump** `P` supported in `(-1/4,1/4)` with positive mass away from zero. Its ordinary cosine Fourier transform satisfies

```text
C_P'(q) = -2 ∫₀^(1/4) v P(v) sin(qv)dv < 0   for 8 ≤ q ≤ 8.1,
```

because `0<qv<8.1/4<π`. Thus `C_P(q(T_j(u)))` has a genuine jump at `u_j`. Fourier transforms of integrable functions are continuous; consequently the bit-toggled source is **not in the full compact-smooth Fourier class**. This is an explicit closure counterexample, not a universal claim that the particular existentially selected W has such a jump.

There is also a topological obstruction: every Lebesgue-measure-preserving homeomorphism of `[0,1]` is either identity or reflection (monotonicity plus interval-length preservation), so no faithful **continuous** `C₂⁶` action can be obtained by such 1D cell rearrangements. The dyadic operation necessarily leaves the continuous source-test category, except for genuine reflection. Finite H6/SSP axes and numerical bit labels cannot repair the analytic/admissibility requirement by themselves.

### Acceptance and proof boundary

Local exact `5·8⁵` Jacobian, 32768 cell maps for all 64 masks, 128 mask laws and 4096 pair compositions, six exact jump sizes with separate smooth Gaussian fixture, q=±16 Gamma reflection and six two-cell Gamma integral reindexings for each parity all **PASS**. The compact bump inequality is a direct sign proof; numeric Gaussian is only a negative-control fixture. The existing earlier selected-W Gamma bound remains conditional on `L6(W(t))`. The original terminal remains `Gap=2(D−2d)+S≥0` under a hypothetical reflected off-axis pair. No new *independent* strict signed zero bound, kernel receipt, RH or GRH claim follows.

**Next P0 min-cut:** source-native admissible `sampleTest/paperFT` map for original selected W, selected-W uniform derivative envelope with its actual variable R(t), and actual signed `H_W+S_W<4d_W+I_W` independent of mere reindexing (including horizontal zero coordinate/multiplicity). Avoid a new finite-index dictionary in place of the signed estimate.
