## 23 Nov 2026 — P0: conditional canonical H_X verified numerically, dyadic full-tail chart, native H6 symplectic receipt

[Complete source/analytic/action ledger](RHQuartic163840G2AnalyticDyadicHeisenbergP0MaxCut20261123.md). Reused already existing canonical `H_X→H_T` proof, explicitly conditional on source `CanonicalCharacterAttachment`; our exact symbolic test of exp(i(b−t)u) and real even/cos shift passed; the selected W test representation is NOT constructed. Original Γ reflection direct and bilateral integrals were compared at t=200 using a separate Gaussian q≈±16 stress fixture, residual 1.23e-32; both Dirichlet parity and conductor-shift cancellation passed. Four actual ζ zero-ordinate samples changed under translation: spectral-shift is NOT zero-functional invariance. Seven cos operators on original real-even profile preserve its Fourier-origin mass but alter curvature (and selected W constraints); the only exact C₂⁷ action on the SAME unmodified Ψ_W uses reciprocal amplitude gauge, no new mathematics on zeros.

Source cutoff 8, sixth Fourier tail ∫_8∞q^-6 = 1/(5·8⁵)=1/163840; exact Jacobian of v=(8/q)⁵ makes the *weighted measure* uniform. Retain 32768=2¹⁵ source-coded cells AND real residual θ, source q=16 at cell k=1024; beyond q=16 has 1/32 of q^-6 reference mass. Repo has actual 32768 dyadic order at n=17, explicitly unequal Monster3B order 3; no same-action identification. Source `RHQuartic163840DyadicTailHXIntertwinerExact.agda` imports native donor, local SymPy exact BIDI PASS.

Paired original H6 primal+dual sign action yields real automorphisms of native finite Heisenberg central extension and symplectic pairing, verified 64/4096/19200 checks; primal-only negative control fails. Seventh external signed SSP invertor. Source `RHQuartic128HeisenbergPairedSixSymplecticExact.agda`, same three TOE roots imported. No actual Monster-normalizer element, no original ζ action. P0 `Gap=2(D−2d)+S` stays nonnegative if off-line target exists; need independent strict sign and selected-W derivative uniformity. No kernels/CI.

---
## 23 November 2026 — seven native signed axes and true Gamma/terminal same-object reflection audit

[Detailed full Gamma exterior and C₂⁷ finite model ledger](RHQuartic128NativeCechC2MonsterNormalization20261123.md). Source analytical reflection uses actual `S_{t,t/16}` scaled cosine test and `x→2t−x`, with original `mu`, `paperFT`, full q-line, no zero-side substitution. Existing H_X→H_T owner already proves exp(i(b−t)u)=exp(−itu)exp(ibu) on canonical RH analytic carrier, distinct from finite 3B/SSP 7-mask action. Full Gamma tail bound using upstream actual `mu(0)>-1`, monotone, parity-uniform Stirling: at t≥200, L6=||P_W⁽⁶⁾||₁,
`|V_tail|≤(32L6/t)[(1/163840)(1+log(t/(2π))/(2π)+10/(πt²))+1/(524288π)]`, valid at q=16 where log approximation is not. Hence complete absolute deviation of V from `globalCubicModeDefect/(12πt²)` is `L6/(49152πt)+M4core/(24576πt)+800M0core/(πt³)+Vtailbound`.

Local source-equivalent SymPy/mpmath PASS; witness selected R(t) is not uniformly lower-bounded, and actual signed terminal `2D+S<4d` remains in contradiction with target-pair D≥2d and S≥0 unless independently established. Source-only group-action / RH no-promotion respected.

---
## 23 Nov 2026 — add genuine finite 128 six-face sheaf and native C2 3B signed carrier, not RH-source action

[Full exact new proof/negative-controls ledger](RHQuartic128NativeCechC2MonsterNormalization20261123.md). Reuses original selected W normalization 128=16 physical ×2 Fourier ×4 origin and original Base369 actual six outer face labels; constructs 128=8 literal outer corners ×16 residual, two-sided fine/coarse, local admissibility and pointwise unique gluing. Existing X6=F₃⁶ Monster3B Schrödinger model plus SSP signed unit supports a nontrivial 128-element *injected* C2 patch, with exact complement intertwining; flip sends original scalar w→128/w, so it is NOT a symmetry of fixed original RH source. The separate zero is a C2 fixed point outside image. An independently tested exact finite construction, not a native Monster group action or RH analytic source morphism. Original selected six q-probe values fail 12/12 face overlaps. 32t/64logN/800/768 roles are source-derived scalar arithmetic only. No new universal full negative margin: `2D+S<4d` remains blocked by `D≥2d`, `S≥0`.

---
## 23 November 2026 — GRH Gamma parity/conductor exact square; universal explicit 800/pi bound

**New external prior-art owner found and reused:** upstream [Anthropic Zeta23 `ThmE/GammaFactsChiProof.lean`](https://github.com/anthropics/formal-math/blob/main/zeta23/Zeta23/ThmE/GammaFactsChiProof.lean), [`ThmE/Hypotheses.lean`](https://github.com/anthropics/formal-math/blob/main/zeta23/Zeta23/ThmE/Hypotheses.lean) and [`ThmE/RvMChi.lean`](https://github.com/anthropics/formal-math/blob/main/zeta23/Zeta23/ThmE/RvMChi.lean) already define and prove character parity `kappa∈{0,1}`, conductor `N>=1`, the completed `mu_{kappa,N}(x)=[log(N/pi)+Re digamma(1/4+kappa/2+i*x/2)]/(2*pi)`, and the **universal, conductor-independent and parity-independent** explicit Stirling estimate
`|mu_{kappa,N}(x)-log(N*|x|/(2*pi))/(2*pi)|<=10/(pi*x^2)` for |x|>=1. This is paid upstream; do not invent another Gamma asymptotic theorem. For kappa=0,N=1 it is the existing zeta `Zeta23.mu` source.

**GRH conductor commuting square, new elementary consequence:** `mu_{kappa,N}(x)=mu_{kappa,1}(x)+log N/(2*pi)` for a fixed parity. Thus `Delta2 mu_{kappa,N}(t,u) = mu(t+tu/16)+mu(t-tu/16)-2mu(t)` is **independent of conductor N**, while parity remains labelled through `1/4+kappa/2`. The *full* original selected W analytic Gamma variation `V_{kappa,N}(W,t)` is therefore equal to `V_{kappa,1}(W,t)` for every even test C_W with convergent integrals; this is a Gamma-only statement, NOT a χ-zero-sum identity or a new GRH source weld. Conversely, the character conductor survives exactly in the center mode:
```
I_{kappa,N}(W,t)-I_{kappa,1}(W,t)
  = [log N/(2*pi)]*integral Psi_t
  = [64*log N/(t*R*M0)]*OriginDet_W.
```
This new visible `64=128/2=2^6` is an algebraic zero-mode consequence, not a new 6D physical representation. For genuine primitive nonprincipal χ the original Theorem E source has **no pole term** (unlike zeta); prime coefficients χ(n) vanish if the actual physical test vanishes at log n, but the FULL χ explicit-formula normalization/target witness has not been welded.

**Stronger concrete P0 core:** insert the source universal `C_gamma=10/pi` in the preceding exact t>=200, |u|<=8 core bound:
```
|V_core - (4/(pi*t))*integral_core C_W(u)*log(1-u^2/256) du|
  <= (800/(pi*t^3))*M0_core.
```
This coefficient applies to both κ=0/1 and all conductor N≥1 at the Gamma-only level. The cubic/tail identity remains exactly
`V_W=globalCubicModeDefect/(12*pi*t²)+M2_tail/(64*pi*t)+V_tail+E_core`,
with `|E_core|<=M4_core/(24576*pi*t)+800*M0_core/(pi*t³)`. The uniform scalar coefficient does NOT certify the selected-W t-uniform L1/derivative norms, nor the sign of `V_tail`, nor any zero-side `χ` transport.

Local SymPy coefficient and actual mpmath digamma controls PASS at parity 0/1, conductor values 1,5,71,10007 and multiple heights; original source code [`check_rh_128_gamma_bilateral_20261123.py`](../../scripts/check_rh_128_gamma_bilateral_20261123.py) committed. Exact-head Lean/Agda kernel and end-to-end repo script execution not claimed. P0 strict signed RH/GRH terminal remains OPEN.

---
## 23 November 2026 — P0 new bilateral Gamma core, 128 provenance and cubic obstruction weld

**Live owners checked first:** RH PR #1533 branch at `a1bf59c5` before this new tranche; Lean PR #113 still `5b22b8f8`. Original `RiemannProjectiveQuarticFourWindowSignedPoleFourierMass.lean` proves `integral signedOrdinateTest = 128*pi*OriginDet/(t*R*M0)` and `fullMuIntegral = centerDensityMode+fullMuVariation`; original `...FourthOrderQuotient.lean` proves both `integral q^2*C_W(q) = -2*pi*P_W''(0)` and `globalCubicModeDefect = 6*pi*(t/16)*P_W''(0)`. Upstream original [Anthropic Zeta23 GammaFacts](https://github.com/anthropics/formal-math/blob/main/zeta23/Zeta23/GammaFacts/Complete.lean) establishes even/smooth `mu` and the Stirling field `|mu(x)-log(|x|/(2*pi))/(2*pi)|<=C_gamma/x^2` for |x|>=1; `GammaFacts/Mu.lean` identifies `mu(x)=(Re digamma(1/4+i*x/2)-log pi)/(2*pi)`. Attribution: these are existing producers, not new in this PR.

**128 actual factorization:** `P_W(0)=4*OriginDet/(R*M0)`, whole-line even cosine inversion `integral C_W=2*pi*P_W(0)`, physical pushforward `integral Psi_t=(16/t)*integral C_W`. Hence `128=16*2*4=2^7` is EXACT as a coefficient product, with each factor retaining its distinct typed source. Existing `DASHI/Wikimedia/IbrahimE7FiftySixAnd128TypedOEISSnowballExact.agda` already licenses `128=2^7` (OEIS A000079) but **denies** same 128 carrier / Spin action from numerical equality. This is a commuting scalar normalization diagram, not a newly constructed 7D physical representation.

**NEW true two-sided ordinate-reflection square (q ↦ −q, NOT horizontal alpha ↦ −alpha):**
Let `r=t/16`, `C_W(q)=integral P_W(v)*cos(qv)dv`, `Psi_t(x)=r^(-2) C_W((x-t)/r)`. The complete original Gamma variation is EXACTLY
```
V_W(t) = (8/t) * integral_R C_W(q) *
   [mu(t+t*q/16)+mu(t-t*q/16)-2*mu(t)] dq.
```
Use `C_W(-q)=C_W(q)` and ordinary absolutely integrable change of variables. This kills the *linear* Taylor mode of `mu` exactly, without claiming a sign for the signed `C_W`. All real `q` and the zero ordinate remain; do NOT truncate in the identity.

**NEW original central quantitative Gamma estimate.** At `t>=200`, choose a declared *analysis cutoff* `|q|<=8` (not a canonical source cutoff). The two shifted ordinates satisfy `t/2<=t(1±q/16)<=3t/2`. From the already-proved Zeta23 `GammaFacts.stirling`, for `V_core=(8/t) ∫_|q|<=8 C_W(q)*Delta2_mu(t,q)`,
```
|V_core - (4/(pi*t))*integral_|q|<=8 C_W(q)*log(1-q^2/256) dq|
  <= (80*C_gamma/t^3)*M0_core,  M0_core=integral_|q|<=8 |C_W(q)|dq.
```
This is uniform in the algebraic scalar Gamma error constant but NOT numerically uniform in the t-dependent selected W's profile norm.

**NEW cubic owner and explicit q-tail weld:** define
`M2_tail=∫_|q|>8 q^2*C_W(q)dq`,
`M4_core=∫_|q|<=8 q^4*|C_W(q)|dq`,
`V_tail=(8/t)∫_|q|>8 C_W(q)*Delta2_mu(t,q)dq`.
For `z=q^2/256<=1/4`, `|log(1-z)+z|<=2*z^2/3`; the already-proved Fourier moment gives
```
V_W(t)= globalCubicModeDefect(W)/(12*pi*t^2)
       + M2_tail/(64*pi*t) + V_tail + E_core
|E_core| <= M4_core/(24576*pi*t) + 80*C_gamma*M0_core/t^3.
```
Here `P_W''(0)/(32*t) = globalCubicModeDefect/(12*pi*t^2)` is a genuine SAME-object existing-Lean determinant, and neither M2_tail nor V_tail has been dropped. For any integer n>=3, integration by parts gives `|C_W(q)|<=||P_W^(n)||_1/|q|^n`; with n=6, `|M2_tail|<=||P_W^(6)||_1/768`. This bound is conditional on an actual selected-W derivative norm, not a scalar theorem uniform across all W.

**Correct terminal firewall:** the coefficient, Gamma mode and cubic recut do NOT imply `2D_t+S_W<4d_W(rho)`; existing source `D_t>=2d_W(rho)`, `S_W>=0` still reverses that inequality for a hypothetical off-line rho. A useful independent producer must pay `V_tail`, `M2_tail`, selected-W `M0/M4/||P^(6)||` controls and a truly new signed zero/archimedean comparison against the strict terminal. Fixed-W t→∞ Gamma convergence is not uniform for W(t) without those bounds. q sign reversals outside |q|<=8 prohibit full-line sign promotion.

**Local checks:** `scripts/check_rh_128_gamma_bilateral_20261123.py` — original-factor algebra, even bilateral reflection, exact 256 log expansion, error constants, cubic determinant and nontrivial outer-tail negative controls PASS; actual upstream `digamma` evaluated at q=2,8,12,20,24,32 over t=200,2000,20000 and converged as expected. Independent local equivalent executed; new repo script committed and read back separately. No full Lean/Agda kernel/CI, and no RH/GRH conclusion.

---
## 23 November 2026 — P0 completed-contour SAME-HEIGHT NORMALIZATION CORRECTION (source-first)

**Checked latest owners:** `dashi_lean4/main` `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleCutset.lean` (`combinedCluster_eq_tsum`, `combined_reflect_eq`, `targetPair_sum_eq_two`, `two_target_le_combinedCluster`, `combinedCluster_eq_offGamma`); `...JointHorizontalJet.lean` (`signedLiteralPairSourceTerm_eq_normalizedPairKernel` ONLY on `((SameOrd t)ᶜ : Set Zeros)`, `signedNormalizedPairKernel_zero_eq_neg_four_target`, `signedNormalizedPairKernel_eq_combinedIntegral`); `...NMu.lean` (`signedNMuPair_eq_pointwise_closed`, `quarticFour_external_eq_half_NMu_add_horizontal`, `completedSignedResidual_eq_combinedCluster`); `...FourierMass.lean` (`fullMuIntegral_eq_centerDensity_add_variation`, `centerDensityMode_eq_originDet`); `...FourierTerminal.lean` (`postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack`); and `Synthesis/RiemannMarkedArithmeticCompletedOperatorAudit.lean` (`unmarkedCompletedArithmetic_eq_gamma`, `selectedPointwiseMultipliers_prime_eq_zero`). Reuse existing exact owners and retain no-kernel-claim.

**CRITICAL geometry fix.** Let r=t/16, D_t = sum over ORIGINAL `SameOrd t` of `W.combinedZeroHeightDefect`, H_t = original UNHALVED `signedLiteralPairSourceTerm` sum on `(SameOrd t)ᶜ`, I_t = integral `W.signedOrdinateTest * Zeta23.mu`. The original source gives `W.combinedCluster=D_t=(H_t-I_t)/2`. Its pointwise *off-ordinate* kernel is `mult/r² K_W(alpha,q)`, while the analytic extension to q=0 is `mult/r² K_W(alpha,0)=-4 W.combinedZeroHeightDefect`. Thus the **full holomorphically extended** zero sum A_ext, if the usual absolutely convergent symmetric exhaustion is used, is A_ext=H_t-4D_t and **A_ext-I_t=-2D_t**. This is a derived rearrangement of the original SAME-W explicit formula, NOT an additional archimedean estimate or an independently established completed `sampleTest` identity. In particular, it is WRONG to infer A_ext=I_t by inserting an abstract Weil formula without the actual `sampleTest`, `paperFT`, `evenResp`, projective radius and SameOrd corrections. The contour is a representation of the *extended off-ordinate kernel*, not automatically the actual completed physical trace. Recovering FarExact still requires subtracting original local, same-ordinate and finite-contour endpoint terms.

**Exact Gamma and pole accounting, not an asymptotic surrogate:** for the ORIGINAL unmarked W at t>=200, the actual primeProjectiveDefect vanishes for both endpoints even after arbitrary pointwise multipliers; the combined poleProjectiveDefect also cancels. By `gammaProjectiveDefect_eq_two_projectiveRvMMuSignedPair`, `quarticFourRvMMuSignedPair_eq_neg_quarter_ordinate_mu` and endpoint linearity, signed Gamma contribution = -I_t/2. Further
`I_t = (128*pi*Zeta23.mu(t)/(t*W.R*unitBumpMass0))*quarticFourSmoothFinitePoleCancelledOrigin(W) + W.fullMuVariation`.
The `fullMuVariation` term is exact and remains SIGNED/UNBOUNDED by this algebra. A new positive prime-jet cannot be substituted for the physically zero original prime channel.

**FULL terminal no-go without genuinely new information.** The correct post-sixth target `H_t+S_W < 4*d_W(rho)+I_t` is equivalent to `2D_t+S_W<4*d_W(rho)`. For an actual off-line target and its distinct same-ordinate reflected partner, source `two_target_le_combinedCluster` gives `D_t>=2*d_W(rho)>0`, and `canonicalLocalBudgetSlack_nonneg` gives `S_W>=0` under its original hypotheses. Thus the desired strict inequality contradicts the source **only if independently established**; the contour+Gamma rewriting gives exactly the lower bound, not that needed upper bound. Using the full extended contour it is `A_ext-I_t+S_W<4d-4D_t`, and `A_ext-I_t=-2D_t` makes the gap `2D_t+S_W-4d>=0`. This is an exact sign/normalization firewall, NOT an RH proof.

**User-requested geometric donor classification:** `16=2^4` is a legitimate four-bit/four-direction cardinality, but the selected `r=t/16` is a **physical source normalization**, not automatically the 16-site YM face or 4-window cardinality without a map. `pi+1` enters the actual support `pi+R<pi+1`; source `JPlusOneScaleBridge` distinguishes typed successor `10+1`, McKay `196883+1`, and refinement; these are not equal to numerical `pi+1`. `2/5` is a safe rational ceiling strictly between the t=200 support and log 2, not the `5dot2` ten-state carrier: `NonaryCompletionPhaseQuotientExact` owns the 5 x 2 -> (9+1) quotient with one glued neutral boundary. `3^(1+12)` is the Monster 3B extraspecial kernel size, **not** `3^12+1`; `TernaryThirteenFibreSplitExact` separately owns a literal 12+1 trit split. Preserve all as distinct typed carriers.

**Genuine quartic commuting square:** endpoint combination S(K_half,K_two)=pTwo*K_half-pHalf*K_two commutes with horizontal mirror R:alpha->-alpha, because each original cosh kernel is even, and S commutes with the Fourier/cosh integral by linearity. This is a 2D exact source square; it does NOT certify the six H05 faces, a Monster representation, or physical C4 time action.

**SSP/FRACTRAN/Monster reuse:** `SignedSSPFRACTRANWeaveExact` owns 15 SSP prime lanes and signed valuations; `Monster369SignedSSPTauInversionSeamExact` owns true negation/Fricke product but forbids unproved same-action identity. They can preserve direction, phase, valuation history and character provenance in a FUTURE GRH coefficient test. They cannot change zero prime-power samples for the short selected detector. Monster/Ogg's 15 primes are not the all-primes/all-Dirichlet-characters quantifier. Any prime-active alternate detector must explicitly change support past log 2, and pay a NEW same-object projection and strict signed estimate; not a silent substitution into this P0 proof.

**Local SymPy 1.14 source-equivalent independent run:** PASS exact `A_ext-I=-2D` derivation, complete gap `2D+S-4d`, reflected target lower bound, genuine endpoint/mirror square, cutoff `16(pi+1)/200<2/5<log2`, and typed 5x2/J+1/3^(1+12) negative controls. No Lean/Agda kernel, no CI, no physical RH/GRH proof, and no uniform signed theorem.

---
## 23 November 2026 — P0 continuation: prime-free right contour and an exact adverse same-ordinate subtraction

**Original source owners verified on chboishabba/dashi_lean4 main.** NMu.lean already owns quarticFourCompletedRadius(t)=16(pi+1)/t, quarticFourPhysicalDetector_support_completedRadius and the literal N-mu normalization. JointHorizontalJet.lean already owns signedLiteralPairSourceTerm_eq_normalizedPairKernel, signedNormalizedPairKernel_eq_combinedIntegral, and (critically) signedNormalizedPairKernel_zero_eq_neg_four_target. SignedPolePair.lean already owns physicalCombinedHeightDefect_scaled and combinedZeroHeightDefect with the TRUE zero multiplicity. RiemannProjectiveRvMMuGammaSameObject.lean already owns projectiveRvMMuPair_eq_literalGammaTerm. FourierTerminal.lean owns the exact post-sixth terminal including local-budget slack. Reuse these; do not build a parallel RH geometry.

### A. Prime-power sampling vanishes exactly at t>=200

The original selected signed profile P_W(v) has support |v|<=pi+W.R<pi+1, while its physical g_W,t has support |u|<=16(pi+1)/t. For every t>=200 and n>=2,

    16(pi+1)/t <=16(pi+1)/200 < 2/5 < 1/2 < log(2) <= log(n).

Hence every standard explicit-formula prime-power sample g_W,t(log n) is exactly zero. This also annihilates character-weighted prime-power samples chi(n)*g_W,t(log n) without eliminating the chi-specific conductor and gamma channels.

For the SAME profile and r=t/16, s0=1/2+i t, define
    f_W,t(s)=r^-2 integral_R P_W(v) exp((s-s0)*v/r) dv.
Evenness makes this exactly the previously constructed entire cosh/cosine lift. After a completed-xi functional-equation contour reflection to Re(s)=c>1, the right-line test is f(s)+f(1-s). Fourier inversion produces the zeta'/zeta term

    -(2/r) sum_(n>=2) Lambda(n)/sqrt(n)
           * P_W(r log n) * cos(t log n) = 0  (t>=200).

The 2/r, n^-1/2 and ±t sheets have been checked by a Gaussian Fourier-exponent normalization fixture; the ORIGINAL compact P_W, not that Gaussian, supplies exact support vanishing. This is not yet a kernel-checked right-contour theorem (horizontal boundary, interchange, and conventions must be paid).

Crucially, on Re(s)>1 the completed logarithmic derivative also has

    xi'/xi(s)=zeta'/zeta(s)+1/s+1/(s-1)
               -(1/2)log(pi)+(1/2)digamma(s/2).

Even if all prime samples vanish, the rational pole-removal and Gamma integral remain. The existing Zeta23.mu/Gamma theorem is the right owner, but its actual sampleTest/paperFT normalization and factors cannot be skipped. Do not claim A_W=I_W.

### B. Exact same-ordinate defect = -4 times the original physical zero defect

At an ACTUAL zero sigma with Im(sigma)=t, displacement a=heightOf(sigma), multiplicity m_sigma, and r=t/16, the theorem signedNormalizedPairKernel_zero_eq_neg_four_target gives

    K_W(a/r,0)=-4 D_W(a/r).

Combining it with physicalCombinedHeightDefect_scaled and the TRUE combinedZeroHeightDefect definition yields

    (m_sigma/r^2) K_W(a/r,0)
      = -4 W.combinedZeroHeightDefect(sigma).

Let D_same(t)=sum_{Im(sigma)=t} W.combinedZeroHeightDefect(sigma) across ALL actual same-ordinate zero events (fixed critical-axis zeros once). Define A_W(t) as the FULL reflected completed-xi contour zero sum with this original normalization, H_W(t) the original literal OFF-ORDINATE signed sum, and I_W(t)=integral W.signedOrdinateTest(tau)*Zeta23.mu(tau) d tau. Exact subtraction gives

    J_same(t) = -4 D_same(t),
    A_W(t) = H_W(t) + J_same(t),
    **H_W(t) = A_W(t) + 4 D_same(t)**.

The sign is important: removing same-ordinate poles makes the off-ordinate residual HIGHER, not lower. This was obscured by the previous generic local-subtraction wording.

### C. The full post-sixth terminal becomes a stricter NEGATIVE contour margin

Keep canonical local-budget slack S_W>=0 and target defect d_W(rho)>0 for a hypothetical off-line zero rho at the same ordinate. The already-verified exact terminal is

    H_W(t)+S_W(t)<4 d_W(rho)+I_W(t).

Substitute the exact same-ordinate correction:

    **A_W(t)-I_W(t)+S_W(t) < 4 d_W(rho)-4 D_same(t)**.

Under the ORIGINAL quantitative target-band assumption 8/t<W.quantitativeTargetRadius, every zero defect is nonnegative. The off-line rho and its distinct same-ordinate horizontal reflection have equal multiplicities and equal positive defects, so D_same(t)>=2 d_W(rho). Thus a necessary condition is

    **A_W(t)-I_W(t)+S_W(t)<-4 d_W(rho)<0**.

This is a genuine signed no-shortcut result. Prime-free source sampling by itself cannot supply the required strict negative surplus. Even a hypothetical later A_W-I_W=0 would be incompatible with this strict inequality for an off-line target, but that equality is NOT established by the support check; Gamma and pole-removal remain to be identified exactly with original mu.

### D. Max-cut next: one same-object archimedean scalar, not another reflection model

(1) Kernel-check the FULL contour/Abel exhaustion with correct horizontal edges and original outer 1/2; (2) identify its rational and Gamma term with the original projective sampleTest, paperFT and Zeta23.mu pairing, not a surrogate log-density; (3) prove or refute the required A_W-I_W+S_W<-4d_W(rho) with actual source and all same-ordinate defects. For GRH retain chi, conjugate chi, conductor, parity, gamma and primitive/imprimitive pole removal, even though the prime sample support argument itself is character-neutral.

Local SymPy 1.14 source-equivalent support inequality, Gaussian Fourier normalization, -4d per zero, -8d per horizontal reflection pair and terminal-recut algebra PASS. Appended to the EXISTING bilateral-pole regression. No local FULL regression, Lean/Agda kernel or CI was run. No RH or GRH proof is claimed.

---

## 23 November 2026 — NEW: original finite far-zero sum as a completed-ξ'/ξ HOLOMORPHIC CONTOUR TRACE (the actual requested two-sided-pole weld)

This reuses the ORIGINAL Lean signed normalized pair kernel and its `signedLiteralPairSourceTerm_eq_normalizedPairKernel` theorem, plus the original completed-ξ/Weil/Abel machinery. It is **NOT a new arbitrary kernel**, and the contour transformation by itself does not make a sign-changing source positive.

For the SAME original selected witness W, put `r=t/16`, `s0=1/2+i t`, and let `P_W(v)=quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t v`. This P_W is **real, even, smooth, compactly supported** by the original Lean source. Define its entire (complex-frequency) cosine transform and the holomorphic s-plane lift:

  C_W(z) = integral_(v∈R) P_W(v)*cos(z*v) dv,
  f_(W,t)(s) = r^(-2) C_W( -i (s-s0)/r )
             = r^(-2) integral P_W(v)*cosh((s-s0)*v/r) dv.

At an ACTUAL zero `rho=1/2+a+i gamma`, `-i(rho-s0)/r=q-i alpha`, where `q=(gamma-t)/r` and `alpha=a/r`. At its SAME CHARACTER/SAME ORDINATE reflected partner `rho#=1-conj(rho)=1/2-a+i gamma`, `z(rho#)=q+i alpha`. Because the source P_W is REAL and EVEN,

  f_(W,t)(rho)+f_(W,t)(rho#)
     = (2/r²) integral P_W(v)*cosh(alpha v)*cos(qv) dv
     = (2/r²)*W.signedNormalizedPairKernel(alpha,q).

For multiplicity m, the RHS is **exactly the sum of BOTH** pre-existing Lean literal original zero-source summands. Critical-line zero a=0 is a reflection FIXED POINT; use its original multiplicity once, never pair it with a copy. Since `f(rho#)=conj(f(rho))`, the sum on any reflection-saturated finite source set is real, and equals the original REAL signed test kernel sum with multiplicities.

Now take a finite rectangle D invariant under `s↦1-conj(s)`, containing the relevant finite original zeta zeros but none on its boundary. The completed function `xi(s)=s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2` is ENTIRE with exactly those nontrivial zeros. By the genuine residue theorem,

  (1/(2*pi*i)) * contour_∂D [ f_(W,t)(s) * xi'(s)/xi(s) ] ds
    = sum_(rho∈Zeros(xi)∩D) mult(rho)*f_(W,t)(rho)
    = sum_(rho∈Zeros(xi)∩D) mult(rho)/r²
        *W.signedNormalizedPairKernel(a_rho/r, q_rho).

For the finite symmetric rectangle, this is an **exact full zero-side source identity**. The original source `FarExact` is a HARD CUT `|q|>eta` and excludes the `SameOrd t` zero guard: the indicator is NOT holomorphic. To recover FarExact from the contour, one must subtract the original `|q|<=eta` local zero terms, including the same-ordinate zeros and original endpoint conventions; similarly for a finite zero exhaustion, preserve explicit rectangle-endpoint atoms. **Do not place a discontinuous Far indicator inside the contour integral.**

The user-requested RH route is now a precise SAME-W commuting square:

  ACTUAL completed ξ zeros with retained ±a, multiplicity and γ
       → (old) literal original signed K zero sum,
       ↘ via residue theorem                              ↗ via original W kernel,
        contour ∮ f_(W,t)(s) [ξ'/ξ](s) ds.

The WHOLE contour (not Far alone) can be deformed to vertical lines `Re(s)=1+epsilon` and `Re(s)=-epsilon`, using `ξ(s)=ξ(1-s)` to relate sides, and on the right `ζ'/ζ=-sum Λ(n)n^-s` where Re(s)>1. Its gamma, pole-removal and normalization terms produce the ORIGINAL `mu`/prime source. This is a route for using BOTH pole sides against the actual far signed integral and existing original `RiemannZetaMuExactAbel` / `FourierMass` machinery. But proving a UNIFORM HEIGHT bound on the deformed vertical and horizontal contour pieces, including local subtraction, positive/negative far-band cancellation, and strict post-sixth margin remains the exact open P0 inequality. The contour identity is standard residue theory specialized to the original W, not a new proof of positivity or RH.

**Executed exact SymPy receipt:** original atomic `F(z)=-(320/351)sin(pi z/4)^4` at a finite rational quadruple (`gamma=7,t=6,r=5,a=1/3`) reproduces the original two-sided value `F(q±i alpha)/r²`; a rational polynomial analytic f on a 4-zero reflected `Q(s)` satisfies all FOUR *actual meromorphic residues*
  `Res_(s=rho) f(s)*Q'(s)/Q(s)=f(rho)`.
Local source-equivalent script `/mnt/data/rh_bilateral_logpoles_complex_notch_sympy_20261123.py` executed PASS; committed source `scripts/check_rh_bilateral_completed_xi_logpoles_20261123.py` extended in commit `7d84996e`. No infinite contour estimate or kernel acceptance claimed.

---

# RH P0 / GRH — completed-log-pole bilateral reflection, mediating zero and exact signed adverse-phase sharpening (23 November 2026)

**Source ownership, no duplicates.** Reuse Lean `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth.lean` (already proves original even 0/2/4 target/reflection reconstruction), `...SignedPoleJointHorizontalJet.lean` (already identifies literal per-actual-zero source with the normalized signed pair kernel), `...SignedPoleNMu.lean` (already carries outer 1/2 literal off-ordinate t-sum), `...SignedPoleLocalRemainderBounds.lean` (already defines literal fourth favorable/adverse phase masses and a 3/2-per-multiplicity envelope), `...SignedPoleConeDecomposition.lean` (original local cone delta²<=6a²), `...SignedPoleV4EndpointAbsorb.lean`, `...SignedPoleFourierTerminal.lean` (original outstanding strict terminal). No changes to original physical witness or imported Lean source. Portable source-specific SymPy regression `scripts/check_rh_bilateral_completed_xi_logpoles_20261123.py`, local expanded `/mnt/data/rh_bilateral_logpoles_complex_notch_sympy_20261123.py` both derived from the exact source formulae. Local SymPy 1.14 checks PASS. No Lean/Agda kernel or CI claim.

## I. Correct meaning of both sides as poles — ξ'/ξ, not ξ

Let `xi(s)=s(s-1)*pi^(-s/2)*Gamma(s/2)*zeta(s)/2` be the usual entire completed zeta. Its nontrivial zeros rho_±=1/2±a+iγ, a>0, have the SAME multiplicity m by the functional equation and conjugation. In the logarithmic derivative of xi, these zeros are poles of residue m. With w=s-(1/2+iγ), the finite matched pair contributes exactly

  m/(w-a)+m/(w+a) = 2m w/(w²-a²).

That is a two-pole object with a **mediating zero at w=0**: this is only a zero of the PAIR CONTRIBUTION to xi'/xi, not a zero of xi, zeta, or the full xi'/xi. At a=0 the orbit is FIXED under horizontal reflection and must count one original critical-line zero with its original multiplicity, not an artificial double pole. The formal comparison with an on-line DOUBLE pole is explicitly only a counterfactual algebraic reference:

  2m*w/(w²-a²) - 2m/w = 2m*a²/[w(w²-a²)].

The difference is an honest squared-separation residual a²; it vanishes as a→0 at fixed w≠0, but the pole multiplicity at a=0 is not inferred by continuity. The whole conjugation/functional-equation quartet has factor
  Q(u)=[(u-iγ)²-a²][(u+iγ)²-a²]
      =(u²-γ²-a²)²+4u²γ², u=s-1/2.
At u=iy this is `[(y-γ)²+a²][(y+γ)²+a²]>0` for a>0. Its evenness implies `Q'(0)=0`, even when it has off-critical zeros. **Counterexample to symmetry-alone RH:** Q is an entire, real-conjugate, critical-reflection-even polynomial with four off-critical zeros and all these geometric properties. Euler product, prime side and exact zeta argument remain indispensable.

## II. Exact transform commuting square — reuse original cosh marker

For Re(w)>|a|, the paired meromorphic resolvent has the Laplace identity

  2w/(w²-a²) = integral_0^∞ 2 e^(-wu) cosh(a u) du.

This is a resolvent/Laplace equality, not equality of this noncompact Laplace integral with the existing compact four-window test.

The ORIGINAL signed normalized RH pair has exactly a compactly supported even profile P_W(v) and `alpha=a/(t/16)`, `q=(γ-t)/(t/16)`. Its source-established normalized kernel equals

  K_W(alpha,q)=∫ P_W(v) cosh(alpha v) cos(qv) dv.

For its ENTIRE complex cosine transform `C_W(z)=∫P_W(v)cos(zv)dv`, exact algebra gives the commuting square

  K_W(alpha,q) = [C_W(q+i alpha)+C_W(q-i alpha)]/2.

Hence the target/reflection average is an actual complex-frequency pullback on the SAME original four-window profile. The physical zero pair at ±a yields the SAME K by evenness of cosh, and the existing literal zero sum already counts both members. Do not insert an extra factor two; the original `offOrdProjectiveDefect_eq_half_literalPair_tsum` already has an outer 1/2, while `literalFarExactAt` is the unhalved finite source sum.

Source norm scaling matters: the resolvent Laplace has unscaled a,w, whereas Fourier observation has alpha=a/r, q=(γ-t)/r, r=t/16. Only after this explicit rescaling is the common cosh multiplier the same geometric operation.

## III. Original local A2 adverse quartic: an exact THREEFOLD improvement to a consumed source estimate

The ORIGINAL physical fourth phase of an actual zeta zero, with `a=Re rho-1/2` and `delta=Im rho-t`, is

  P4(a,delta)=Re(a+i delta)^4=a^4-6a²delta²+delta^4
             =(delta²-3a²)²-8a^4.

The exact completed-square identity gives the new **signed residual-weighted inequality** for EVERY original zero:

  max(-P4(a,delta),0) <=8a^4 <=1/2, since |a|<=1/2.

The bound is sharp as a **strip-wide algebraic envelope** at |a|=1/2 and |delta|=sqrt(3)/2 (not a claim that zeta has a boundary zero). This is strictly stronger than existing Lean `QuarticFourSignedPolePair.literalLocalFourthAdverseMassAt_le_three_halves_mul_multiplicity` (3/2 per unit multiplicity). On the SAME original finite `centeredZeroFinset` and unchanged literal off-ordinate/multiplicity guards,

  Original AdverseMass(t,eta,n)
  <= 8 * Σ_[local adverse zero rho] mult(rho)*heightOf(rho)^4
  <= (1/2)*AdverseMultiplicity(t,eta,n)
  <= (1/2)*N(t-3/2,t+3/2).

This consumes the existing exact `literalLocalFourthAdverseMultiplicityAt_le_fixedWindowN`, leaving the source count convention and right/left endpoint atoms untouched. Existing original zero-count bound `N(t-3/2,t+3/2)<=3 A0 log(t+5)` therefore yields the direct refined conditional-on-source-weld certificate:

  AdverseMass <= (3/2) A0 log(t+5),

rather than the already-owned `(9/2) A0 log(t+5)`. This is a factor THREE improvement in this **specific subsidiary local adverse-phase ledger**, not a proof of its being the unique controlling A2 debt nor a declaration that RH closes.

The same polynomial provides a sharper geometrically exact *adverse sector*:

  P4<0 iff a≠0 and (sqrt(2)-1)|a|<|delta|<(sqrt(2)+1)|a|.

At every actual zeta zero |a|<=1/2, this implies `|gamma-t|<(1+sqrt(2))/2≈1.20711`, strictly narrower than the currently used ±3/2 window. The original local cone `delta²<=6a²` includes positive AND negative P4 regions; it is a classification cut, not the optimal sign sector. A NEW length-sensitive RvM count bound on the narrower window could sharpen still further, but must be proved in the same source; cannot infer a better logarithmic constant merely from interval inclusion.

This is directly in the user's balanced-ternary/residual sense: the zero mediator is retained, the two pole signs are not flattened, and the adverse magnitude retains the original a^4 physical horizontal residual instead of collapsing immediately to a binary adverse-bit count.

## IV. Complex 4-branch notch geometry, and a HARD physical scale separation

The atomic original RH source has entire complex frequency extension

  F(z)=-(320/351)sin(pi z/4)^4.

At the notch z=4+i alpha, its exact symmetric-pole evaluation is

  [F(4+i alpha)+F(4-i alpha)]/2
   =-(320/351)sinh(pi alpha/4)^4 <=0.

Original fixed even compact bump with second moment m2∈[1/24,1] gives at high pole and small R, q=4+sqrt(R)*x, leading real/complex jet

  K_R(q)/R² = 60m2/13 -(5pi⁴/1404)x^4 +O(sqrtR).

The quartic has FOUR simple complex roots `x=(6/pi)m2^(1/4)*{+1,-1,+i,-i}`. By analytic perturbation of the original compact-bump Fourier profile and the original J2-selected branch, they yield two real and two imaginary-leading complex-frequency TEST-root branches asymptotically as R→0. The preceding fixed R=10^-10 source certificate rigorously supplies TWO real roots, NOT a fixed-R numerical interval certificate for the complex roots.

**Scale obstruction:** at R=10^-10, the imaginary-leading roots have |Im(q-4)| asymptotic coefficient at least `(28/33)*10^-5` (the lower 28/33 follows from π<22/7 and 24^(1/4)<9/4). But an actual zeta zero has |a|<=1/2 and t>=10^14, so `|alpha|=16|a|/t<=8*10^-14`. The leading complex notch scale is **over 100 million times greater** than the physical horizontal strip. This is an asymptotic leading-scale nonalignment, NOT a rigorous no-overlap for the particular finite-R complex roots without an explicit complex neighbourhood bound.

In the same actual far q4 band, |q|>39/10 implies |delta|=t|q|/16>39t/160. For the paired RESOLVENT on the critical axis, the correction relative to the double-axis reference obeys

  |polar residual|/|2m/(i delta)| = a²/(delta²+a²)
    <= 64/(q²*t²)<5/t²<=5*10^-28.

Thus merely reflecting both poles cannot repair the globally mixed sign of the actual far q4 weighted source; the original K already depends on cosh(alpha v), which is even in a, and its two real q bands have O(R²) opposite signed contributions. No unsourced positivity theorem arises from pole symmetry.

## V. Character-indexed GRH commuting square: retain χ, conjugate χ, sign and height

For a primitive Dirichlet character χ, the completed Dirichlet L-source satisfies

  Λ(s,χ)=epsilon(χ) Λ(1-s,conjχ),
  overline[Λ(s,χ)]=Λ(conj(s),conjχ),

up to the usual nonzero root-number normalization. On zero events tagged with their original character, define C:(χ,ρ)↦(conjχ,conjρ), F:(χ,ρ)↦(conjχ,1-ρ). The source-symmetry commuting square is

  C²=F²=id, C∘F=F∘C,
  (F∘C)(χ,ρ)=(χ,1-conjρ).

For non-real χ, its negative-ordinate partner belongs to the **conjugate-character sheet**, while its horizontal mirrored same-ordinate partner belongs to χ. For real χ the two character sheets identify, but their zero events and multiplicities do not get deleted. Primitive principal / zeta completed normalization must be chosen with pole removal so poles of the completed LOG derivative correspond to zeros of the chosen entire completed function.

This establishes a valid **GRH labelled geometric symmetry square**, not an all-character positive-prime, completed μ or quantitative A2/FarExact estimate; χ-dependent conductors, root numbers, gamma factors and prime sums are not supplied by the zeta witness.

## Remaining actual RH min-cut

Lean `SignedPoleFourierTerminal` still requires the SAME-W strict `LiteralFarMinusMuUniformHighEstimate` / `CompletedResidualWithLocalSlackUniformHighEstimate` with full signed literal far sum, original μ centre-density and variation, bad zero multiplicities, post-sixth signed sixth/eighth and original prime channel. Reflection pair DOES NOT imply the sign: actual q4 positive and negative bands each occur at symmetric horizontal a and have the SAME sign for ±a. The new local adverse-mass upper bound is mathematically exact and lowers a real bound in the existing ledger, but must be threaded into whichever strict physical A2 consumer it actually improves. No RH, GRH or zero-exclusion theorem is claimed. Exact source SymPy PASS; Agda/Lean kernels deferred at user direction.
