## 22 November 2026 — P0 priority correction after merged Lean A2 source audit

**Do not rebuild a localized M0/M2/M4 producer as the first A2 task.** The merged [Lean PR #22](https://github.com/chboishabba/dashi_lean4/pull/22) is available on `main`. Original source owners re-read:
`Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth.lean` (exact same-object zero-minus-mu BIDI moment operator),
`...SignedPoleRvMFourth.lean` (existing actual ordinate-only V4 Abel/RvM discrepancy estimate),
`...SignedPoleV4EndpointAbsorb.lean` (closed local interval versus half-open RvM interval, including the possible LEFT-ENDPOINT ZERO ATOM, not silently dropped),
`...SignedPolePostSixthAbsorb.lean` (complete quartic, signed sixth, eighth debt, signed literal FarExact),
and `...SignedPoleA2ScalarAudit.lean` (exact strict scalar).

The EXACT remaining A2 scalar equivalence, no abs(FarExact), is:

`postSixthTerminalLocalPositiveDebt(EV) + literalFarExactAt(eta0,n) < compensationTargetThreshold(rho) + postSixthTerminalLocalMuGain`,

with `eta0=1/(pi+1)`, `r=eta0*t/16`, and actual expanded multiplicity count `NZ=N(t-r-1,t+r)`. Its source local positive debt includes (1) `S/(6(t/16)^6)*(EV+(3/2)r²NZ)`, (2) signed M6 cap `(3pi^6/20)*sixthEnvelope*NZ/(720(t/16)^8)`, (3) G1-fourth-Lipschitz eighth envelope `(pi+1)^2*W.fourthLipschitz*eighthEnvelope*NZ/(t/16)^10`. Its favorable mu gain is `S/(6(t/16)^6)*(2/5)r^5*muLower(t-r)`; source proves `muGain>0` and dominant selected M6 coefficient paid for t>=200. **Only a TRUE strict overall comparison including signed FarExact and compensation remains unpaid**.

The new reflected-cloud M0/M2 no-go `93198e65` is a source-geometry test forbidding count-only fourth-sign promotion, NOT a counterexample to this RvM-using A2 theorem. The A2 front can employ already-paid V4/H4 and sixth/eighth bounds directly; a separate stronger localized marked-pair estimate is an optional alternative only if it improves this exact scalar. Preserve the original left atom, SameOrd exclusion, actual Zeros multiplicities, signed far, and local slack. Do not switch to q=4 synthetic positivity as a proof of a universal signed zero sum. Indexed cube remains 8 vertices/12 maps/6 faces with proof-relevant history/sign/zero semantics.

**Next research action:** audit the source magnitude/sign of the one A2 inequality, especially NZ, eighth debt and signed FarExact versus the actual compensation threshold and smooth mu gain; derive a source-backed strict inequality or a rigorous asymptotic no-go, not another scalar wrapper. Actual `H_n+E_n+S_W<T_W(rho)` and RH/GRH remain open; no Lean/Agda kernel receipt from this work.

---

## 22 November 2026 — P0 ACTUAL zero-marked fourth max-cut (source owner already paid)

Source-first audit of Lean main `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth.lean` and Agda `DASHI/Analysis/RiemannQuarticSignedPoleBidiMarkedFourthExact.agda`: original `literalLocalCenteredFourthAngularAt_eq_bidi_discrepancy` is an EXACT source-owned local zero-minus-`Zeta23.mu` 0/2/4 BIDI identity. The zero sum uses the real `centeredZeroFinset`, actual multiplicity and `SameOrd t` exclusion. `localizedBidiMarkedProducer_exact` is only a trivial packaging of the already-defined three moments; it is NOT the missing one-centre analytic marked-pair theorem. The specific short-support cosh-marked literal prime channel is already recorded source-paid as zero. The remaining full signed response/archimedean and far/slack payment is not thereby proved.

New local SymPy regression `scripts/check_rh_marked_fourth_reflected_cloud_obstruction_20261122.py` (commit `93198e65`) constructs two strictly off-ordinate **synthetic** reflection-complete clouds (no actual ζ-zero claim). Both have identical positive integer mass `M0=4`, vertical `M2=100h²` and marked `M2=-100h²`. Source `D_A=1/2 M4 -3 A² M2 +5 A⁴ M0` yields opposite local *zero* fourth-angular signs: `-4375h⁴/4` versus `+4841h⁴/4`, with exact marked M4 difference `4608h⁴`. This improves the previous unreflected M0/M2 negative controls: reflection, positivity, local support, and SameOrd exclusion still cannot certify the required fourth-moment sign. A shared smooth `mu` background preserves the difference but may shift BOTH centred signs.

Sharp local positive-measure cone: for `V0>0`, `|δ|<=L`, `V2²/V0<=V4<=L²V2`. In a constant-|a|=A subfamily, fourth-angular sum lies in `[V2²/V0-6A²V2+A⁴V0, L²V2-6A²V2+A⁴V0]`; this band crosses zero on the two clouds. For full physical strip `|a|<=1/2`, `-8L²V2<=Σ mult*P4<=L²V2+V0/16` is a universal bound, but not a strict RH payment.

**Exact new execution target (not more low-moment algebra)**: derive the genuine ACTUAL-zero localized marked fourth correction `ΔM4` relative to original `ΔM0,ΔM2` and `Zeta23.mu`. If the required local lower angular charge is `D_A(Δ)>B`, the exact reverse target is `ΔM4 > 2B+6A²ΔM2-10A⁴ΔM0` (inequality reversed for an upper charge). Couple the actual finite zero source to the merged Lean #22 A2 strict scalar `localPositiveDebt+signed FarExact < compensationTargetThreshold+localMuGain`, keeping full sign/multiplicity and local slack. A2 remains OPEN, as does `H_n+E_n+S_W<T_W(rho)`. No RH/GRH or Lean/Agda kernel claim.

**Geometry/attribution**: preserve eight vertices, twelve maps, six faces with reflection/smoothing/pole axes, time/history/refinement/Frobenius/consumer, balanced ternary sign, actual-Zeros target vs excluded off-ordinate distinction, full far source and separate scalar-zero/exponent-zero-C3/Fourier-zero semantics. This is a finite **nonpromotion test** and mathematical moment cone; it is not an analytic commuting-cube theorem or a zero distribution theorem. Full details and exact provenance in `Docs/proofs/RHR2G3AgdaBIDIReverseExactRemainingLemmas20261122.md`, ledger commit `14b2ca29`.

---

## 22 November 2026 — P0 concrete original-bump q=4 witness, still NOT the RH signed terminal

**New original-source quantitative result**, source-written on
[PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533):
`scripts/check_rh_original_bump_explicit_radius_20261122.py`,
and full proof ledger in
`Docs/proofs/RHR2G3AgdaBIDIReverseExactRemainingLemmas20261122.md`.

Mathlib `ContDiffBump.neg`, `ContDiffBump.le_one`,
`ContDiffBump.one_of_mem_closedBall` plus original Lean
`RiemannQuantitativeScaledBump` and the original projective
four-window pairing show the **actual fixed unit bump** is even,
bounded by 1, equal to 1 on the inner half-radius and affinely
scaled. This gives `E[Z²]>=1/24`; the original J2 equation
is QUADRATIC in smooth mu, so source-selected endpoint roots
are explicitly bracketed around the original atomic roots:
`|mu_exact-(mu0+mu1*eps)|<=600R^4`
with the strict J2 derivative >=10 in the small-radius regime.
The original corridor and `J4<-1/4` survive at R=10^-10.

At the explicitly selected `R=10^-10` the computed rational
majorant is `C=22848813692672` multiplying R4.
Therefore the exact original high-pole `q=4` smooth margin
`kappa_R>R²/6`, and via original uniform source transfer,
`t>=10^14, |a|<=1/2 ==> K_t(a,4;R)>11R²/300>0`.
These are mathematical source bounds checked with local SymPy,
NOT Lean/Agda kernel-certified (and no CI).

**Negative control / strict scope:** atomic high-pole
`K_inf(0,q=1)=-80/351<0`, so **the original source remains
sign-changing in normalized q**. q4 corresponds to moving
physical ordinate gamma=5t/4, not an actual-zero population
or universal sign. This fixes the earlier P0 ledger's statement
that the original smooth selected W was entirely unquantified:
a local single-q margin is now quantified, while a universal
actual-zero signed/W prime compensation theorem remains open.

**Geometry preserved:** an 8-vertex/12-directed-map/6-face
indexed cube with reflection/smoothing/pole axes is a bookkeeping
and non-promotion carrier. Keep ordered history/time/refinement,
Frobenius and consumer indices, balanced ternary sign, multiplicity,
and distinctions among zero scalar, unit C3 phase, nonempty
cancelled phase orbit, Fourier observed zero, and actual ζ-zero.
No six-face analytic transport is inferred from symbolic parity.

**Next nonduplicate P0:** original actual-zero localized
M0/M2/M4 marked-pair estimate and prime-side sign/coupling;
control all real q, actual ordinates/multiplicities, signed
near/far and local slack; pay the exact terminal
`H_n+E_n+S_W<T_W(rho)` (still OPEN). Avoid further
single-q Taylor work unless it actually supplies that payment.

---

## 22 November 2026 — exact selected atomic sign bifurcation and BIDI marked-fourth cut

**New local SymPy result committed, WITHOUT promotion to actual selected W or actual ζ zero distribution.** The original selected four-window *atomic* response, formed with `μ_0(λ)=(13λ−8)/(144−54λ)`, `λ=1/2,2/3` and original high-`t` pole coefficients `P∞(λ)=3(2−λ)/4`, obeys for **every real q**
```text
K∞(0,q)=−(80/351)*(1−cos(πq/2))² <= 0.
K∞(α,q)= (160/351)*cos(πq/2)*cosh(πα/2)
         −(40/351)*cos(πq)*cosh(πα)−40/117.
```
For `α!=0`, let `h=cosh(πα/2)>1`; the same exact kernel is **strictly positive** at a q with `cos(πq/2)=h/(2h²−1)`, and **strictly negative** at `q=4k`. Thus the source's *BASE* globally nonpositive square cannot be used as a full horizontal pointwise signed estimate. Horizontal reflection `α↦−α` preserves, not removes, this sign conflict.

Stronger: using the ORIGINAL **finite-`t` atomic pole determinant** (rather than high-`t` pole coefficients), physical `a=β−1/2`, normalized `α=16a/t` and `u=π/t`, exact local SymPy Taylor algebra gives
```text
K_{t,atom}(a,4)=(5120/351)*(1−16a⁴)*u⁴+O(u⁶)
K_{t,atom}(a,1)=−80/351+O(u²).
```
For each **fixed** `|a|<1/2`, this proves opposite signs for sufficiently large t **only in the atomic model**. The original Lean source owner `RiemannProjectiveQuarticFourWindowPoleSameObject.lean` supplies the actual finite pole weight `cosh(8v/t)cos(16v)cos(cv)`. The selected smoothed W remains `R>0` and the actual ζ-zero ordinates are **not** generated by choosing arbitrary q. A fixed-width `O(R)` localization estimate by itself cannot preserve an `O(t^-4)` sign for all unbounded t. Neither atomic sign is a theorem about actual W or actual ζ zeros.

**Existing Agda producer recovered (not missing mathematics):** `DASHI/Analysis/RiemannQuarticSignedPoleBidiMarkedFourthExact.agda` has the exactly owned reflection-centred `P4` decomposition into only **even marked moments M0/M2/M4**. Its `localizedOneCentreMarkedPairProducer`, `markedPairPrimeSideSignOrBound`, `centredFourthAngularBias` and `fourthAngularFarCouplingPaysG3` remain false/open. SymPy confirmed the exact P4 target/reflection identity. Two synthetic vertical lists `[-1,-1,1,1]` and `[-sqrt(2),0,0,sqrt(2)]` have the SAME `M0=4,M2=4` but opposite comparisons to a fourth-moment threshold 6 (`M4=4` versus `M4=8`). These are **not actual ζ zeros**; they prove M0 and M2 alone do not determine the fourth-order signed payment. This is why the already-paid RvM upper count / reflection geometry cannot settle the marked signed terminal.

**Exactly remaining math**, with original attribution:
1. Retain full terminal `H_W+S_W < T_W(ρ)=4d_W(ρ)+I_W` for every hypothetical high off-line actual ζ zero. Alternative literal finite signed certificate `H_n+E_n+S_W<T_W(ρ)` over the ORIGINAL half-open `(t-n,t+n]`, or eventually sharpened signed `B_n^sharp+S_W≤T_W(ρ)−ε`. A loose signed `H_W<T_W` **without local slack** is insufficient.
2. Original positive-width selected W, its true `μ_{½},μ_{⅔}`, actual finite ζ-zero ordinates and multiplicities, and quantitative signed finite source remain **OPEN**. Source Fourier, bounds, exact source cone/good/far partition, and actual RvM count remain reusable.
3. Alternatively source-locate the existing Agda/Lean **marked-fourth** M0/M2/M4 identity, prove the genuinely missing same-target localized actual-zero/prime-side marked-pair bound and couple its actual `μ` background and signed far source. Do NOT rebuild even-moment algebra.
4. External all-character trusted admission and independent Agda literal near+far+Gamma<ClusterResponse are separate avenues, not synonyms for this selected-W inequality.

**Executable original-source test:** `scripts/check_rh_selected_finite_t_atomic_sign_20261122.py`, commits `964db866`/`ed54cef3`, readback blob `af78e6365b55b194bc23d6dd5efb14ad979f580b` **matches exact locally executed Git blob**. SymPy 1.14.0 exact high-`t` all-real-q factorization, full horizontal positive/negative extrema, exact finite-`t` Taylor coefficient cancellation/order, even reflection, 16/16 untruncated high-precision finite-`t` signs, and 0/2/4 marked identity/negative controls **PASS**. High-precision signs aren't rigorous interval certificates. Source-authored math BIDI register updated `Docs/proofs/RHR2G3AgdaBIDIReverseExactRemainingLemmas20261122.md` (commits `ec86352c` / `7b0480f1`). **No** Lean/Agda kernel, CI, actual ζ off-line zero sample or RH/GRH theorem.

---

## 22 November 2026 — FULL post-sixth BIDI min-cut (corrected P0)

**Current theorem target supersedes the weaker G3 completed-residual-only threshold.** Original source `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean` proves
`postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack`,
with `canonicalLocalBudgetSlack_nonneg`. Original `FourierMass`/joint-source gives `completedSignedResidual=(H-I)/2`.
For each actual selected `W`, original nontrivial ζ zero `ρ` at target ordinate `t`, and `EV=quarticSignedPoleCanonicalV4Error CV t`, let
`H=∑'W.signedLiteralPairSourceTerm`,
`I=∫W.signedOrdinateTest·Zeta23.mu`,
`d=W.combinedZeroHeightDefect ρ`,
`S=W.canonicalLocalBudgetSlack EV≥0`,
`T=4d+I`. **The literal complete post-sixth terminal iff `H+S<T`.**
Earlier `UniformSignedCompensationGap ρ` and its existing stronger `UniformSharpenedSignedCompensationGap ρ` as stated only imply **`H<T`**, not necessarily `H+S<T`; `H=3,I=0,d=1,S=2` is an exact counterexample. Never drop `S` at the final endpoint.

**Already-paid improved cone geometry was overlooked.** The existing same-original-zeros `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean` proves `literalConeExactAt_eq_debt_sub_gain`, `literalSharpenedJointBudgetAt_le_jointBudgetAt`, `literalOffOrdExactAt_le_sharpenedJointBudget`, `UniformSharpenedSignedCompensationGap`, and old→sharpened. A negative cone term is **useful signed gain**; replacing it or a negative far term by absolute value loses precisely the candidate compensation. Good-lane absolute remainder can still be slack. Reuse that source, don't reimplement another cone theorem.

**Reverse-solved exact weaker/stronger alternatives (conditional on existing source far-tail inequality):**
- **Direct finite signed certificate**: `H_n=W.literalOffOrdExactAt n` over original **half-open** `(t-n,t+n]` with actual ζ zero multiplicities; if `E_n≥|H-H_n|` and `E_n→0` for `n≥ceil(t+7)`, then
  `H+S<T ⇔ ∃n≥ceil(t+7), H_n+E_n+S<T`.
  Forward uses gap `g=T-H-S>0` and `2E_n<g`; converse `H≤H_n+E_n`. The existing R2 `O(log t/t)` bound is a candidate **absolute** `E_n` using the pre-existing multiplicity-weighted RvM interval theorem and fixed-W symbolic derivative constants. Actual finite signed H_n must be evaluated/estimated on the original zero carrier. For each fixed t, E_n→0 as n→∞; no uniform fixed-n global assertion.
- **Sharpened sufficiency**: if eventually `W.literalSharpenedJointBudgetAt η n + S≤T-ε` with `ε>0`, then the exact cofinal theorem implies `H+S<T`. This is NOT necessary because the sharpened upper budget can exceed the exact finite source (absolute good remainders).
- **Core at fixed W**: `UniformQuarticFourPoleDeterminantCompilerTarget` remains source-written but kernel-UNPAID; previous SymPy radius `δ*=5.53270840772e-7` is mathematical input only. Original `UniformQuarticFourSignedPoleCore` is a conditional compiler; still need target-radius/sixth-moment/case conditions. Source actual ζ RvM/Weil supplies counts, not the signed finite values.

**Agda BIDI comparison was now checked against actual source**: `RiemannG2ClayTerminalBishopLocatedExact` and `RiemannG2UniformLiteralPhaseHighProducerExact` require an analytic **per-high-off-line-zero producer** plus Bishop low same-substrate inputs. The latter needs independent `literalNear+far+Gamma<ClusterResponse` and a **separate final balance attachment**. `RiemannG2ZeroSideHMBypassBidiExact` already compiles `H_X→H_T` and literal selected window→`H_W` without mandatory historical `H_M`; `RiemannG2HASingleSourceProducerBidiExact` already packages `H_A` as one dependent source-native producer. But Agda's literal cluster response is NOT yet proved equal to Lean's selected-W `H+S<T`; separate actual-zero, test/taper, scalar order and quantifier same-object welds would be needed. Avoid declaring this cross-language equivalence via shared terminology.

**Committed audit/acceptance**: exact full source-to-consumer ledger `Docs/proofs/RHR2G3AgdaBIDIReverseExactRemainingLemmas20261122.md` (commit `1ac70327`), Python `scripts/check_rh_bidi_reverse_terminal_20261122.py` (commits `f44d4390`, `3c0f7977`, blob `6eb3222e13d178ccc855f6ae24f1641221bb79d8`). Local SymPy 1.14.0 **108/108 exact terminal substitutions**, cone/good/far negative controls, real original selected atomic `μ(1/2)=-1/78,μ(2/3)=1/162`, source atomic `K(0,2)=-320/351`, finite-tail BIDI criterion and adversarial margin checks PASS. Exact local script Git blob equals committed GitHub blob, `py_compile` PASS. Earlier radius/actual-ζ count symbolic source test rerun PASS. **Not run** Lean/Agda kernel or CI. Not actual zero census; no strict signed theorem paid.

**Priority order**: P0 original mathematical `H_n+E_n+S<T` (or sharpened `B_n+S≤T-ε`) for every hypothetical high off-line ζ zero with its **same** original W, while paying source-selected W witness conditions; not another compiler. Parallel: Agda literal final scalar independent route and external all-character Lean theorem trust; avoid claiming any is already RH/GRH resolution.

---

## 22 November 2026 — uniform pole radius and actual-zeta logarithmic two-sided tail

**Source FIRST; original named finite analytic target mathematically
reduced; kernel acceptance pending.** This adds to the 22 Nov source
correction that the literal selected signed-W integral identity is
already theorem-bearing in Lean main.

### Original same-source owners recovered

- Synthesis/RiemannProjectiveQuarticFourWindowUniformPoleWeight.lean
  (blob 065baf7769b121c05611f92f5be55386e38e0074):
  actual high-t normalized pole weights have t-uniform
  Lipschitz K = 19 cosh(1) on [-6,6], t>=200, c=1,2.
- Synthesis/RiemannQuantitativeSymBumpLocalization.lean
  (blob f5ec98fa832e91b661193ae45259b0444c370201):
  positive normalized exact-mass symmetric radius-R bump.
- Synthesis/RiemannProjectiveQuarticFourWindowLocalization.lean
  (blob 28eaab93e1d05c214bc2b9541b5f12ef6379bba1):
  coefficient rectangle 1/2<=lambda<=2/3, |mu|<=1/10.
- Synthesis/RiemannProjectiveQuarticFourWindowPoleSameObject.lean
  (blob 60cc239d3968e25b8a42cebc18bf4744907facd3):
  actual signed pole coordinate is the determinant of four
  normalized source pairings, not a synthetic test.
- Synthesis/RiemannProjectiveQuarticFourWindowPoleLocalization.lean
  (blob 45eeecdd828d903b6c3d7406ea1c616d4852e9ae):
  each atomic determinant coordinate has abs <= 5 for t>=200.
- Synthesis/RiemannProjectiveQuarticThreeWindowRobustness.lean
  (blob 53bc06356d778d52582244bf5dc4b3af1b9c79f7):
  existing exact determinant perturbation theorem
  |D-D0| <= (4M+2)*xi for entry errors <=xi<=1.
- Synthesis/RiemannProjectiveQuarticFourWindowUniformPoleLocalization.lean
  (blob 2fbcdf785511ffc064d393d7f62d6c6de5ad212d):
  conditional fixed-width selected-W core compiler already exists.
  Its named remaining input, UniformQuarticFourPoleDeterminantCompilerTarget,
  remains UNINHABITED in UniformPoleLocalizationPaid.lean.
  Never count this mathematical source derivation as a kernel receipt.

### Explicit uniform determinant localization

For every source normalized bump, nonnegativity, exact mass and
support within R imply that the normalized pairing of an even
K-Lipschitz weight differs from its atomic-center evaluation by
at most K*R. This applies also to on-line cos(cx), c=1,2,
since Lipschitz <=2 <=K. The original FOUR-window absolute
coefficient sum is B=1+1+2/3+1/10=83/30.
Thus each of the four original smooth determinant entries differs
from the source atomic entry by at most xi=B*K*R.
Using M=5 and source perturbation theorem (4M+2)=22,
the determinant error <=22*B*K*R, for xi<=1.

The ORIGINAL determinant tolerance is
  eta0 = min(1, (7*pi^4/800)/(2*(4*(10+pi^4)+2))).
Consequently an explicit positive radius INDEPENDENT OF t is
  delta* = eta0 / [22*(83/30)*19*cosh(1)]
         = 5.53270840772e-7 approximately.
For every t>=200, 0<R<delta*, allowed lambda,mu,
the smooth/atomic determinant difference is <=eta0.
This is an exact mathematical derivation from original source
premises, not a newly admitted Lean theorem. Once its named
Lean statement is kernel-checked, the EXISTING source compiler
constructs one fixed R and selected muHalf/muTwo with original
signed target strength floor for every t>=200.

### Actual selected W full horizontal weighted C4 control

Let b_j = ||unitBump^(j)||_1 / ||unitBump||_1, b_0=1.
These are finite but numerically UNMEASURED source Mathlib
ContDiffBump values. For B=83/30, the original profile
  G = [B_0 - B_{pi/3} + lambda*B_{pi/2} + mu*B_pi]/(2R*B0)
satisfies ||G^(j)||_1 <= B*b_j/R^j.
The existing source profile is
  P_G(x)=4G(x)[A1*cos(2x)-A2*cos(x)],
with |A1|, |A2| <= B.
For original signed selected combination
  P_W = pTwo*P_half - pHalf*P_two,
the determinant pole coefficients are each <=72 in abs
(smooth response entries <=5+xi<6).
Therefore, for j=0..4,
  M_j(W)=||P_W^(j)||_1
    <= Mstar_j(R)
     = 576*B^2 * sum_{k=0}^j binom(j,k)
                   *(2^(j-k)+1)*b_k/R^k.
In particular Mstar_0=1152*B^2=220448/25.

At source t>=200, the true horizontal parameter
alpha=(Re(s)-1/2)/(t/16) satisfies |alpha|<=8/t<=1/25,
both sides of the half line; original support L<=pi+R<pi+1.
Define
  Dstar(R)= exp((pi+1)/25) *
    sum_{j=0}^4 binom(4,j)(1/25)^(4-j) Mstar_j(R).
Then the existing actual selected-W cosh-cos Fourier identity and
four integration by parts give
  |K_W(alpha,q)| <= Dstar(R)/|q|^4
for q!=0 and the true source alpha.
The literal actual-zero summand carries its exact multiplicity:
  |sourceTerm(sigma)| <= mult(sigma)*(t/16)^2*Dstar(R)
                         /|Im(sigma)-t|^4.
Dstar is finite and t-independent GIVEN the fixed-width core;
it is not a practical numerical constant and is not signed.

### Sharper ACTUAL zeta, both positive and negative ordinate tails

Do NOT reuse the obsolete A=160 total-count upper bound when
the stronger original source already exists:
  Synthesis/RiemannZeta23RvMArbitraryEndpointCountBound.lean
  (blob 5fcf3260c204e873ae4cb91de04b34d8c4d1e669)
proves existence of C_N>=0 such that
  N(A,B) <= C_N*(B-A+1)*log(B+4), 5<=A<B
on actual zeta zeros WITH multiplicity.
Synthesis/RiemannZeta23RvMTwoSidedDiscrepancy.lean
(blob c4a78b921820a0a3846659fbcb98662d4f7e8a51)
preserves count/multiplicity for negative heights by conjugation.

For t>=200, choose an integer cofinal cutoff n>=t+7.
Right original half-open shell (t+k,t+k+1] has at most
2*C_N*log(t+k+5) multiplicity. The left shell
(t-k-1,t-k] reflects into a subset of
(k-t-1,k-t+1] of width 2, including all boundary multiplicity,
so its count <=3*C_N*log(k-t+5).
For every integer k>=n, total both sides <=
5*C_N*log(t+k+5) <= 5*C_N*log(2k).
Thus the *complete positive+negative height* ABSOLUTE far tail obeys
  sum_far |literalSourceTerm(sigma)| <=
  5*C_N*(t/16)^2*Dstar(R)*[
    log(2n)/n^4 + log(2n)/(3*n^3) + 1/(9*n^3)].
The exact antiderivative is
  int_n^infinity log(2x)/x^4 dx =
    log(2n)/(3*n^3)+1/(9*n^3).
For n(t)=ceil(t+7), the RHS is O(C_N*Dstar(R)*log(t)/t)
and tends to zero as t tends to infinity.
This is a new source-grounded t-VARYING cutoff tail; it is NOT
uniform in t at fixed n. It is NOT a signed cofinal surplus,
nor a theorem forbidding an actual off-line zero.

### Tested local receipt; comparison with external theorem

Source-specific script newly committed on Agda #1533:
  scripts/check_rh_r2_uniform_pole_and_two_sided_tail_20261122.py
  commit 98eaf7e62db888fd04803888d9d49e1dfcf8e0c8,
  readback blob 76073cd50eb9befd03cb57bd61f771fef9b098a5.
Local SymPy 1.14: 256/256 exact determinant corner adversaries;
12,010/12,010 source pole-weight derivative numerical stresses;
exact coefficient algebra, full cosh-weighted 4th Leibniz derivative,
logarithmic tail antiderivative, and t^2 F(t+7)->0 PASS.
Negative controls deliberately reject dropping quadratic determinant
error and fixed-cutoff t-uniform estimates.
Locally executed mathematically matching script; committed text
was read back but not byte-compared with local test.
Original all-character source checked syntactically in
pinned MainTheorems.lean + MainConclusion.lean:
  allChi := UpperTheory.FinalTheorems.everyCharacter,
  rhOfAll := Formalism.VW.rh_of_every allChi,
  root Main.lean has unconditional *declared* RH/Dirichlet GRH
  theorem signatures. The original claim is stronger in stated
  quantification; *trusted kernel admission* is NOT established
  by any of these symbolic/finite tests. The existing DASHI
  signed compensation is still literally an assumed premise.

**P0 REMAINS:** kernel-implement uniform determinant lemma on original
Lean source; obtain an effective source bump norm witness or accept
finite symbolic constants; prove the actual signed cofinal
UniformSignedCompensationGap rho (or sharpened exact same-source variant)
including original zero multiplicities, source target threshold and
quantifier order. There is no RH/GRH claim from these tests.
No Lean/Agda or GitHub CI was run.

---

## 22 November 2026 — selected-W FULL horizontal-weighted q^-4 formula (symbolically discharged, constants/uniformity OPEN)

Following the source correction, the original Lean theorem
`QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_combinedIntegral`
and the original actual selected-W compact-`C⁴` theorem
give a concrete **human-level symbolic full-horizontal kernel
tail** at any fixed selected `W` and `t`, not just the
unweighted base channel.

Let `P_W=quarticFourSignedPoleCombinedProfile
W.R W.muHalf W.muTwo t`, supported in
`[-L,L]` (take `L=π+W.R` from the
source four-center bump support), and define
`M_j(W)=∫ |∂_x^j P_W(x)| dx` for `0≤j≤4`.
For `q≠0`, `|α|≤a`, put
`P_{W,α}(x)=P_W(x)cosh(αx)`. Product
differentiation gives the **exact formula**
```text
(P_W cosh(αx))'''' =
    P_W'''' cosh(αx)
  + 4α P_W''' sinh(αx)
  + 6α² P_W'' cosh(αx)
  + 4α³ P_W' sinh(αx)
  + α⁴ P_W cosh(αx).
```
On `|x|≤L`,
`|cosh(αx)|,|sinh(αx)|≤exp(aL)`.
The already source-proved compact Fourier
fourfold integration-by-parts lemma therefore
yields the precise conditional-norm inequality
```text
|W.signedNormalizedPairKernel(α,q)|
 ≤ exp(aL)/|q|^4
    ·[M4 + 4a M3 + 6a² M2 + 4a³ M1 + a⁴ M0].
```
For an actual off-ordinate zero `σ` in the
critical strip, the source identifies
`r=t/16`, `α=(Re σ−1/2)/r`,
`q=(Im σ−t)/r`. Hence for `t>0`,
`|α|<8/t`, and
```text
|W.signedLiteralPairSourceTerm σ|
 ≤ mult(σ) (t/16)^2 exp(8L/t)
   · [M4+4(8/t)M3+6(8/t)^2M2
        +4(8/t)^3M1+(8/t)^4M0]
   / |Im σ−t|^4.
```
The `mult(σ)` is the actual original zeta
zero multiplicity, NOT dropped for a
scalar surrogate. The estimate applies to
**both horizontal sides** because the
kernel is cosh-even in `α`; it is
an ABSOLUTE tail envelope and proves
NO desired signed surplus by itself.

**Local executable mathematical check:** the EXISTING
`scripts/check_rh_r2_explicit_zero_shell_fourier_20261117.py`
was extended in place (commit `e3c25a13`) to audit
the exact source identity status, the five-term
weighted fourth Leibniz derivative,
horizontal reflection, `α=0` base recovery
and true strip `8/t` radius. Independently
executed local SymPy 1.14.0: **7/7**
new exact derivative/normalization assertions
PASS. The full revised file has been
committed and source-readback verified but
not executed end-to-end in this runtime;
do not state a complete script receipt
or native Lean kernel result.

**Precisely UNPAID:** obtain numerical/source-quantified
uniform bounds for the **actual**
`W.R,W.muHalf,W.muTwo,W.poleHalf,W.poleTwo`
and `M_j(W)`; prove those are strong enough,
with actual two-sided ζ-zero counts and
tail/cutoff quantifiers, to pay the
correct-polarity cofinal
`W.UniformSignedCompensationGap rho`.
An arbitrary fixed-t positive finite-core
estimate, absolute convergence, symbolic
`q^-4` formula or same-ordinate local
positive signal does not imply the
universal strict RH inequality. This
update is a proof-of-algebraic-estimate
at paper level, **not** a new kernel-accepted
original analytic GRH/RH result.

---

## 22 November 2026 — SOURCE RECLASSIFICATION: selected-W integral already proved

This dated source audit **supersedes the first 17 Nov open
lemma** `selectedQuarticFourWActualProfileIntegralExact`,
as phrased there: **the literal same-selected-W
weighted Fourier/cosh representation is ALREADY
theorem-bearing in original Lean main**, not an
unconstructed theorem. Do not write a new replacement
theorem or copy the same proof into this branch.

Inspected exact source paths and Git blobs:

- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`
  blob `4d0437ffb058c7e8b6961521a611608b1494ba3f`,
  **lines 1142–1203**:
  `QuarticFourSignedPolePair.signedNormalizedPairKernel_eq_combinedIntegral`
  proves directly, for the ACTUAL selected
  `QuarticFourSignedPolePair t`,
  ```text
  W.signedNormalizedPairKernel α q =
     ∫ x, quarticFourSignedPoleCombinedProfile
                W.R W.muHalf W.muTwo t x
             * cosh(α*x) * cos(q*x)
  ```
  including both original signed pole coefficients
  and the two actual source windows; the proof
  establishes integrability and expands the true
  source definitions, not an abstract W.
- In the **same** source, lines 415–440:
  `W.signedLiteralPairSourceTerm_eq_normalizedPairKernel`
  identifies the genuine original non-same-ordinate
  zero summand with
  `mult(σ)/(t/16)² * K_W(heightOf σ/(t/16),
      (Im σ−t)/(t/16))`. The necessary analytic
  `Re(s)−1/2` reflection is already visible
  through the cosh-even dependence.
  `W.signedNormalizedPairKernel_eq_jointJet`
  and `_eq_quarticJet` also source-write
  the exact base/horizontal/remainder split.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleTarget.lean`
  blob `16110e433efd16379c6b93bdc13420036b1d6411`
  defines the **literal** combined profile and
  exact zero- and second-moment identities.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourthOrderQuotient.lean`
  blob `6b30db459d28a2b5707cec004b570ff7061e1a8a`
  proves source-selected
  `quarticFourSignedPoleCombinedProfile_contDiff_four`,
  `compactCosineTransform_abs_le_invPowFour`
  and the **literal base ordinate channel**
  `W.signedOrdinateTest_abs_le_gap_four`,
  ```text
  |W.signedOrdinateTest x|
    ≤ (t/16)² * ∫ |P_W''''(u)| du / (x−t)⁴
  ```
  for x≠t and t>0. The original proof
  already uses the actual combined W profile,
  not an arbitrary test substitute.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean`
  blob `2fb66d2e7c4345673e1dda82e67823bf2d7e0481`
  proves the actual cone/good/far
  **algebraic** split and convergence compiler,
  but `W.UniformSignedCompensationGap rho`
  at lines 941–953 remains an **ASSUMED
  strict eventually quantified inequality**.
  Its theorem
  `completedSignedResidual_lt_target_of_uniform_compensation_gap`
  at lines 960+ consumes, rather than constructs,
  that analytic payment.

**Revised R2 priority:**
1. **PAID SOURCE-WRITTEN:** exact selected
   W ↔ weighted cosh-cos integral,
   source multiplicity/scaling and both
   horizontal sides, exact `C^4`/compact
   selected W, fourth-power base-channel
   `signedOrdinateTest` decay.
2. **OPEN QUANTITATIVE:** explicit *selected*
   `W.R,W.muHalf,W.muTwo,W.poleHalf,W.poleTwo`,
   actual derivative-norm and
   horizontal-weighted `P_W(x)cosh(αx)`
   bounds and their uniformity in t,
   original ζ zero multiplicities and
   cutoff. Do not incorrectly promote
   the `α=0` **base** tail theorem
   to the full `α≠0` horizontal source.
3. **OPEN ORIGINAL SIGN:** a **strict
   correct-polarity cofinal margin**
   `W.UniformSignedCompensationGap rho`
   or its source-valid sharpened version,
   with actual original ζ-zero configurations,
   completed residual and the exact
   quantifier order (not test-specific floats).
4. **OPEN TRUST:** no new exact-head Lean
   kernel receipt was run by this
   Git source-readback audit.

**Acceptance distinction:** source declarations, bodies
and dependency edges were read directly from the current
`dashi_lean4/main` tree, but no Lean/Agda typechecking
was executed in this runtime. This corrects a
stale research-status classification rather
than newly proving an R2 estimate.

---

# RH R2 — explicit unconditional shell count A=160, parameterized C, exact remaining lemmas (2026-11-17)

**Classification:** classical unconditional external zero-count theorem plus elementary analytic deductions; local SymPy checks of algebra. **R2 OPEN. No new Agda/Lean kernel theorem.** The explicit value A below is universal but deliberately generous.

## 1. Verified zero-count source and constant

Use Chiara Bellotti and Peng-Jie Wong, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function*, Math. Comp., published electronically 2025-11-14, DOI 10.1090/mcom/4133, with
`|N(U) - U/(2pi)*log(U/(2pi*e))| <= 0.10076 log U + 0.24460 loglog U + 8.08344` for `U>=e`. Count includes multiplicity; no RH required.

For `U>=e`, using `loglog U<=log U`, `U log U>=e`, and `U/(2pi)log(U/(2pi*e)) <= U log U`, one obtains
`N(U) <= (1+0.34536+8.08344/e)*U log U <5U log U`.
For `0<=U<e`, monotonicity gives `N(U)<=N(e)<5e<20`.
Thus for all `U>=0`,
`N(U)<=20(1+U)log(e+U)`.

For `t>=0`, integer `k>=1` and `X=1+t+k>=2`, symmetry of the actual nontrivial zeta zeros about the real axis gives the **multiplicity-weighted** shell count
`Z(t,k)=#{rho: k<=|Im(rho)-t|<k+1} <=2N(t+k+1)`.
Using `1+t+k+1=X+1<=2X` and `log(e+X+1)<=2log(e+X)` gives
**`Z(t,k)<=160*(1+t+k)*log(e+t+k)`**.
At the inclusive shell boundary use `N(t+k+1)` as an upper bound, so endpoints cannot invalidate the inequality. This count is **not** a proportion of off-line zeros and does not assume RH.

Note: the previously supplied Hasanalizade–Shen–Wong JNT DOI was incorrectly given as `...06.028`; the verified DOI is **10.1016/j.jnt.2021.06.032**. The cited Carneiro–Chandee–Milinovich 'Mollifiers and the zeros...' title/identifier was not verified and is not used as a source of this bound.

## 2. Parameterized fourth-derivative kernel constant, NOT yet instantiated

For `P∈C_c^4(R)` supported on `[-L,L]` and
`F(alpha,q)=integral P(u)e^(alpha*u)e^(i*q*u)du` with `|alpha|<=a`, four integrations by parts give
`|F(alpha,q)|<= e^(aL)/|q|^4 * sum_(j=0)^4 binom(4,j)*a^(4-j)*||P^(j)||_1`.
In particular with `r=t/16`, `alpha=(beta-1/2)/r`, the zeta critical strip gives `|alpha|<=1/(2r)=8/t`, and for `|gamma-t|>=k>=1`, using `((k+1)/k)^4<=16`, the multiplicity-normalized physical term has envelope
`C(t,P)/(1+k)^4`, where
`C(t,P)=16*r^2*exp(L/(2r))*[M4+4a M3+6a² M2+4a³ M1+a⁴ M0]`,
`a=1/(2r)`, `M_j=||P^(j)||_1`.

**Important:** the original `W.signedNormalizedPairKernel` is defined as a signed linear combination of `genericProjectivePairKernel` terms for two distinct profiles. Before inserting this `C(t,P)`, one MUST prove the appropriate exact integral representation with its signed pole factors, distinguish possible `cosh(alpha u)`/base subtractions, and bound each term. The formula is a **conditional donor**, not an evaluation of the selected witness.

The original Lean identity is
`signedLiteralPairSourceTerm sigma = mult(sigma)/r² * W.signedNormalizedPairKernel ((beta-1/2)/r) ((gamma-t)/r)`.
Original finite far source is `W.literalFarExactAt eta n` with `eta=1/(pi+1)` and `centeredZeroFinset t n` iff `t-n<gamma<=t+n`. The original `literalGoodQuarticGainAt` uses `S*(alpha²q²-q⁴/6)`, **not** the newer complete quartic with an additional `-alpha⁴/6`.

## 3. Local executable check

`scripts/check_rh_r2_explicit_zero_shell_fourier_20261117.py` checks:
- the 2025 published coefficients imply the generous factor 5 via exact rational/SymPy inequalities;
- the two-sided unit-shell count admits A=160;
- binomial fourth derivative envelope and physical rescaling;
- the exact fixed-t tail integral and monotonicity.

It does **not** numerically integrate the selected W or formally prove the cited N(U) theorem. These remain separate acceptance gates.

## 4. Exact remaining lemmas / producers

1. **`selectedQuarticFourWActualProfileIntegralExact` (OPEN):** extract the constructed `QuarticFourSignedPolePair t` and show the exact selected `signedNormalizedPairKernel` equals the claimed Fourier integral or a finite combination, including pole coefficients, horizontal factor and source normalization, for every `alpha,q`.
2. **`selectedQuarticFourWDerivativeNormsExplicit` (OPEN):** determine actual W parameters and compact support `L`, calculate/certify `||P_j^(m)||_1` for `m=0,...,4`, bound `cosh`/horizontal terms, and construct an explicit valid `C(t,W)` on `0<=beta<=1`. A symbolic expression with unknown norms does not close this lemma.
3. **`originalActualZetaUnitShellCountA160` (CLASSICAL COROLLARY; NATIVE OPEN):** instantiate Bellotti–Wong 2025 zero count in Lean for the original `Zeros` type, multiplicity, real-axis reflection and interval endpoints; deliver the numeric universal constant `A=160`.
4. **`originalLiteralFarExactCertifiedFinite` (OPEN):** certified interval value of `W.literalFarExactAt eta n` for the source selected W and actual zero ordinates, preserving sign; verify `OffOrdExactAt=ConeExactAt+GoodExactAt+FarExactAt`.
5. **`originalSelectedTargetThresholdCertified` (OPEN):** calculate actual `T_W(rho)=4D_comb(rho)+∫Psi_t dmu` from the literal selected witness, not generic surrogate.
6. **`originalSelectedFiniteSignedSurplusStrict` (OPEN):** construct a rational `epsilon>0` and finite cutoff with a **certified** positive surplus in the *correct polarity*, including local remainder and target threshold; explicitly handle same-height exclusion and multiplicities.
7. **`originalSelectedUniformCofinalTail` (OPEN):** combine an instantiated `A,C(t,W)` with a rigorously uniform cutoff and the literal signed far term; the supplied majorant only converges with n for fixed t.
8. **`originalR2EventualSignedCompensationGap` (OPEN):** prove `exists eps>0, N, forall n>=N: LocalDebt_n-SignedCompensation_n<=T_W(rho)-eps` for the originally quantified t,rho,W. For fixed t and W, a certified total surplus and a tail smaller than half that surplus suffice; a margin depending on t or rho does **not** imply the universal target.
9. **`originalR2NativeKernelWeld` (OPEN):** typecheck and import the actual proof at exact Lean/Agda heads, then update gate ledger only after the original acceptance predicate is discharged.

**Accounting:** Classical external A bound established, but the native carrier and all selected-W signed-gap producers OPEN. Portfolio remains **13/28 settled, 15/28 open**; **0/6 original Clay endpoints**.
