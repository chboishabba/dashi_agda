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
