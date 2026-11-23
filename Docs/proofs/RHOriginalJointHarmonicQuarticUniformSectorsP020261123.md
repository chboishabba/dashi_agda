# RH/GRH P0 — original signed quartic joint harmonic kernel, universal local sign sectors (23 Nov 2026)

**Scope:** mathematical source-aligned consequence of the original *Lean main* quartic RH kernel, exact rational inequalities independently checked by local SymPy 1.14, and a separate numerical compact-smooth fixture checked by mpmath. The selected original test exists through upstream Lean witness constructors, but the new quantified inequalities have **not** been typed and kernel-checked in Lean/Agda. No global signed zero-distribution estimate or RH/GRH proof is claimed. Preserve original zero ordinate, horizontal displacement, multiplicity and post-sixth local slack.

## Original theorem owners (reuse, do not rebuild)

In `chboishabba/dashi_lean4` **main**:

- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`: `signedNormalizedPairKernel_eq_jointJet` and `signedNormalizedPairKernel_eq_base_add_horizontal` identify the *original* source pair kernel as the even real Fourier–cosh transform of `quarticFourSignedPoleCombinedProfile`. `signedHorizontalQuadraticKernel_zero` gives `M2=0` for the same pair, and `signedHorizontalQuadraticKernel_secondDeriv_zero` says `Q_W''(0)=4*W.targetStrength`. Since `Q_W(q)=∫P_W(v)v²cos(qv)dv`, `Q_W''(0)=-M4`, hence `M4=-4*W.targetStrength` (NOT an assumed sign).
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleQuantitativeBand.lean`: `combinedProfile_taperMass_le_explicit`, `quarticFourCombinedProfileMassBound_lt_5184` for **every** `t≥200` original witness, plus `combinedProfile_support_abs_le_pi_add_one` implying support `|v|≤π+1<5`. Original `QuarticFourSignedPolePair` target-strength floor in the selected P0 witness is `T=W.targetStrength≥7π⁴/1600>567/1600`.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleNMu.lean` and `...JointHorizontalJet.lean`: per-actual-zero identity `signedLiteralPairSourceTerm_eq_normalizedPairKernel` with `α=16(β-1/2)/t`, `q=16(γ-t)/t`, scalar `mult(ρ)/(t/16)^2`.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean`: `postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack`, `canonicalLocalBudgetSlack_nonneg`; full P0 is `H_W+S_W<4d_W(ρ)+I_W`. An analytic sign-sector theorem does not pay that strict terminal.

## A. SAME analytic test, true two-dimensional harmonicity

Let `P_W(v)=quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t v`, where the original pole coefficients and selected radius remain attached to the *same* witness W. Define

```text
K_W(α,q) = ∫_R P_W(v) cosh(α v) cos(q v) dv
         = Re ∫_R P_W(v) cos((q+iα)v) dv .
```

Compact support permits differentiation under the integral; `∂_α² K_W=-∂_q² K_W`. In particular `Δ_(α,q)K_W=0`, a genuine real-harmonic action of the actual horizontal/ordinate coordinates. This is **not** a nontrivial automorphism of the fixed original W, nor a 15-bit/SSP/Monster action.

Put `z=q+iα`, `ρ_*²=q²+α²`, `M_j=∫v^j P_W(v)dv`, `T_W=W.targetStrength`. Exact even-cosine Taylor, source `M2=0` and `M4=-4T_W` give

```text
K_W(α,q)-K_W(0,0)
 = -(T_W/6) Re z⁴ + E6
 = -(T_W/6)(q⁴-6α²q²+α⁴)+E6 .
```

The compact profile `|v|<5` and `||P_W||₁<5184` provide an explicit *source-witness-uniform* remainder for ALL real α,q:

```text
|E6| ≤ (5184*5⁶/720)*ρ_*⁶ * exp(5|α|).
```

This follows by applying Taylor with integral remainder to `cos(s z v)`, retaining the zero fifth-order coefficient and bounding the sixth derivative by `exp(|αv|)`; no asymptotic assumption and no selected `R(t)` lower bound are required. For `ρ_*≤10^-4`, `exp(5|α|)<2`, hence `|E6|<225000 ρ_*⁶`.

## B. NEW certified original-W two-dimensional strict sign sectors

Let `P4=q⁴-6α²q²+α⁴=ρ_*⁴ cos(4θ)`, for `q=ρ_* cosθ, α=ρ_* sinθ`. On the explicit compact sector

```text
0<ρ_*≤1/10000    and    |P4|≥ρ_*⁴/20,
```

the source-independent strength floor `T_W>567/1600` makes the fourth term at least `(567/192000)ρ_*⁴` in magnitude, whereas the remainder is less than `225000/10⁸ ρ_*⁴=(9/4000)ρ_*⁴`. The **strict rational margin** is

```text
567/192000 - 9/4000 = 9/12800 > 0.

P4>0 => K_W(α,q)-K_W(0,0) ≤ -(9/12800)ρ_*⁴ < 0;
P4<0 => K_W(α,q)-K_W(0,0) ≥ +(9/12800)ρ_*⁴ > 0.
```

The neutral origin is retained, and `|P4|<ρ_*⁴/20` is *uncertified*, not declared to have a sign. These are genuine **full-dimensional open cones of angles** at small radius, rather than just Fourier-response roots.

Sharper rational controls on the axes/diagonal for every `0<h≤1/10000`:

```text
K_W(0,h)-K_W(0,0) ≤ -(909/16000)h⁴ < 0.
K_W(h,0)-K_W(0,0) ≤ -(909/16000)h⁴ < 0.
K_W(h,h)-K_W(0,0) ≥ +(873/4000)h⁴ > 0.
```

The diagonal uses `ρ_*²=2h²` directly (so remains valid even when `ρ_*>1/10000`). The bounded remainder ratio is monotone in `h²`, hence the estimates hold for **all** smaller positive h, not merely the endpoint. At `t≥80000`, the actual critical-strip horizontal normalization satisfies `|α|=16|β-1/2|/t≤8/t≤10^-4` for `|β-1/2|≤1/2`; however, a given actual zero ordinate need NOT have `q=|α|` or belong to a certified angular sector. An on-ordinate off-line target has `q=0`, so the second estimate is a conditional positive **height-defect** donor after the original base-minus-pair normalization and positive multiplicity factor; **not** an independent upper bound on the global off-ordinate signed source.

## C. Independent tests, limitations and exact P0 weld

`scripts/check_rh_p0_harmonic_joint_kernel_20261123.py` passed locally with SymPy and mpmath. Exact script Git SHA-1 blob `0404952cd11d6c73b2ada029b135225ab4b9d267` was checked byte-for-byte against GitHub after commit. Acceptance includes: harmonic joint quartic identity, all exact rational margin inequalities including full angular sector `9/12800`, physical `t≥80000` normalization, and an independent genuine C∞ even compact signed fixture `P=-b''''` where `b(v)=exp(-1/(1-v²))` for `|v|<1` (zero outside); its cosine–cosh kernel has precisely the required J2-null and negative fourth moment signs. For `h=0.1,0.01,0.0001`, the fixture's ordinate and horizontal axes are negative and diagonal positive, consistent with exact moment geometry. **This smooth fixture is NOT original selected W**, and cannot substitute for original-source proof obligations.

**P0 remains OPEN:** convert this source-aligned analytic estimate to a Lean kernel theorem *if needed*, but do NOT mistake it for `LiteralFarMinusMuUniformHighEstimate`. Need actual selected `W(t)` signed zero-minus-µ correlation over all q including complementary far sectors, actual β and γ and multiplicities, original post-sixth slack `S_W≥0`, and then strict `H_W+S_W<4d_W(ρ)+I_W` independently of the already-known nonnegative gap. Existing genuine zero-bucket sign and RvM-count fourth-primitive non-implication remain relevant negative controls. The GRH all-Dirichlet-character upstream Lean admission/root import and Agda `H_X` same-object realization are separate P0 gates. No Lean/Agda kernel, CI, certified actual ζ-zero selection, or RH/GRH proof in this tranche.

**Attribution:** original Weil explicit-formula/zero configurations, original Zeta23 `mu`, Lean original signed quartic W/jet/target-strength/support/mass lemmas; DASHI contribution is the quantitative **joint complex-Fourier harmonic sector bound** and source-preserving P0/no-promotion audit.
