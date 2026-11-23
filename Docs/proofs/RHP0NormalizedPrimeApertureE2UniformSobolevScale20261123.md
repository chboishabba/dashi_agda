# RH P0 E2 — normalized annihilator and uniform physical two-prime source scale (23 Nov 2026)

**Acceptance:** Mathematical analytic estimates with exact-rational locally executed regression. **Not** Lean/Agda kernel-checked; not a source-selected Mathlib unit bump numerically evaluated; **not** complete E2 global post-sixth/far bound or E3 independent signed strict estimate. RH/GRH remain OPEN. Builds on the **existing** original `Synthesis/RiemannSelectedPrimeSensitiveTwoScale.lean` (source-native literal von-Mangoldt prime2/3/four-channel theorem) and draft Lean [#116](https://github.com/chboishabba/dashi_lean4/pull/116), not a new Weil formula.

## 1. Correct an avoidable apparent derivative obstruction

Previous E0 monic order-52 source annihilator `A_t(D)` with an order-52 prescribed-jet port made derivative costs look intrinsic. Instead set `r=t/16`, `D=d/du`, and normalize at zero:

```text
A_t(D)=(D²+r²)^9(D²+4r²)^9 *
  Π_{c=1,2; σ=±1}
   [((D−1/2)²+(t+σcr)²)((D+1/2)²+(t+σcr)²)],
Q_t(D)=A_t(D)/A_t(0)=Σ_{j=0}^{26} q_j(t)D^{2j}.
```

For t≥200, `A_t(0)>0`, `q_0=1`, **all coefficients nonnegative** and the following coefficientwise bound is an *analytic theorem*:

```text
0≤q_j(t)≤binom(26,j)(256/t²)^j,  j=0,...,26.
```

Proof: the first 18 normalized quadratic factors are `(1+256D²/t²)^9(1+64D²/t²)^9`. Each of the four pole quartics has frequency `ω=t+σcr`, `A=ω²+1/4≥49t²/64`, and normalized form `1+(2/A−1/A²)D²+D⁴/A²`. At t≥200 its coefficients are nonnegative, and `2/A≤128/(49t²)<512/t²`, `1/A²≤(64/49)²/t⁴<(256/t²)²`; it is coefficientwise bounded by `(1+256D²/t²)^2`. Product gives exponent 9+9+8=26. Independent local `fractions.Fraction` multiplies all 26 actual scalar factors at heights 200/300/1000/32768/1e6 and checks all 27 coefficient bounds. Not extrapolated from the five samples.

## 2. Fixed-width C∞ flat-top ports: exact original eight constraints and uniform Sobolev norms

For p=2,3, choose once and for all an even compact C∞ **flat-top** b_p, `0≤b_p≤1`, equal to 1 near ±log p, supported inside radius `δ=1/32` of those points. Its support is inside `U=(-1.25,-0.36)∪(0.36,1.25)`, disjoint from original high-t core and all other prime-power samples, and `||b_p||1≤4δ=1/8`.

Then `h_{p,t}=Q_t(D)b_p` is even, compact smooth, and annihilates the original EXACT eight source-weight integrals (two A responses, projective M2/M4/M6/M8, two literal pole integrals) by 52-fold formal-adjoint integration by parts. Since every positive derivative of b_p vanishes at ±log p and the constant coefficient is one,

```text
h_{p,t}(log p)=1 EXACTLY, h_{p,t}(log q)=0 (other prime),
h_{p,t}(log n)=0 (all n≥4), for EVERY t≥200.
```

No 52nd-order *point-jet* or finite matrix rank premise is needed. If `B_{p,k}=||b_p^(k)||1`, then for all fixed derivative orders k,

```text
||h_{p,t}^(k)||1 ≤ Σ_{j=0}^{26} binom(26,j)(256/t²)^j B_{p,k+2j}
                 → B_{p,k} as t→∞.
```

This is an explicit all-height **source incremental Sobolev envelope**. Define the finite sufficient threshold

```text
T_b = max(32768,
     16 max_{p∈{2,3},1≤j≤26}
       (208 binom(26,j) B_{p,2j})^(1/(2j))).
```

At t≥T_b, each of 26 correction summands is ≤1/208, whence `||h_{p,t}||1≤1/8+26/208=1/4`. T_b is **effectively specified by finitely many derivatives of a chosen explicit C∞ plateau**, but a *numerical evaluated* bound for those derivative integrals has not been performed. The support stays in the same fixed physical aperture.

## 3. True original selected-W physical target floor

Original `...SignedPoleQuantitativeBand.lean` and `...SignedPolePair.lean` supply `||P_norm||1<5184`, `supp(P_norm)⊂(-5,5)`, `M0=M2=0`, `M4=-4T_W`, `T_W>567/1600`. The physical profile has `P_phys(u)=r^-1 P_norm(r u)`, so `M4phys=r^-6 M4norm` and `d_W(a)=T_W a⁴/(24r⁶)+R6`. Source Taylor remainder:

```text
|R6| ≤ [5184*5^6/(4*6!)] cosh(5|a|/r) |a|⁶/r⁸
     = 28125 cosh(5|a|/r) |a|⁶/r⁸.
```

For t≥32768 (r≥2048), `0<|a|≤1/2`, `cosh(5/(2r))<2` and `|a|⁶≤|a|⁴/4`; hence for **every originally selected high W with original floor**,

```text
d_W(a) ≥ c_* a⁴/r⁶,
c_* = 567/(1600*24) - (2*28125)/(4*2048²)
    = 2393451/209715200 > 1/100.
```

This is an independent analytic original-source local target lower estimate, not the original global signed completed P0 estimate.

## 4. Four-port exact physical amplitude admission and price of prime visibility

Existing Lean `halfWindow_taperMass_le`, `twoWindow_taperMass_le`, `poleHalf_abs_le`, `poleTwo_abs_le` imply for either endpoint `G_*:=||G||1≤83/30<3` and `|P_pole|≤2 cosh(1)(83/30)^2<32`. Since `A_c(g_phys)=(1/r)∫G(v)cos(cv)dv`, `|B_g(u)|≤2G_*/r`. Each of the four real independent original signed prime-port profile variations has `P_i(u)=±4 P_pole h_{p,t}(u)B_g(u)`. On `|u|≤5/4`, `cosh(|u|/2)<2`; at t≥T_b, `||h||1≤1/4`. The actual tenth-order target-norm constant satisfies:

```text
C_i = (4*10!)^-1 ∫ |P_i(u)| |u|^10 cosh(|u|/2)du
    < [6484375/28538044416]/r < 1/(3000r).
```

Choose each real port amplitude `ε_i=κ_i/r^5`, `|κ_i|≤1`, with arbitrary independent signs. The exact M0/M2/M4/M6/M8 cancellations and `|a|^6≤1/64` give the original all-strip target-positivity gate:

```text
Σ_i |ε_i| C_i < 1/(750r⁶) < 64*c_*/r⁶ ≤ 64*m_W .
```

Thus **for all t≥T_b the extended four-port target is still strictly positive throughout 0<|a|≤1/2**. This is a nontrivial **uniform-in-high-height admissible amplitude scale** after an explicit finite threshold, not an assertion for arbitrary perturbation size.

The exact original Lean source prime response is `4(log p/√p)cos(t log p) ε_i P_pole B_g(log p)`, hence `O(r^-6)`—the **same height power** as the original quartic target. This matches scale only: at arbitrarily near-double prime phase resonances the total arithmetic response may be much smaller and its sign can flip. No independent P0 strict signed source bound is proved.

## 5. Paid physical sixth/eighth moments, and the remaining absolute-zero factor

For k=0,2,4,6,8,10, the **increment** in the signed physical projective profile obeys

```text
∫ |ΔP_phys(u)| |u|^k cosh(|u|/2)du
    < 1536 (5/4)^k /r⁶,
```

in particular sixth moment <5859.375/r⁶ and eighth <9155.2734375/r⁶. These are true PHYSICAL-axis source bounds. Old normalized support<5 certificates must not be imported as-is.

The bracket still oscillates at frequency r: `|B_g^(m)|≤G_*(1+2^m)r^(m-1)`. With each flat-top `||h^(l)||1` bounded, Leibniz gives `||(ΔP_phys)^(k)||1=O(r^(k-6))`; for k=8 this can grow O(r²), so the *full raw physical derivative* bound is NOT uniform. Integration by parts at normalized ordinate offset `q=(γ−t)/r` gives a genuine incremental Fourier estimate `|Fourier(ΔP_phys)(r q)|=O(r^-6 |q|^-k)` for fixed q≠0, including the physical horizontal factor `cosh((β−1/2)u)`.

**Critical unresolved E2/E3 distinction:** a normalized unit-q band contains O(r log t) actual zeta zeros by RvM; summing these envelopes in absolute value produces only O(r^-5 log t), a factor O(r log t) larger than the original O(r^-6) target. The source-zero/Gamma *signed* correlation and complete post-sixth slack must be bounded independently; this does not follow from cancellation in the same explicit-formula equality. The full original E2 FarExact/Schwartz/post-sixth compiler has NOT been re-certified here.

## 6. Execution and remaining gates

Executed local exact rational `scripts/check_rh_p0_normalized_annihilator_e2_20261123.py`; full independent five-height polynomial coefficient regression, all-t factor bound, source m_W floor, four-port C_i and epsilon scale, sixth/eighth absolute moments and relative Fourier scaling PASS. Source and run receipt on [Agda PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533) (draft, unmerged); new normalized scalar-annihilator even/zero source theorem bodies on [Lean PR #116](https://github.com/chboishabba/dashi_lean4/pull/116) (draft, NOT compiled). This is a SAME original selected-W source estimate conditional on constructing the fixed flat-top extension, not a substitute bump claimed to be the original W.

**OPEN:** E0 Lean actual smooth inhabited carrier; E1 formal kernel verification; E2 a numeric evaluation of T_b for an explicitly implemented plateau and the full original post-sixth/far-shell/Zeta23 acceptance with all rates; E3 an INDEPENDENT strict complete signed prime/zero/Gamma estimate at every hypothetical off-line height, including near resonance. No Lean/Agda kernel or GitHub CI run. RH/GRH remain OPEN.
