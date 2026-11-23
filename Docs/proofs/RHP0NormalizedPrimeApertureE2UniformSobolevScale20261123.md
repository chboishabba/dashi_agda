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

**Coarse generic normalized-q bound, NOT optimal:** counting O(r log t) actual zeta zeros across a unit-q band against a generic r^-6 envelope only yields O(r^-5 log t). However the original frozen projective product has exact PHYSICAL-frequency sidebands at ±r,±2r. The sharper wavepacket cut below improves the global absolute increment to O(r^-6 log t), leaving ONE LOG, not one power of t. The original complete post-sixth and independent E3 signed strict estimate are still UNPAID.

## 6. Execution and remaining gates

Executed local exact rational `scripts/check_rh_p0_normalized_annihilator_e2_20261123.py`; full independent five-height polynomial coefficient regression, all-t factor bound, source m_W floor, four-port C_i and epsilon scale, sixth/eighth absolute moments and relative Fourier scaling PASS. Source and run receipt on [Agda PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533) (draft, unmerged); new normalized scalar-annihilator even/zero source theorem bodies on [Lean PR #116](https://github.com/chboishabba/dashi_lean4/pull/116) (draft, NOT compiled). This is a SAME original selected-W source estimate conditional on constructing the fixed flat-top extension, not a substitute bump claimed to be the original W.

**OPEN:** E0 Lean actual smooth inhabited carrier; E1 formal kernel verification; E2 a numeric evaluation of T_b for an explicitly implemented plateau and the full original post-sixth/far-shell/Zeta23 acceptance with all rates; E3 an INDEPENDENT strict complete signed prime/zero/Gamma estimate at every hypothetical off-line height, including near resonance. No Lean/Agda kernel or GitHub CI run. RH/GRH remain OPEN.


## 7. IMPORTANT E2 SHARPENING — physical Fourier sidebands remove the artificial factor r

The generic normalized q derivative bound above is too pessimistic for the **actual original source construction**, because the physical bracket is the precise cosine combination `A1 cos(2ru)−A2 cos(ru)`, not an arbitrary rapidly oscillating function. For a port `P_i(u)=4 P_pole ε h(u)[A1 cos(2ru)−A2 cos(ru)]`, let

```text
H_a(ξ) = ∫ h(u) cosh(a u) cos(ξ u)du,
ω=γ−t,  |a|=|β−1/2|≤1/2.
```

Then the **EXACT** physical horizontal-and-ordinate Fourier kernel is

```text
K_i(a,ω)=2 P_pole ε [
    A1( H_a(ω+2r)+H_a(ω−2r) )
   −A2( H_a(ω+r)+H_a(ω−r) )].
```

This follows from `cos(mru)cos(ωu)=[cos((ω+mr)u)+cos((ω−mr)u)]/2`, preserving the source factor FOUR and both horizontal and ordinate coordinates. The FOUR packets are centered at physical offsets ±r and ±2r, each with fixed O(1) physical-frequency width (NOT O(r)). Because `h=Q_t(D)b_p` has uniform `W^{k,1}` bounds at every fixed k, `h(u)cosh(a u)` does too uniformly over the true critical strip. Thus for k≥3,

```text
|H_a(ξ)| ≤ C_{b,k}/(1+|ξ|)^k
```

with `C_{b,k}` independent of t once t≥T_b.

The original Riemann–von Mangoldt arbitrary-endpoint zero count implies, INCLUDING actual zero multiplicities and both ±ordinate ranges, a bound `N([y+n,y+n+1])≤C log(y+n+3)` for y≥1. For each packet center `y=t±r` or `t±2r` (all comparable to t), summing physical **unit-width** shells using `Σ_{n≥0}(1+n)^-3<∞` yields

```text
Σ_{actual nontrivial zeros ρ} m_ρ |H_{βρ−1/2}(γρ−y)|
     = O_{b}(log(t+3)),
∫_ℝ |H_0(τ−y)| |Zeta23.mu(τ)|dτ
     = O_{b}(log(t+3)).
```

Since the exact original coefficients are `ε A_c=O(r^-5)*O(r^-1)=O(r^-6)`, the **FULL absolute increment**, summed over the complete physical zero and Gamma channels, satisfies

```text
|ΔZero|+|ΔGamma| = O_b(r^-6 log(t+3)).
```

**This improves the crude O(r^-5 log t) to O(r^-6 log t): only ONE logarithm remains versus the original quartic O(r^-6) target.** The improvement is a SAME-source geometric consequence of the two exact shifted Fourier packets for each on-line radius. It does NOT prove the missing strict terminal: `log t` is unbounded, prime phases can approach zero simultaneously, and the original post-sixth compensation `S_W` must be recomputed on this new test. Cancellation within the completed Weil identity is NOT independent proof of strict RH.

Executed local exact SymPy cosine shift + compact flat-top C∞ Fourier fixture regression: `scripts/check_rh_p0_prime_wavepacket_e2_20261123.py`; same-source implementation is committed on DASHI PR #1533. Source unit-shell summation is an analytic proof argument, not new Lean kernel code. **E2 full source post-sixth and E3 independent sign still open.**


## 8. P0 E2 improvement: **sharp** three-sheet punctured-27 coefficient envelope

**Reference:** [complete 26/J geometric arithmetic proof ledger](RHP0Punctured27GeometricAnnihilatorCoefficientEnvelope20261123.md); [exact rational coefficient regression](../../scripts/check_rh_p0_punctured27_geometric_majorant_20261123.py); [native original typed 9+8+9 Agda chart](../../DASHI/Analysis/RHPrimeAperturePuncturedFactorChartExact.agda). This corrects the original `binom(26,j)*(256/t²)^j` estimate to an exact **source-sharp** factor-by-factor coefficient envelope.

With the ORIGINAL physical scale `r=t/16`, `256/t²=1/r²`. The 52nd-order even annihilator's 26 effective **majorant** quadratic slots have three-sheet 9+8+9 weights: first nine `1` at r; middle eight as TWO virtual slots at each of the four ORIGINAL pole frequencies k r for k=14,15,17,18 with weights `1/k²`; last nine `1/4` at 2r. The exact original quartic at k r becomes `1+[2(k²−δ)/(k²+δ)²]x+[1/(k²+δ)²]x²`, x=(D/r)², δ=1/(4r²)>0. This is dominated coefficientwise by `(1+x/k²)²` and approaches that upper envelope as δ→0. **Four quartics do NOT factor into eight real quadratic factors**; the eight middle slots are for the bound ONLY.

```text
E(x)=(1+x)^9(1+x/4)^9 Π_(k=14,15,17,18)(1+x/k²)^2
    =Σ_(j=0)^26 E_j x^j.

0≤q_j(t)≤E_j/r^(2j)≤binom(26,j)/r^(2j)  (all t≥200).
```

Every E_j is the EXACT elementary symmetric polynomial of 26 original source majorant slot weights; `E_1=1294113017/114704100≈11.2821862253` versus old 26; `E_2≈58.8625457` vs old 325; `E_13≈2.953309` vs old 10400600; `E_26≈2.23716×10^-25` vs old 1. As t→∞, `q_j(t)r^(2j)→E_j` for every j, so **E_j is a SHARP t-uniform coefficientwise bound** within this ORIGINAL source. The 27 coefficients q0..q26 include the distinguished q0=1 plus 26 graded coefficients, but their 26 indexes are not canonically the same object as the 26 majorant-factor slots. The source `J=RI⊕J0` 1+26 and F4 dimension 52=2×26 match the INDEX SHAPE, not a Jordan multiplication or Lie representation. Antipodal sign survives in the original site chart, since outer-sheet weights are 1 versus 1/4.

The same true **physical** Sobolev source gate improves to

```text
||h_(p,t)^(k)||1 ≤ Σ_(j=0)^26 E_j*r^(-2j)||b_p^(k+2j)||1,
T_(b,sharp)=max(32768,16 max_(p∈{2,3};j=1..26)
   (208 E_j ||b_p^(2j)||1)^(1/(2j))).
```

For t≥T_(b,sharp), `||h_p||1≤1/4` exactly as before; `T_(b,sharp)≤T_(b,old)` in the same chosen bump family. No NUMERIC plateau derivative evaluation is claimed, so this is an improved **effective symbolic threshold** and mass bound, not a certified numeric cutoff. Original same-source target `d_W(a)≥c_*a⁴/r⁶`, admissible four port amplitudes `ε≤r^-5`, prime source O(r^-6), sharpened full added zero+Gamma O(r^-6 logt), and P0 strict gap all retain their previous statuses. **The geometric improvement does not cancel the logarithm or force a sign.** Agda/Lean source modules added on open draft PRs #1533/#116; no kernels or CI.
