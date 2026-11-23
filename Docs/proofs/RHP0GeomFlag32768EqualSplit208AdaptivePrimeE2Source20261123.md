# RH P0 — 32768 is an ORIGINAL geometric flag; 208:26 is E2 budget bookkeeping; exact adaptive prime ports (23 Nov 2026)

**Scope and trust.** Original selected `W(t)`, original `r=t/16`, real-even original Zeta23 Weil two-prime source and the native RH/G2 q-tail. This is mathematical analytic proof, exact locally executed Python `fractions.Fraction`/SymPy regression and source-written Agda/Lean only. **No Lean/Agda kernel compilation, no GitHub CI, no RH/GRH claim.** It improves **P0 E2 local physical target/port admissibility**, not full off-ordinate signed P0 or E3.

## 1. Recover two distinct original meanings of 32768

**Original geometric flag**: `DASHI/Analysis/RHQuartic163840DyadicTailHXIntertwinerExact.agda` imports `NonArchimedeanMonster3BActionSeparationExact` and the exact fifteen-bit capacity. The RH source's sixth-power tail is

```text
q>8, v=(8/q)^5∈(0,1), dv=−5*8^5*q^-6 dq;
8^5=2^15=32768, ∫_8^∞q^-6 dq =1/(5*32768)=1/163840.
v=(k+θ)/32768, k∈{0,...,32767}, θ∈[0,1).
```

This is an **exact reversible continuous measure chart** only WITH the residual θ. Original source also has a distinct order-32768 odd-residue ×3 action at n=17; these agree as integers but are not thereby the same action, and neither is Monster 3B's order-three element.

**Prior RH E2 cutoff**: the formerly used `t≥32768` in the selected-W fourth-moment floor was merely a conservative proof convenience: `r=t/16≥2048`, then use `cosh(5/(2r))<2` to get one rational c. There was no mathematical source requiring the dyadic tail **capacity** to be used as the **height** cutoff. Preserve the geometric flag, but separate the analytic inequality.

## 2. 208:26 and original punctured-27 signed geometry

The source-native `Punctured27NineSheetBridgeExact` counts 9+8+9=26 oriented non-origin sites; `IbrahimTernary27OriginTraceless26AlbertShapeBidiExact` already owns 27=1+26; `HyperfabricPunctured27Projective13OrientationExact` retains 13×sign. The normalized RH operator has degree26 in D² and 27 coefficients. Its majorant factor slots are 9 weight1, eight pole weights in four antipodal pairs, and 9 weight1/4. This is a CHOSEN native **index chart**, not an actual Jordan/F4 representation.

The old `208=26×8` had the distinct **analytic** derivation:

```text
choose bump support halfwidth δ=1/32,
||b_p||1<=4δ=1/8,
choose mass cap ||h_p||1<=1/4,
unused allowance=1/4−1/8=1/8,
split across 26 positive nonconstant terms:
      each term<=1/(8*26)=1/208.
```

That budget is **not geometrically forced**. Change δ to 1/64: equal-split reciprocal becomes 416/3, not 208. Using the actual convolution bump below with mass3/32, it would instead be 832/5. The equality `208=26*(3²−1)` is an exact **cross-carrier arithmetic compatibility**, but there is NO native action/analytic theorem identifying the central punctured eight sites with bump-mass reciprocal. A true same-action intertwiner is unpaid. The equal-share rule can simply be eliminated.

## 3. An EXPLICIT C∞ fixed-width flat-top, with every derivative norm certified

Use the canonical rational widths:

```text
a=3/128, b=1/128, δ=a+b=1/32.
For n>=1 define h_n=b/(2n²)=1/(256n²).
K_n(u)=1/(2h_n) 1_{[-h_n,h_n]}(u).
η=K_1*K_2*... (infinite centered probability convolution).
B(u)=1_{[-a,a]}*η(u).
b_p(u)=B(u−log p)+B(u+log p), p=2,3.
```

Because `Σ_{n≥1}1/n²≤2`, `Σh_n≤b`; η is a compact supported probability distribution. For each fixed integer m, differentiate m distinct box factors distributionally and use total variation `||K_n'||_{TV}=1/h_n=256n²`. Convolving the remaining probability kernels gives

```text
||η^(m)||1 ≤ Π_(n=1..m)256n² =256^m(m!)².
```

Taking arbitrarily many remaining smoothing kernels establishes C∞; absolute continuity and the uniform derivative L1 bounds persist in the compact-convolution limit. Differentiate the two interval indicators only ONCE to gain the stronger bound for m≥1:

```text
||b_p^(m)||1 ≤ 4||η^(m−1)||1
              ≤ 4*256^(m−1)*((m−1)!)².
```

Moreover the signed reflected intervals are disjoint, η has unit mass, and the geometric support/plateau are exact:

```text
supp b_p within ±log p plus radius1/32,
b_p≡1 on radius1/64 of its prime centres,
||b_p||1=4a=3/32.
```

This explicitly supplies finite, **rational** upper bounds through derivative order 52 for the original source normalized even differential operator. No undocumented Gevrey constants, SVD numerical rank, or unknown B_(p,2j) is left. This is a mathematical C∞ convolution construction; the infinite-convolution and formal-adjoint lift are not yet Lean/Agda kernel theorems.

## 4. Source-geometric coefficient polynomial replaces every 1/208 allocation

Retain the exact SHARP original 26-slot coefficient envelope from [punctured-27 source](RHP0Punctured27GeometricAnnihilatorCoefficientEnvelope20261123.md):

```text
E(z)=(1+z)^9(1+z/4)^9 Π_{k=14,15,17,18}(1+z/k²)^2
    =Σ_{j=0}^{26} E_j z^j.
Q_t(D)=Σ q_j(t)D^(2j), 0≤q_j(t)≤E_j/r^(2j), r=t/16.
```

For either p the original exact projection `h_{p,t}=Q_t(D)b_p` satisfies all eight source integral orthogonality constraints and has **EXACT** prime-point value1 at its own ±logp and zero at the other prime/power. The entire physical L1 bound is now ONE known positive polynomial:

```text
H(r)=3/32 + Σ_{j=1}^{26}
    [ 4 E_j 256^(2j−1) ((2j−1)!)² ]/r^(2j),

||h_{p,t}||1 ≤ H(r).
```

Every nonconstant coefficient is positive, so H(r) is **strictly decreasing** in r>0, and `lim_{r→∞}H(r)=3/32`. No equal error splitting. Exact rational evaluation shows

```text
H(31829)>1/4, H(31830)<=1/4, H(32768)<1/7.
```

So the earlier unknown `T_b` is superseded by an ACTUAL proven sufficient **integer radius** r≥31830 (t≥509280) for `||h_p||1≤1/4`, with **r=32768 (t=524288)** an optional dyadic-geometric audit checkpoint. The first inequality does not claim a necessary threshold for true ||h||: it is the integer crossing of this conservative *majorant* H(r).

## 5. Original selected-W target floor: eliminate the artificial t≥32768 condition

On the ORIGINAL selected witness, normalized `||P_W||1<5184`, `supp P_W⊂(-5,5)`, `M0=M2=0`, `M4=−4T_W`, `T_W>567/1600`. With `r=t/16` and `|a|≤1/2`,

```text
d_W(a)=T_W a^4/(24r^6)+R_6,
|R_6| <= 28125 cosh(5|a|/r)|a|^6/r^8.
```

At t≥200 (r≥12.5), `5/(2r)≤1/5<1` and elementary nonnegative series gives `cosh x≤1+x²` for |x|≤1. Using `a²≤1/4`:

```text
d_W(a)≥[c(r)/r^6]a^4,
c(r)=567/(1600·24) − (28125/(4r²))·(1+25/(4r²)).
```

This is an exact rational rational-function estimate and c(r) increases with r. The equation `c(r)=1/100`, x=r², is

```text
61x²−90000000x−562500000=0,
sqrt(x_positive)≈1214.6670679816334.
```

Therefore **for all t≥19440** (integer r≥1215), `d_W(a)>a^4/(100r^6)` on EVERY `0<|a|≤1/2`. It fails this particular 1/100 sufficient certificate at integer r=1214. This replaces the former **t≥32768** proof convenience; it does NOT replace the distinct source dyadic **capacity 32768**.

## 6. NO plateau-height restriction: an adaptive exact four-prime-port amplitude

Existing true source bounds `||G_H||1,||G_T||1≤83/30`, `|poleHalf|,|poleTwo|<32`, the true frozen on-line bracket `|B_g(u)|≤2(83/30)/r`, `|u|≤5/4` and `cosh(|u|/2)<2` imply for all t≥200:

```text
C_i = (4·10!)^-1 ∫ |P_i(u)| |u|^10 cosh(|u|/2)du
    ≤ K H(r)/r,
K=4·(83/30)·32·(5/4)^10/10!
  =6484375/7134511104 < 1/1000.
```

No assumption `H≤1/4` is needed. At every height **t≥19440**, choose each of four independently signed port coefficients as

```text
ε_i(t) = κ_i/[r^5(1+H(r))],  |κ_i|≤1.
```

Then the full independent physical target gate follows **uniformly**, using c(r)>1/100:

```text
Σ_i |ε_i| C_i
 ≤ [4K H(r)/(1+H(r))]/r^6
 < 4K/r^6 < (64/100)/r^6 <64 m_W.
```

This is the original selected-W full-strip target-positivity condition; all M0/M2/M4/M6/M8 and both pole coordinates stay exactly frozen. Crucially, `H(r)→3/32` so `ε_i(t)/[κ_i r^-5]→32/35`; no exponent loss asymptotically. At finite moderate heights the attenuation may be tiny due to the very conservative high-derivative bound and yields no all-height positive prime coefficient floor.

If one insists on unattenuated `|ε_i|≤r^-5`, a direct positivity admission using the **true c(r)** is `4K H(r)<64c(r)`; exact integer tests give FALSE at r=26870, TRUE at r=26871. Since LHS decreases and RHS increases, this **sufficient** source condition holds for all r≥26871, i.e. **t≥429936**, earlier than the mass cap H≤1/4 at t≥509280. Again, no claim about minimal possible perturbation or optimal constant beyond this analytic envelope.

## 7. Mandatory P0 scope, next acceptance

**Paid mathematically:** actual 32768 dyadic flag is preserved; 208:26 dissected; explicit source-native continuous plateau and ALL derivative norms up to52; actual 26-slot geometric polynomial replaces equal-splitting; true source m_W floor t≥19440; strict *local* target preservation with adaptive four-port amplitude for all such t; explicit unattenuated and norm thresholds.

**Unpaid:** Mathlib/Agda kernel construction of infinite-convolution flat-top and full 52-fold integration by parts, Lean source frozen pair inhabitation, native original FarExact/Schwartz/post-sixth E2 total across **actual zeros and Gamma**, and E3 an INDEPENDENT strict completed signed zero/Gamma/prime upper estimate uniformly in off-line displacement and near-double prime phase resonance. Previous `|ΔZero|+|ΔGamma|=O(r^-6 logt)` remains; no source-coherent log removal or negativity follows from the adaptive local budget. RH and GRH OPEN, no CI.

**Exact executed source:** [full local script](../../scripts/check_rh_p0_geomflag_208_adaptive_e2_20261123.py), reproducible compact committed regression on [DASHI RH PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533); `DASHI/Analysis/RHPrimeAperturePuncturedFactorChartExact.agda` updated to import the original dyadic owner rather than recoding capacity. The script's rational P0 gates were executed locally; Lean/Agda compiler/kernel tests were not.
