# BSD P0 — original conductor-32 eta tail: explicit positive lower bound (21 Nov 2026)

## Target, original owners, and claim boundary

The ONLY selected curve in this note is the repository's **E: y²=x³−x**
(conductor 32, CM by Z[i]). The original owner
`DASHI/Mathematics/Arithmetic/EllipticCurveFrobeniusExact.agda`
and the exact S4 classical closure ledger
`Docs/roadmaps/ClayBSDOriginalLevel32S4ClassicalClosure20261116.md`
establish the source identity for the target. This is **not** the
distinct conductor-36 j=0 curve `y²=x³+1` studied by Lean #114.

The original existing Agda K4 owners are:
- `EllipticCMLevel32EtaNewmanArithmeticExact` (eta exponent conditions);
- `EllipticCMLevel32LigozatCuspArithmeticExact` (six exact cusp orders);
- `EllipticCMLevel32GenusOneArithmeticExact` (genus arithmetic);
- `EllipticCMNormalizedOneDimensionalQSeriesExact` (all-n equality GIVEN genuine 1D modular-form proportionality);
- `EllipticCMLevel32FrickeMellinExact` (Fricke and central Mellin algebra GIVEN authentic eta inversion / Mellin data).

**This note strengthens the existing CLASSICAL selected S4 tail lower bound
with a new explicit rational, uniform, elementary inequality.** It is a
mathematical deduction *conditional on the original classical Dedekind
eta infinite-product identity, the same-curve level-32 modularity, and
the same-curve Mellin formula*. It is not an Agda analytic eta proof,
does not close native K4, and makes no universal BSD claim.

## Exact nonnumerical positive tail argument

Let `t0=1/sqrt(32)=1/(4sqrt(2))` and `r(t)=exp(-8*pi*t)`.
On the original positive imaginary axis the genuine Dedekind eta
infinite-product identity implies

```text
f32(i t) = eta(4 i t)^2 eta(8 i t)^2
         = exp(-2*pi*t)
           * [product_(n>=1)(1-r(t)^n)]^2
           * [product_(n>=1)(1-r(t)^(2n))]^2 .
```

The elementary input `pi>3` and `sqrt(2)>7/5` gives
`pi sqrt(2)>21/5`. The exponential Taylor polynomial through
degree eight at **exactly** `x=21/5` is

```text
sum_(k=0)^8 (21/5)^k / k! = 16205908927 / 250000000
                          = 64 + 205908927/250000000 > 64 .
```

Using the standard `exp(x)>=sum_(k=0)^8 x^k/k!` for `x>0`
and strict monotonicity of exponential, this implies
`exp(pi sqrt(2))>64`.
Thus for EVERY `t>=t0`,
`0<r(t)<=exp(-pi sqrt(2))<1/64`.

For every finite nonnegative sequence with `a_i<=1`, the
elementary product/sum inequality
`product(1-a_i)>=1-sum(a_i)`
follows by induction, because the cross term is nonnegative.
Apply it to `r^n` and `r^(2n)`, and take the original genuine
convergent eta products to the limit. Then

```text
product_(n>=1)(1-r^n)    >= 1 - r/(1-r)     >= 62/63
product_(n>=1)(1-r^(2n)) >= 1 - r²/(1-r²)   >= 4094/4095 .
```

Both are **strictly positive**, with a constant independent of
the integration variable t. Therefore the original eta cusp form obeys

```text
f32(i t) >= C * exp(-2*pi*t),  t>=t0,
C = (62/63)^2 * (4094/4095)^2
  = 64428653584 / 66556260225
  > 0 .
```

Now use the already classical, ORIGINAL SAME-CURVE Mellin/Fricke
identity in the existing S4 closure ledger:

```text
L(E,1) = 4*pi * integral_(t0)^infinity f32(i t) dt
       >= 4*pi*C * integral_(t0)^infinity exp(-2*pi*t) dt
       = 2*C * exp(-2*pi*t0)
       = 2*C * exp(-pi/(2sqrt(2)))
       > 0 .
```

The lower bound is approximately **0.637588175627469**;
the original classical L-value in the S4 ledger is about
0.655514388573030. The former is a strict *analytic* lower
bound provided the authentic eta/newform/Mellin identities are in force,
not a numerical fit to the known central value.

## Proof receipt / exclusions

Local exact reference: `scripts/check_bsd_level32_original_positive_tail_bound_p0.py`.
It checks the rational Taylor certificate, rational C and finite
product inequality, plus positive-imaginary-axis numerical diagnostics.
The finite script does **not** prove the infinite eta or integral identity.

**Native P0 exact missing producer path:**
1. Instantiate the actual analytic Dedekind eta on a pinned complex/Bishop
   upper-half-plane carrier and prove its infinite-product/positivity
   identity, including the genuine uniform tail passage.
2. Apply the existing Newman/Ligozat arithmetic via authentic analytic
   modularity and the actual `dim S2(Gamma0(32))=1` theorem to the
   *original selected* E32 newform and normalized q-series.
3. Transport the *same* original elliptic L-function through
   Fricke/Mellin to the positive original eta tail; do not take this
   identity as a bare arbitrary `Set` label.
4. Run pinned Agda/Lean kernels and transitive axiom checks. Then
   separately pay the selected Kummer/MW/Sha and universal rank gates.

No code owner named R445, F19, K4, or any round number is itself a Clay
endpoint. Historical iterations are only evidence/producers against
these genuinely original source-specific proof obligations.


## 21 Nov 2026 — original E32 eight-coefficient STURM alternate endgame (local exact 16/16)
A new source-first alternative to the dimension-one q-series compiler is the **classical Sturm bound**, applied only to original E:y^2=x^3-x (level 32, weight 2, trivial character). The exact index [SL2(Z):Gamma0(32)]=32*(1+1/2)=48 gives Sturm cutoff floor(2*48/12)=8. From the genuine eta q-product identity, the first eight coefficients of eta(4z)^2 eta(8z)^2 are (1,0,0,0,-2,0,0,0). Independently, direct point counts on original E32 at good p=3,5,7 give a_p=(0,-2,0), and original additive p=2 has local Euler polynomial 1, so the selected curve's first eight coefficients agree. The false constant-unit normalized coefficient sequence agrees at a1 but fails at a5, so q1 alone never identifies the real curve. Local executable source: scripts/check_bsd_level32_sturm_shortcut.py (16 exact checks against SymPy).

**Steelman BIDI endpoint:** if the source actually constructs (a) original E32 newform as a weight-2 level-32 modular form of the correct character and normalizes its genuine analytic coefficients, (b) the original eta quotient as an analytic same-level holomorphic cusp form with the same character, and (c) an imported correctly instantiated Sturm theorem, these eight exact coefficients yield equality of ALL analytic Fourier coefficients without separately needing the genus-one/dimension-one proportionality route. This is an ALTERNATIVE coefficient proof after genuine modularity, not unconditional source admission, and it is NOT a statement that eight numerical point counts prove modularity. The original E32 L(E,s)↔Mellin/Fricke same-function identification, actual eta infinite product and analytic integration, Kummer/MW/Sha and universal BSD remain OPEN. No Agda/Lean kernel or CI receipt.


## 21 Nov 2026 — SOURCE CORRECTION: original E32 L-function and analytic eta already exist
The prior suggestion to CONSTRUCT an original conductor-32 elliptic L-function or all-n L-series is incorrect. Direct inspection of canonical dashi_lean4 main identifies these ACTUAL original source owners:

1. Synthesis/MillenniumBSDMathlibLFunctionWeld.lean, exact original Git blob 6a1f757e18de3a6f8c57940bbb125b1ad81957d3: cmWeierstrass : WeierstrassCurve ℚ is (0,0,0,-1,0), with discriminant 64; cmFormalLFunction := cmWeierstrass.LFunction, cmAllNCoefficient n := cmFormalLFunction n, cmLSeries s := cmWeierstrass.LSeries s. Genuine curve-level Mathlib objects, proven definitional equivalence and coefficient multiplicativity. The file states its actual missing good-prime source weld to explicit E(Fp) point counts.
2. Synthesis/MillenniumBSDFrobeniusPointCount.lean, original blob d83c4e9c0fbf0ac56e8bcf20f1c01530b9ece76f: original point-count coefficient a_p = - sum_x quadraticChar(x³-x), with p≡3 mod4 inert zero theorem. The equation to Mathlib cmWeierstrass.LFunction local factors remains an original same-source task.
3. Synthesis/MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact.lean, original blob 39a2d5010e8ffd382f916a8fe7db37a0067103d1: actual INFINITE Dedekind eta expression ModularForm.eta(4z)^2*ModularForm.eta(8z)^2, and source-written holomorphic/nonzero statements using Mathlib genuine eta theorems. Synthesis/MillenniumBSDCMLevel32ImaginaryAxisPositivityFromRealnessExact.lean, blob 20cd229f4c1976d5dd447f8ce35d54793e3eb854, source-writes real-axis positivity conditional on real eta factors. Their native Lean kernel was not checked in this audit.
4. Agda BirchSwinnertonDyerBoundary.EllipticLFunctionData has Set-valued semantics and is NOT the best available actual L implementation. Original Agda EllipticCMLevel32FrickeMellinExact already owns conditional Fricke/Mellin split algebra and must be reused.

Steelman BIDI reverse source path: literal original cmWeierstrass → literal Mathlib localEulerFactor/LFunction and all-n coefficients → exact original frobeniusCoefficient point-count connection including bad p=2 → original level32 eta analytic modularity at weight2 correct character → Sturm bound 8 on TWO authenticated modular forms → original same-L analytic Mellin/Fricke continuation and central value → rank-zero arithmetic inputs. The missing theorem is NOT the creation of any L-function or Dedekind eta. The first narrow exact source task is the localEulerFactor-to-original-frobeniusCoefficient correspondence; then same-object level32 modularity, central analytic continuation/Mellin and native kernel acceptance. A formal LSeries expression by itself does NOT establish convergence or central evaluation at s=1; no universal BSD claim. Do not accidentally substitute the conductor36 curve.


## 21 Nov 2026 — original Lean E32 local-polynomial ↔ point-count source BIDI (new Lean #115)
The original Mathlib owner was audited down to its literal `WeierstrassCurve.localPolynomial` reduction definition, NOT just PR descriptions. Lean #115 (https://github.com/chboishabba/dashi_lean4/pull/115), source at Synthesis/MillenniumBSDCMActualLocalEulerPointCountBidiExact.lean, uses the ORIGINAL main owner `cmWeierstrass.LFunction` and original `frobeniusCoefficient` to identify the same good local inverse Euler polynomial under exactly three original mathematical witnesses: (1) correct selected prime's minimal-model good reduction; (2) its residue-field cardinality equals rational p; (3) its reduced minimal-model point-group cardinality equals the original direct ZMod-p projective point count. Unlike arbitrary normalized q-series, this points to the actual Mathlib L-function. The additive p=2 factor 1 has its own explicit three negative reduction predicates; its actual original place proof remains OPEN. Global all-n Mathlib Euler multiplication, selected eta/newform modularity, central analytic continuation/Mellin, BSD arithmetic and universal BSD remain OPEN.

Lean #115 is a DRAFT. Its new source-written theorems have NOT been checked by the pinned Lean kernel. The **exact committed Python script** `scripts/check_bsd_e32_actual_lfunction_euler_weld.py` was independently reconstructed, executed under local SymPy 1.14.0, and its local Git blob matched the committed original `d4f69d16d7c5e8816488c85aa6d0daa9a790a9c5`. Result **163/163 PASS**: 30 odd good-prime inverse Euler polynomials, 128 full coefficients versus original eta product, p5 sign and bad-p2 negative controls. This is finite agreement only, not a Mathlib reduction or analytic theorem. Attribution: Mathlib original localPolynomial and global LFunction; DASHI original point-count owners; source-specific same-object adapter and regression are separate contributions. Do not rebuild LFunction/eta, substitute conductor36, or promote analytic endpoint.


## 21 Nov 2026 — Lean #115 literal E32 reduction geometry, not missing new L-function
Original mathematical owner remains dashi_lean4 main `Synthesis/MillenniumBSDMathlibLFunctionWeld.lean` (actual `cmWeierstrass.LFunction`, `cmAllNCoefficient`, `cmLSeries`) and `MillenniumBSDFrobeniusPointCount.lean` (actual E32 ZMod-p points). Lean DRAFT #115 new head 8fbf9c256090c820e307e7e953f67cb0d41bf803 now source-writes an ORIGINAL LITERAL same-coefficient ZMod-p reduction `cmOriginalLiteralModP`, the universal discriminant 64 and smooth/IsElliptic conclusion for ALL odd primes, the actual p=2 singular point (1,0) and exact cusp chart `F(1+u,v)=(v+u)^2+u^3`. This is an arithmetic improvement over finite-only normalized coefficients, but the module is still UNCOMPILED/UNACCEPTED. It is not a claim that Mathlib's chosen p-adic minimal model is already the literal reduction, nor that the original local Euler factor has been attached.

The EXACT GitHub source blob for the new Lean candidate is 78890cbf83180e12cc3bcf54f004a4ea6981af73 and the exact locally executed Python script blob is 9697492f6e4a2b0a0d36b5e69c560320f3ec8da5. Local SymPy: 115/115 exact checks across all 55 primes ≤257 (54 odd nonsingular, characteristic 2 one singular), original p2 chart, bad-Euler wrong-model control, and v2(64)=6. Prior source-exact 163/163 E32 q^128 coefficient regression also reexecuted. No Lean kernel/CI.

**Real next source payment (existing consumers, no duplicate L-series):** (i) original rational prime p → HeightOneSpectrum (𝓞 ℚ) identification and residue field equivalence to ZMod p; (ii) show Mathlib selected `(cmWeierstrass.baseChange K).minimal R` has reduction point group equivalent to the already-proved literal E32 field curve at odd p, using genuine minimality/coordinate-equivalence; (iii) certify p2 selected minimal additive reduction so Mathlib's actual polynomial is 1, not the naive singular-fibre good polynomial 1+2T²; (iv) only then propagate actual localEulerFactor to `cmFormalLFunction` global coefficients, original same-level eta/Sturm, analytic L/Mellin and arithmetic BSD. K1–K5/S6 remain OPEN.


## 22 Nov 2026 — RECOVERED existing Eisenstein bad-prime owners and BSD classical S4 closure
The user's recollected y²=x³-1 belongs to the broader Eisenstein j=0 family y²=x³-D discussed previously; the ORIGINAL implemented J+ curve is y²=x³+1 (j=0, CM Z[omega]), discriminant -432 with bad p=2 and p=3. The minus-one J- twist is a DISTINCT rational model. Do not conflate them with this original selected BSD E32 y²=x³-x (j=1728, CM Z[i]), discriminant 64, bad p=2 only; still less with original 4D Yang–Mills Wilson source. The shared C3 / spectral structures are mathematics/method donors, not isomorphisms of the curves or L-functions.

The repository ALREADY contains original J+ bad-prime Lean proofs: Integration/EisensteinJZeroBadPrimeTwoExact.lean (singular (0,1), 2 affine/3 naive-projective F2 points), Integration/EisensteinJZeroBadPrimeThreeExact.lean (singular (2,0), 3 affine/4 naive-projective F3 points), and Integration/EisensteinJZeroAllGoodPrimeLocalExact.lean (all p>3 split/inert local formulas). Agda original provenance owner DASHI/Mathematics/CrossPollination/EisensteinLeanSplitPrimeLocalClosureReceiptExact.agda explicitly has badPrimeEllipticLocalFactorsObserved=false: the literal singular-fibre facts are NOT a Neron/Kodaira result or proof of p2/p3 elliptic L-factors. Existing original BSD module DASHI/Mathematics/Arithmetic/EllipticCurveTwoTorsionAndBadPrimeExact.agda ALREADY records the delta=64=2^6 and E32 two-torsion/support; docs/bsd-agda-golden-k1-k5-maxcut-20261113.md records selected E32 at p2 Kodaira III and Tamagawa c2=2 as external/classical arithmetic, not kernel-certified Tate reduction.

***Classical S4 status correction:*** Docs/roadmaps/ClayBSDOriginalLevel32S4ClassicalClosure20261116.md already proves the specific E32 original L(E,1)>0 under the explicitly invoked established external modularity/eta/isogeny theorems, using the source-specific rational 2-isogeny E32 y²=x³-x → optimal 32.a4 y²=x³+4x. It identifies L(E,s)=L(E',s) INCLUDING the bad Euler factor by classical isogeny invariance and f32=eta(4z)^2 eta(8z)^2 via genuine 1D modularity, then gives a positive central Mellin tail. This is a classical SAME-CURVE selected analytic S4 result, not an Agda/Lean native theorem or universal BSD. Do not incorrectly describe the selected E32 analytic rank-zero result as mathematically unknown or rebuild it. Native Lean E32 LFunction-to-actual reduced point-count / minimal-model, analytic eta and positive Mellin formalization remain real proof obligations.

Lean #115 new head b23cd8d5966d8772e7a9d78251ca71304dbf7222 adds Synthesis/MillenniumBSDCMEisensteinBadPrimeLineageBidiExact.lean, importing/reusing the original J+ 2/3 bad-prime modules and original E32 smooth/Frobenius source with exact same-cardinality/different-reduction negative controls. The companion script scripts/check_bsd_eisenstein_three_curve_badprime_bidi.py passes 40/40 exact local SymPy assertions, blob c120571ac3474dd2f7f3e667a0f7d2797f3b34d5. On p=3 original E32 and J+ both have 4 naive projective points, while E32 is smooth/good and J+ is singular/bad. On good p=5 E32 a5=-2 versus J+ a5=0; on p=7 J+ and J- traces are -4 versus +4. Three source files exact Git readback 3/3. This is finite regression, NOT actual Mathlib p-adic minimal-model equation or kernel acceptance. Original K1,K2,K3,K5 and universal S6 remain OPEN.
