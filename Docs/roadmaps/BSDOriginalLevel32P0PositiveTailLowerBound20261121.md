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
