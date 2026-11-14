# BSD K4: explicit constructive positive-tail and modulus — 14 November 2026

**Source**: original conductor-32 curve E: y²=x³−x; selected candidate
newform f32(τ)=η(4τ)²η(8τ)², Agda PR #1500. **Authority**: finite
Bernoulli product induction and exact geometric sums. The companion
Python certificate is *exact rational regression*, NOT an Agda proof.
Original Bishop Dedekind eta, Newman/Ligozat analyticity,
the level-32 dimension theorem, selected E modularity and Mellin
identification remain distinct source-proof obligations.

## Elementary uniform estimate

Put t0=1/√32 and q(t)=exp(−8πt), t≥t0. Since
8πt0=π√2>4 (π>3 and √2>4/3) and e>2,
0<q(t)<e^(−4)<1/16. Write

  P_N(t) = product_(n=1)^N (1−q(t)^n)²(1−q(t)^(2n))².

**Lemma 1 (finite Bernoulli product).** If 0≤a_i≤1 then
0≤product_i(1−a_i)≤1 and product_i(1−a_i)≥1−sum_i a_i.
Proof by finite induction: if P≥1−S and 0≤P≤1 then
P(1−a)=P−Pa≥P−a≥1−S−a. No infinite-series assumption.

**Lemma 2 (uniform positivity, all N, all t≥t0).**
Applying Lemma 1 to q^n,q^n,q^(2n),q^(2n), then bounding both
geometric sums by q≤1/16 gives

  P_N(t) ≥ 1−2sum_(n≥1)q^n−2sum_(n≥1)q^(2n)
         ≥ 1−2/15−2/255 = 73/85 > 0.

This is a uniform bound, not sampled numerical positivity.

**Lemma 3 (explicit Bishop-compatible Cauchy modulus).**
For all M>N≥0, 0≤P_N(t)−P_M(t)≤delta_N, where

  delta_N =
      2(1/16)^(N+1)/(1−1/16)
    + 2(1/16)^(2N+2)/(1−(1/16)²).

Proof: P_M=P_N R with 0≤P_N≤1; by Lemma 1,
0≤P_N−P_M=P_N(1−R)≤1−R≤sum_tail a_i≤delta_N.
The delta_N geometric limit is zero with an explicit
modulus. Hence (P_N) converges uniformly and constructively
on t≥t0, and 73/85≤P_infinity(t)≤1. The actual
Bishop-real realization/limit transport is a separate
Agda implementation gate, not supplied by this prose proof.

## Quantitative central-value bound, with explicit dependencies

If an actual same-object Bishop eta theorem establishes

  f32(it)=exp(−2πt) P_infinity(t)

and the selected curve's actual Fricke + Mellin theorem establishes

  L(E,1)=4π integral_(t0)^infinity f32(it) dt,

then

  L(E,1) ≥ 4π(73/85) integral_(t0)^infinity exp(−2πt)dt
         = (146/85) exp(−2π/√32) > 0.

This is a symbolic positive bound **conditional on the two
actual analytic identifications**. It is not an unconditional
Agda statement that the original L-function is nonzero.

An exact integral-tail error modulus also follows:

  0 ≤ 4π integral_(t0)^infinity
        exp(−2πt)(P_N(t)−P_infinity(t))dt
    ≤ 2 exp(−2πt0) delta_N.

## Remaining exact K4 source-proofs

1. Formalize the ordered-field Bernoulli/geometric induction
   over the genuine original Bishop real setoid, using the
   actual exponential t↦exp(−8πt).
2. Construct the actual analytic Dedekind-eta product and
   invoke the uniform delta_N modulus for convergence.
3. Prove actual analytic eta inversion and Fricke at level 32.
4. Admit Newman/Ligozat cusp and dim S2(Gamma0(32))=1
   on the genuine modular form carrier, with E modularity.
5. Establish original Bishop Mellin equality L(E,1)=tail integral,
   and Agda 2.9 kernel-check all transported declarations.
6. K1–K3 and K5 remain untouched; universal BSD is open.

## Reproduction / acceptance boundary

  python3 scripts/check_bsd_level32_positive_tail.py --n 10
  python3 scripts/test_bsd_level32_positive_tail.py

These commands establish exact rational constants and finite
regression/negative controls. They do not kernel-check the
analytic theorems or promote any Clay BSD endpoint.
