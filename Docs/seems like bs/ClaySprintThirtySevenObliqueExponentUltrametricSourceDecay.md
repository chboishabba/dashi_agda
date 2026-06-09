# Clay Sprint 37 Oblique Exponent and Ultrametric Source Decay

Sprint 37 quantifies the source decay required by the Sprint 36 transition
budget and records DASHI-native mechanisms that could supply it.  These are
mechanism candidates only.  The physical PDE bridge remains separate.

## Oblique Source Exponent

If:

```text
s_obl(K) <= C * 2^(-sigma*K)
```

then:

```text
2^(K/2) * s_obl(K) <= C * 2^((1/2 - sigma)K)
```

The weighted source is summable exactly when:

```text
sigma > 1/2
```

So the oblique refill must decay faster than the half-derivative tax.

## Power Source Transition

The sharpened transition condition is:

```text
R^+_(K+1) <= c * R^+_K + Csource * 2^(-sigma*K)
c * sqrt2 < 1
sigma > 1/2
```

Under those conditions:

```text
Sum_K 2^(K/2) * R^+_K < infinity
```

This is the analytic transition/source theorem to aim at.  It is no longer a
symbolic branch-counting claim.

## Kernel Decay Versus Concentration

If the oblique source has the form:

```text
s_obl(K) <= 2^(-mu*K) * concentration(K)^theta
```

and:

```text
concentration(K) <= C * 2^(beta*K)
```

then:

```text
s_obl(K) <= C' * 2^(-(mu - theta*beta)K)
```

Closure requires:

```text
mu - theta * beta > 1/2
```

So `NoAlignedMassConcentration` should be relative to the kernel decay, not
just `beta < 2` in isolation.

## 369 Cube Lineage

Use the 3-by-3-by-3 local cube as a source-decay input, not a proof by itself.

```text
badCubeFraction = N_bad / 27
```

If lineage-to-shell amplification is:

```text
A_K <= C_A * 2^(a*K)
```

then the cube lineage condition is:

```text
badCubeFraction < 2^(-(1/2 + a))
```

This is a falsification metric: count dangerous local cube states, estimate
amplification exponent `a`, and test the inequality.

## Braid Quotient Growth

Different dangerous-looking local words can represent the same physical state
after braid/Yang-Baxter quotienting.  If:

```text
|W_bad(K)| <= Lambda_bad^K
|W_all(K)| >= Lambda_all^K
```

then lineage decays when:

```text
Lambda_bad / Lambda_all < 2^(-(1/2 + a))
```

Again, this is a source-decay candidate.  It does not replace the PDE bridge.

## Ultrametric Source Decay

For a `p`-adic / BT tree source:

```text
s(K) <= C * p^(-eta*K)
```

the half-derivative is beaten when:

```text
eta > log_p(sqrt2)
```

Higher-prime lanes need weaker `eta`:

```text
p=2  -> eta > 0.5
p=3  -> eta > 0.3155
p=7  -> eta > 0.1781
p=71 -> eta > 0.0813
```

## Tetration Scale-Jump Guard

Tetration-scale language should be used as a jump-cost guard:

```text
cost(K -> L) >= c * d_BT(K,L)
```

Nonlocal jump source is summable if:

```text
jump cost > jump entropy + log sqrt2
```

The point is not large growth.  The point is that unaccounted scale jumps must
pay enough code-length / ultrametric cost to prevent an infinite bad lineage.

## Worker Lanes

```text
W1: estimate sigma_obl and test sigma_obl > 1/2
W2: estimate mu, beta, theta and test mu - theta*beta > 1/2
W3: count 369 cube bad states and braid quotient growth
W4: estimate ultrametric eta_p and scale-jump entropy/cost
W5: keep Q_K <= C R_K^+ separate; carry Gate3/YM false gates
W6: validate aggregate Agda and promotion flags
```

## Boundary

This sprint records source-exponent algebra and DASHI-native source-decay
candidate mechanisms only.  It does not prove `Q_K <= C R_K^+`, actual oblique
source decay, actual kernel/concentration bounds, ultrametric-braid source
decay for NS, Gate3 Mosco/no-pollution, YM nonperturbative uniformity,
Lean-port work, or any Clay promotion.
