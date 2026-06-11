# Clay Sprint 38 Source Decay and Physical Bridge Audit

Sprint 38 consolidates the source-decay algebra and keeps the physical bridge
as the decisive NS gate.

## Polynomial Decay Fails

If the source decays only polynomially:

```text
source(K) <= C * K^(-p)
```

then:

```text
2^(K/2) * source(K)
```

still diverges for every `p > 0`.  Exponential or ultrametric decay is needed.

## Exponential Source Decay

If:

```text
source(K) <= C * 2^(-sigma*K)
```

then the weighted source closes only when:

```text
sigma > 1/2
```

The tail from `K0` onward is bounded by:

```text
C * 2^(-(sigma - 1/2)*K0)
  / (1 - 2^(-(sigma - 1/2)))
```

Near-critical `sigma` is technically enough but practically weak.

## Positive Transition With Source

The exact recurrence is:

```text
R^+_(K+1) <= c * R^+_K + C * 2^(-sigma*K)
```

It closes when:

```text
c * sqrt2 < 1
sigma > 1/2
```

Then:

```text
Sum_K 2^(K/2) * R^+_K < infinity
```

## Ultrametric Source Decay

If:

```text
source(K) <= C * p^(-eta*K)
```

then closure requires:

```text
eta > log_p(sqrt2)
```

Representative thresholds:

```text
p=2  -> eta > 0.5000
p=3  -> eta > 0.3155
p=7  -> eta > 0.1781
p=71 -> eta > 0.0813
```

This is the useful DASHI-native advantage: higher-prime lanes need weaker
ultrametric decay.

## Braid Lineage With Amplification

If:

```text
L^+_K <= C * rho^K
A_K   <= C_A * 2^(a*K)
```

then:

```text
Sum_K 2^(K/2) * A_K * L^+_K
```

closes when:

```text
rho * 2^(1/2 + a) < 1
```

Bad local-state counts only help if they imply this real lineage/source decay.

## Physical Bridge

All source-decay algebra remains conditional until the physical bridge is
proved:

```text
Q_K <= C * R_K^+
```

where:

```text
Q_K =
  |PhysicalShellStretching_K|
  / (2^(K/2) * D_K + epsilon)
```

Falsification ratio:

```text
C_K = Q_K / (R_K^+ + epsilon)
```

Pass:

```text
sup_K C_K < infinity
```

Fail:

```text
C_K -> infinity
```

## Worker Lanes

```text
W1: prove/falsify Q_K <= C R_K^+
W2: estimate sigma for actual source_K
W3: estimate ultrametric eta and braid-lineage amplification
W4: estimate M_(+,+), concentration, and persistence thresholds
W5: carry Gate3 Mosco and YM rho/leakage as separate false gates
W6: validate aggregate Agda and promotion flags
```

## Boundary

This sprint closes source-decay algebra only.  It does not prove the physical
stretching bridge, actual source decay for NS, no positive replenishment,
non-Beltrami tube non-persistence, Gate3 Mosco/no-pollution, YM
nonperturbative uniformity, Lean-port work, or any Clay promotion.
