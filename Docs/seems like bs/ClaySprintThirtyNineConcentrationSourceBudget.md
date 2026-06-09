# Clay Sprint 39 Concentration Source Budget

Sprint 39 combines braid/angular depletion, BT ultrametric decay, and aligned
mass concentration into one source-budget inequality.

## Master Inequality

Let:

```text
gamma = braid / angular / cube depletion
eta   = BT ultrametric decay exponent
beta  = aligned concentration exponent
theta = concentration power in the physical bridge/source bound
p     = prime lane
```

Assume:

```text
source(K)
  <= C * 2^(-gamma*K)
       * p^(-eta*K)
       * 2^(theta*beta*K)
```

Since:

```text
p^(-eta*K) = 2^(-eta*log_2(p)*K)
```

the weighted source satisfies:

```text
2^(K/2) * source(K)
  <= C * 2^((1/2 - gamma + theta*beta - eta*log_2(p))*K)
```

So closure requires:

```text
gamma + eta*log_2(p) - theta*beta > 1/2
```

This is the concentration-adjusted source budget.

## Special Cases

Pure source exponent:

```text
eta = 0
beta = 0
need gamma > 1/2
```

Pure ultrametric source:

```text
gamma = 0
beta = 0
need eta > log_p(sqrt2)
```

With concentration:

```text
need more gamma or eta to pay for theta*beta
```

## Concentration-Aware Physical Bridge

The bridge can be weakened from:

```text
Q_K <= C * R_K^+
```

to:

```text
Q_K <= C * R_K^+ * concentration_K^theta
```

but then the source budget must pay the concentration cost:

```text
gamma + eta*log_2(p) - theta*beta > 1/2
```

This is more realistic than pretending concentration has no effect.

## Aligned Mass Concentration

Define an aligned concentration exponent:

```text
alignedConcentration(K) <= C * 2^(beta*K)
```

Concentration is now a first-class gate.  Large `beta` can defeat otherwise
good source decay.

## Diagnostics

For each shell:

```text
K
R^+_K
Q_K
adjusted C_K = Q_K / (R^+_K * concentration_K^theta + epsilon)
alignedConcentration_K
beta_K = log_2(alignedConcentration_K) / K
gamma_K
eta_K
budget_K = gamma_K + eta_K*log_2(p) - theta*beta_K
```

Pass:

```text
budget_K > 1/2 uniformly at high K
adjusted C_K bounded
```

Fail:

```text
budget_K <= 1/2
adjusted C_K unbounded
```

## Worker Lanes

```text
W1: prove/falsify concentration-aware bridge
W2: estimate aligned concentration exponent beta
W3: estimate gamma, eta, and high-shell budget_K
W4: connect budget failure to replenishment / coherent tube persistence
W5: carry Gate3 Mosco and YM rho/leakage as separate false gates
W6: validate aggregate Agda and promotion flags
```

## Boundary

This sprint closes only the concentration-adjusted source-budget algebra.  It
does not prove the concentration bound, the concentration-aware physical
bridge, actual gamma/eta/beta estimates for NS, no positive replenishment,
non-Beltrami tube non-persistence, Gate3 Mosco/no-pollution, YM
nonperturbative uniformity, Lean-port work, or any Clay promotion.
