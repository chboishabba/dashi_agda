# Clay Sprint 35 No-Coherence-Replenishment Audit

Sprint 35 records the forced red-bucket version of the NS route.  High-shell
direction mixing can look strong in the frozen/coercive model, but full
Navier-Stokes can still fail if nonlinear transfer replenishes coherent
non-Beltrami alignment.

## Forced Red Bucket

The actual residue is not just a free-decay quantity.  It has the form:

```text
d/dt R_K^+ <= - gamma_K * R_K^+ + F_K
```

where:

```text
gamma_K = high-shell direction mixing / depletion rate
F_K     = nonlinear replenishment into the coherent non-Beltrami red branch
```

If replenishment is relative to the current red mass:

```text
F_K <= eta_K * R_K^+
```

then:

```text
d/dt R_K^+ <= - (gamma_K - eta_K) * R_K^+
```

The half-derivative loss is beaten when:

```text
2 * (gamma_K - eta_K) * T_nl > log sqrt2
```

Equivalently:

```text
eta_K < gamma_K - log(sqrt2) / (2 * T_nl)
```

This is the replenishment tolerance.  It is a conditional calculus/order
surface, not a proof that actual NS satisfies the bound.

## Subquadratic Strain

The conditional high-shell coercivity surface is:

```text
2 * nu * 4^K >= lambda_1_max(K)
```

If:

```text
lambda_1_max(K) <= C * 2^(alpha*K)
alpha < 2
```

then viscosity eventually dominates the strain growth:

```text
2 * nu * 4^K >= lambda_1_max(K)
```

This is closeable as an order lemma.  The open PDE audit is whether actual NS
traces satisfy a subquadratic high-shell strain-growth exponent.

## Replenishment Functional

The functional to test is:

```text
F_K =
  ||Pi_danger Pi_perp^xi
    P_K[(u dot grad)omega - (omega dot grad)u]||_2
  / (||omega_K||_2^2 + epsilon)
```

`Pi_danger` projects into the coherent + non-Beltrami + not
pressure-decorrelated branch.

Pass condition:

```text
F_K < eta_K^max
```

Fail condition:

```text
F_K >= eta_K^max
```

or persistent red-branch survival:

```text
rho_K = R^+_(K+1) / (R^+_K + epsilon) >= 1 / sqrt(2)
```

## Concentration Blocker

Average direction mixing can miss a tiny intense coherent tube unless aligned
mass concentration is controlled.

The needed condition is:

```text
sup_x |omega_K|^2 / (||omega_K||_2^2 + epsilon)
  <= C * 2^(beta*K)

beta < 2
```

Plain Bernstein in 3D gives only `beta = 3`, so it is too weak.  This is an
actual open blocker, not a closed micro-lemma.

## Worker Lanes

```text
W1: define and estimate the replenishment functional F_K
W2: compare F_K against eta_K^max
W3: estimate concentration exponent beta
W4: estimate strain growth exponent alpha and high-shell coercivity
W5: maintain the conditional absorption chain from F_K, beta, and rho_K
W6: validate aggregate Agda and keep all promotion flags false
```

## Carry-Forward

Gate3:

```text
power-law density is carried forward
Mosco/no-pollution remains open
```

Yang-Mills:

```text
safe-scale correction budget is carried forward
k >= 67 remains the first sensible diagnostic target
nonperturbative rho/leakage remains open
```

## Boundary

This sprint records conditional calculus/order surfaces and audit targets only.
It does not prove `Q_K <= C R_K^+`, no coherence replenishment, no aligned-mass
concentration, actual dynamic residue decay, Gate3 Mosco/no-pollution, YM
nonperturbative uniformity, Lean-port work, or any Clay promotion.
