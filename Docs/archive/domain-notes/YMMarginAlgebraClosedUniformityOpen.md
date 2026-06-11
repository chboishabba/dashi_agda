# YM Margin Algebra Closed, Uniformity Open

Sprint 10 separates the closed Yang-Mills margin algebra from the still-open
constructive-QFT theorem.

For

```text
m(beta) = beta * c_min - a - log(2p)
rho(beta) = exp(-m(beta))
```

with `p = 7`, `c_min = 0.198`, and `a = 0.06`, the usable targets are:

```text
beta >= 14.1637  => rho <= 0.90
beta >= 15.0845  => rho <= 0.75
```

This algebra is closed as a receipt-level target.  It does not imply the
nonperturbative Balaban theorem.  The live blockers are:

```text
BetaForTargetRho:
  rho* < 1 ->
  beta >= (a + log(2p) - log rho*) / c_min ->
  exp(-(beta*c_min - a - log(2p))) <= rho*
```

The Agda receipt records this under `betaForTargetRho` and marks the margin
algebra as proved bookkeeping.

```text
YMNonperturbativeRGMonotonicity
ContinuumUniformRhoBound
ContinuumUniformLeakageBound
```

One-loop running remains diagnostic only.  `clayYangMillsPromoted` remains
false until uniform Balaban control, Shimura-to-flat universality,
self-adjoint Hamiltonian construction, mass-gap survival, OS/Wightman
reconstruction, and nontrivial SU3 are all inhabited.
