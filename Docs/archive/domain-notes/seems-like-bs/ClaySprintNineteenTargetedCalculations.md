# Clay Sprint 19 Targeted Calculations

Sprint 19 moves from route compression to three targeted checks.

## Gate3

Target:

```text
PruningPreservesCumulativeFillDistance
```

ELI5: the full dot set covers the circle.  After pruning, prove the remaining
dots still cover it densely.

Worker result required:

```text
h_pruned(J) <= C / J^alpha
alpha > 0
```

If `alpha > 0`, the pruned union remains dense.  If `alpha` is approximately
zero, pruning killed density and the Gate3 Mosco route fails.

## Navier-Stokes

Target:

```text
DynamicBraidResidueDecayForNS with r * sqrt(2) < 1
```

ELI5: the bad vortex branch grows like `sqrt(2)` each scale.  Any deterministic
gate that shrinks it by a factor `r < 1/sqrt(2)` wins.

This generalizes the earlier `1/3` target.  `1/3` is strong, `2/3` still
closes, and `6/7` fails.  The approximate products are:

```text
(2/3) * sqrt(2) ~= 0.943
(6/7) * sqrt(2) ~= 1.212
```

The physical-stretching interface is still mandatory.  Decay without
`BraidResidueControlsPhysicalStretching` does not prove a PDE theorem.

## Yang-Mills

Target:

```text
eta_k <= beta_1loop(k) - 14.16373
```

ELI5: the one-loop forecast says when the glue becomes safe.  The tolerance
budget asks how wrong that forecast may be before the usable `rho <= 0.90`
margin fails.

The worker output is not a proof of Balaban.  It is a budget for the
nonperturbative theorem:

```text
ContinuumUniformRhoBound
ContinuumUniformLeakageBound
```

## Governance

No promotion follows from these calculations.  Gate3 can close only after
Mosco/no-pollution transfer.  NS can close only after physical residue control
and deterministic actual-flow depletion.  YM can close only after continuum
rho/leakage plus the constructive-QFT terminal stack.
