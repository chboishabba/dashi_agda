# Retained stage tree, signed 3/6/9 profile, and finite Euler selector

This continuation keeps the local constituent chart and the global balanced-radix chart simultaneously.

## Stage 5 is not destructive

The retained state is

```text
lower constituent = +++
upper constituent = ++0
joined amplitude  = 5
balanced address  = 1 -1 -1
visible ancestor  = 3
residual child    = ++0.
```

The visible `5 -> 3` map is therefore a coarse retraction. A theorem rejects the claim that the residual child is `none`.

Stage 6 is represented in both charts:

```text
local chart = +++ joined with +++
global balanced address = 1 -1 0.
```

## Signed closure profile

The profile retains residues and orientation relative to the three closure scales.

For stage 5:

```text
mod 3/6/9 = 2,5,5
relative to 3 = past by 2
relative to 6 = before by 1
relative to 9 = before by 4.
```

For stage 6:

```text
relative to 3 = past by 3
relative to 6 = exactly closed
relative to 9 = before by 3.
```

The existing shared balanced-ternary prefix theorem connects the two radix addresses.

## Depth-two nonary complement

A typed certificate proves

```text
81 = 9^2,
10 = 9 + 1,
10 + 71 = 81.
```

The value `71` is connected to the repository's existing `p71` Ogg lane. The implementation does not claim an invariant `71`-element complement or a module exact sequence; those require an action-preserving carrier decomposition.

## Constrained Euler selector

The existing finite MDL frame selector is recast as

```text
minimise total frame cost
subject to ClosesThreeAt(frame).
```

The compact frame carries the actual closure witness and the existing natural-number minimality theorem. A finite first variation is the endpoint cost minus the selected cost. Every admissible cost-preserving deformation has first variation zero. This is the exact discrete Euler-stationarity statement available on the finite frame carrier; it is not a differentiable continuum frame manifold and does not turn local coherence into universal truth.

## Validation

```bash
bash scripts/check_stage_euler_tree_complement_round2.sh
```

No Agda-kernel or Actions success is asserted until observed.
