# Gate3 Depth-Decoupled Frame

Companion to:

```text
DASHI/Physics/Closure/Gate3DepthDecoupledFrameReceipt.agda
```

Sprint 8 sharpens the Gate3 obstruction.  The Archimedean frame collapse is
not primarily caused by poor angular density inside a fixed BT level.  It is
caused by cross-level depth coupling: for the flat Gaussian depth coordinate,
adjacent levels at the same angle can have Gram entry about `0.758`.

The depth axis saturates after roughly two decorrelated levels, while the BT
tree has seven tested levels.  The fix recorded here is a block-diagonal
depth kernel:

```text
G_depth(i,j) = delta(depth_i, depth_j)
```

Under that kernel, the Gram is a direct sum of levelwise angular Grams.  With
geometric angular pruning at `min_sep = 0.12`, the tested levelwise lower
bounds remain positive, with the recorded certificate:

```text
A_j >= 1e-4
covering_radius_j <= 0.115
level 7 retained density ~= 14 percent
```

## Live Blocker

The live Gate3 support blocker is now:

```text
MoscoDensityFromBoundedCovering
```

Finite levelwise positivity is not the same as continuum density.  The next
functional-analysis question is whether bounded levelwise covering radius plus
positive retained density gives a Mosco recovery sequence in `H_continuum`.

## Boundary

This receipt records the depth-coupling diagnosis and levelwise
depth-decoupled frame positivity.  It does not prove Mosco density, no
spectral pollution, Gate3 closure, or Clay.

