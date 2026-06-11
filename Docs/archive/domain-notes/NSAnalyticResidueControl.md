# NS Analytic Residue Control

Sprint 17 tightens the NS braid-depletion route.

The prior conditional receipt is not strong enough by itself: decay of a
combinatorial residue does not matter unless that residue controls physical
vortex stretching.

The live analytic interface is:

```text
BraidResidueControlsPhysicalStretching:
  |PhysicalShellStretching_K|
    <= C * BraidResidue369_K
       * 2^(K/2)
       * DissipationShell_K
```

Then, and only then, the residue decay

```text
BraidResidue369_K <= C * 3^-K
```

produces the useful physical bound:

```text
|PhysicalShellStretching_K|
  <= C * (sqrt(2)/3)^K * DissipationShell_K
```

The current frontier receipt generalizes the decay target.  Any residue
correlation base `r` is sufficient if:

```text
r * sqrt(2) < 1
```

It records DNS-like `(2/3)^K` as sufficient and BT `(6/7)^K` as insufficient
without another suppression mechanism.  The remaining NS terminal is therefore
`CoherentTubeFormation`, not another combinatorial branch-count receipt.

The receipt records five audit questions:

1. What is `BraidResidue369(K)` as a functional of `u`, `omega`, and `p`?
2. Does it reconstruct or bound actual physical shell stretching?
3. Why must every NS trajectory lose a factor `1/3` per shell?
4. Can a coherent vortex tube choose the bad branch repeatedly?
5. Does Leray projection enforce trit cancellation, or is it imposed
   externally?

All five remain theorem obligations.  Branch counting, trit signs, BT
adjacency, and supervoxel trace rules are not enough unless they become
deterministic analytic inequalities for arbitrary smooth divergence-free
Navier-Stokes data.
