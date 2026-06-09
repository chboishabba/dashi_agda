# Clay Sprint 17 Analytic Residue Worker Assignment

Sprint 17 assigns workers to the stricter analytic-residue interface.

Workers:

- W1 residue functional: define `BraidResidue369(K)` as a functional of
  `u`, `omega`, and `p`.
- W2 physical stretching control: prove or kill
  `BraidResidueControlsPhysicalStretching`.
- W3 deterministic decay: prove or kill
  `BraidResidue369_K <= C * 3^-K` for actual NS trajectories.
- W4 coherent tube adversary: prove or kill repeated bad-branch selection by
  coherent vortex tubes.
- W5 Leray/supervoxel enforcement: prove or kill whether Leray projection and
  incompressibility enforce the trit/supervoxel cancellation law.
- W6 transfer/governance: if the above only holds for carrier data, prove or
  kill density/stability transfer and audit all promotion flags.

The follow-on braid-correlation frontier consumes this assignment into the
sharper threshold:

```text
BraidResidue369(K) <= C * r^K
r * sqrt(2) < 1
```

The next six frontier workers are:

- W1 coherent tubes: prove or kill `CoherentTubeFormation`.
- W2 extra suppression: prove or kill a second mechanism that improves the
  insufficient BT `(6/7)^K` rate.
- W3 shared transfer: prove or kill
  `HyperbolicShimuraToEuclideanUniversality`.
- W4 Gate3 typing: type the structurally complete Mosco/no-pollution proof.
- W5 YM uniformity: attack `ContinuumUniformRhoBound` and
  `ContinuumUniformLeakageBound`.
- W6 governance: audit all promotion flags.

The single current NS Clay-facing stack is:

```text
BraidResidueControlsPhysicalStretching
+ DynamicBraidResidueDecayForNS
=> SubcriticalVortexStretchingAbsorption
=> PointwiseEnstrophyControl
=> no blowup
```

All promotion flags remain false.
