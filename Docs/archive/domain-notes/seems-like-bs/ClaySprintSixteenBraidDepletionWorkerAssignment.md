# Clay Sprint 16 Braid-Depletion Worker Assignment

Sprint 16 consumes the conditional braid-depletion calculation and assigns
six workers to the remaining state-changing surfaces.

Workers:

- W1 carrier count: count admissible trit-braid loops and unbalanced
  expansive loops per shell.
- W2 transition decay: test or prove
  `Residue(K+1) <= (1/3) * Residue(K)` on the carrier transition rule.
- W3 deterministic promotion guard: the conditional correlation theorem is
  recorded, but deterministic Navier-Stokes promotion still requires
  `CoherentTubeFormation`.
- W4 coherent tube formation: prove or kill repeated bad-branch selection by
  coherent vortex tubes.
- W5 Gate3 continuation: continue `MoscoRecoveryFromPrunedUnionDensity`.
- W6 YM continuation and governance: continue `ContinuumUniformRhoBound` and
  `ContinuumUniformLeakageBound`, while auditing all promotion flags.

The exact next high-alpha computation is:

```text
BraidResidue369(K) <= C * r^K
check whether r * sqrt(2) < 1 along actual NS trajectories
```

All promotion flags remain false.
