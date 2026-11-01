# Gate3 Phase-Completeness Reduction

This note isolates what the Monster/T7/zeta7 material contributes to Gate3.
It does not prove the Gate3 spectral gap.  It states a necessary-condition
reduction for the atom frame.

## Reduction

A phase-blind dictionary loses the character/phase information needed by the
inert or complex frame sector.  In the existing finite-frame accounting this
is stored as failure of the inert factor:

```text
phase-blind frame
  -> inert/complex phase information lost
  -> A_inert degenerates
  -> uniform lower-bound route fails
```

The phase-complete MirrorB7 dictionary restores the missing phase lane:

```text
phase-complete MirrorB7 frame
  -> zeta7 / complex character resolution retained
  -> candidate A_inert > 0
  -> A_split, A_inert, A_71 still all need proof
```

The latest toy-model attempt adds an important guard:

```text
1D toy Gram with sectors orthogonal by position
  -> blind and complete sectors block-diagonalise
  -> phase has no measurable effect
  -> no inert-prime failure mode is witnessed
```

So the phase-completeness reduction only becomes testable in the full 3D
Archimedean image, where different phase sectors can overlap spatially and
the cross-Gram can see the `zeta7` phase.

## Exact Open Lemmas

The Gate3 frame proof target is:

```text
A_split > 0
A_inert > 0
A_71 > 0
uniform cutoff lower bound
Mosco / no-spectral-pollution lift
```

This makes phase completeness a necessary condition and a proof-routing
constraint.  The 1D toy model cannot discharge it; the open proof must use
the physical 3D Hecke/SSP embedding.  It is not a spectral-gap proof and it
does not promote Clay.
