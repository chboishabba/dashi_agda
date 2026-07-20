# DASHI Wave Algorithm Formalism

## Status

This document records the theorem-thin wave lift of the existing DASHI algorithm.
It is a formal interface and crosswalk over the finite wave modules already in the
repository. It does **not** promote the current integer-pair carrier to analytic
quantum mechanics, a Hilbert-space model, a continuum Schrödinger equation, or a
quantum speedup claim.

The canonical implementation surface is:

- `DASHI.Physics.WaveAlgorithmLift`
- `DASHI.Physics.WaveAlgorithmLiftRegression`

## 1. Core correspondence

The wave variant retains the original algorithmic structure while changing the
representation and the point at which irreversible selection occurs.

| DASHI discrete language | Wave-lift language |
|---|---|
| balanced trit `- / 0 / +` | opposite phase / zero amplitude / reference phase |
| involution | phase opposition |
| branch | superposition |
| check or invariant action | phase action |
| prune | cancellation, but only with an explicit cancellation witness |
| fixed point or low-action orbit | coherent eigen-object |
| quotient / decode | observation followed by projection |
| renormalisation lift | coarse/fine wave lift with evolution compatibility |
| action / MDL | description-length concentration on coherent observables |

The critical qualification is that *pruning is equivalent to interference only
when a cancellation law has actually been supplied*. Merely attaching phases to
branches does not prove that rejected branches disappear observationally.

## 2. Exact finite carrier

The existing wave spine uses:

```text
DiscreteWave = (re : ℤ, im : ℤ)
```

with superposition by integer-pair addition and the quarter-turn operation

```text
mulI(re, im) = (-im, re).
```

`WaveAlgorithmLift` embeds balanced ternary as:

```text
+  ↦ ( 1, 0)
0  ↦ ( 0, 0)
-  ↦ (-1, 0)
```

and proves by reduction that:

1. ternary involution is involutive;
2. ternary involution is represented by two quarter turns (`mulI ∘ mulI`);
3. `+` and `-` have equal unit squared norm;
4. `0` has zero squared norm.

These are finite algebraic facts over the current carrier, not analytic claims.

## 3. Full algorithmic surface

`WaveInferenceSurface` carries:

- a hypothesis type;
- a wave type;
- an observable type;
- zero amplitude;
- superposition;
- hypothesis-indexed phase action;
- evolution;
- observation;
- coherence and admissibility classifiers.

The following laws are deliberately separate records rather than assumptions
hidden in the carrier:

### Reversibility

`ReversibleWaveObligations` requires a two-sided inverse for evolution.

### Norm preservation

`NormPreservingWaveObligations` requires both evolution and phase actions to
preserve a supplied norm. The current Euler-style finite Schrödinger step does
not satisfy this merely because `mulI` preserves basis norms.

### Interference/pruning bridge

`InterferencePruningBridge` requires rejected hypotheses to pair with an
opposite contribution whose superposition is exactly zero amplitude.

### Coherent eigen-objects

`CoherentEigenObject` packages a state whose evolution differs only by a supplied
eigenphase action and whose coherence classifier is true. This is the wave form
of a fixed object or low-action orbit; no spectral theorem is inferred.

### Projection boundary

`ProjectionBoundary` keeps observation and classical projection downstream from
evolution, and requires an explicit law connecting observational zero to the
zero-amplitude observation.

### Refinement tower

`WaveRefinementTower` requires:

```text
projectWave (lift ψ) = ψ
evolveFine (lift ψ) = lift (evolveCoarse ψ)
projectObservable (observeFine (lift ψ)) = observeCoarse ψ
```

This is the wave form of the DASHI renormalisation tower. It aligns with the
existing `ShiftWaveRefinementSeam`, `ShiftWaveRefinementHierarchy`, and
`ShiftWaveGlobalUpdate` modules without pretending a continuum limit.

### MDL concentration

`WaveMDLConcentration` keeps compression distinct from norm preservation. It
requires a code and description-length surface and states that coherent evolution
does not increase the selected observable description length.

This is intentionally not derived from unitarity. Norm concentration, coding
concentration, and physical energy conservation are different propositions.

## 4. Existing formal spine referenced

The new package sits above, and should be read with, these existing modules:

- `SchrodingerGapPhaseWaveShiftInstance`: structured carrier, amplitude, phase,
  density ordering, phase descent, and finite interference-charge conservation;
- `ShiftPhaseTableInterference`: four-class phase table and bounded interaction
  intensity;
- `ShiftDiscreteWaveStep`: integer-pair superposition and the Euler-style
  `ψ ↦ ψ + iHψ` update;
- `ShiftUnitaryLikeConstraint`: exact basis norm preservation and four-quarter-turn
  closure for `mulI`, explicitly not unitarity of the Euler step;
- `ShiftWaveRefinementSeam` and `ShiftWaveRefinementHierarchy`: finite
  lift/project compatibility;
- `ShiftWaveGlobalUpdate`: synchronous coarse/refined field update;
- `ShiftDiscreteHelmholtzSurface`: finite modewise Helmholtz and Schrödinger-facing
  equations;
- `ShiftDiscreteWaveEnergy` and `ShiftWaveEnergyHierarchy`: exact finite energy
  behavior, including concrete growth where stability would be false;
- `ShiftDiscreteContinuityCurrent` and `ShiftDiscreteActionPrinciple`: finite
  current and action bookkeeping;
- `ShiftFinitePathSum`: bounded two-history path sum;
- `ShiftFieldTheoryConsistency`: coherence of update, action/current, energy, and
  path-sum surfaces;
- `ShiftFiniteGaugeSymmetry`, `ShiftFiniteGaugeCoupling`, and follow-ons: bounded
  finite phase/gauge analogues;
- `ShiftFiniteMatrixSymmetry`: finite matrix action and non-commuting witness,
  still below `SU(2)` or Hilbert-space promotion.

## 5. Promotion boundary

A genuine unitary or physical quantum interpretation still requires, at minimum:

1. a specified scalar field and complete inner-product space;
2. linearity and boundedness/domain control for the evolution operators;
3. an actually self-adjoint Hamiltonian or an exact unitary update construction;
4. norm preservation for the complete state space, not only basis quarter turns;
5. a justified observation/probability rule;
6. spectral and convergence results where invoked;
7. a demonstrated relationship between wave cancellation and computational cost;
8. empirical correspondence before any physical interpretation.

Until those obligations are inhabited, the defensible claim is:

> DASHI has an exact finite sign/phase wave encoding and a typed algorithmic
> interface relating superposition, interference, coherent eigen-objects,
> projection, multiscale refinement, and MDL concentration, while retaining hard
> boundaries against analytic-unitary, continuum, physical-quantum, and speedup
> overclaims.
