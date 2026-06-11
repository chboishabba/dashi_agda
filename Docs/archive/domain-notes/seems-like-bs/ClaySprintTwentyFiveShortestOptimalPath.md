# Clay Sprint 25 Shortest / Optimal Path

Sprint 25 records the shortest honest route from the current repo state and
why these lemmas are the correct direction.

No promotion flag changes in this document.

## One-Line State

```text
Gate3 is the nearest support flag.
Navier-Stokes is the shortest Clay-facing route.
Yang-Mills is the longer constructive-QFT route.
```

## Gate3: Nearest Support Flag

### Lemma 1: `PrunedFillDistanceGoesToZero`

ELI5: the pruned atoms are dots on a circle.  If the biggest gap between dots
keeps shrinking, eventually every point on the circle is near a dot.

Why needed: density starts the continuum approximation route.  Without density,
there is no Mosco recovery sequence.

Intuitive solution: use the power law

```text
h_pruned(J) <= C / J^0.92
```

Since `0.92 > 0`, the right side goes to zero as `J` grows.

Source:

```text
DASHI/Physics/Closure/ClaySprintTwentyFourMicroLemmaReceipt.agda
```

### Lemma 2: `PrunedUnionDenseInAngularL2`

ELI5: once the dots cover the circle densely, combinations of kernels centered
at those dots can draw any smooth enough angular picture.

Why needed: Gate3 needs the pruned atoms to span the target angular Hilbert
space densely.

Intuitive solution: use dense centers plus Gaussian kernel universality.

### Lemma 3: `MoscoRecoveryFromPrunedUnionDensity`

ELI5: if every target shape can be approximated by pruned atoms, build a
sequence of pruned approximations that converges to the real object.

Why needed: Mosco recovery is the bridge from dense approximation to spectral
operator convergence.

Status: open. Density arithmetic alone does not prove this recovery sequence.

### Lemma 4: `Gate3MoscoNoPollutionTransfer`

ELI5: the approximations must not create fake notes in the spectrum.

Why needed: Gate3 is not just density; the spectral limit must be clean.

### Why This Direction

The direct Archimedean Gram route already exposed collapse issues.  The
p-adic carrier arithmetic is not the current blocker.  The pruned-union
density plus Mosco route directly attacks the remaining support flag.

Rejected direction:

```text
Direct Archimedean Gram only.
```

Reason: it does not solve the continuum transfer/collapse problem.

## Navier-Stokes: Shortest Clay-Facing Route

### Lemma 1: `ResidueDecayBeatsHalfDerivative`

ELI5: bad vortex stretching grows like multiplying by `sqrt(2)` each scale.
If bad residue shrinks by a factor `r`, and `r * sqrt(2) < 1`, the bad tower
shrinks.

Why needed: this is the exact arithmetic for the missing half derivative.

Intuitive solution:

```text
sum_K (r * sqrt(2))^K
```

is finite when `r * sqrt(2) < 1`.

### Lemma 2: `BraidResidueControlsPhysicalStretching`

ELI5: the traffic-light/braid score has to measure how hard the water rope is
actually being pulled.

Why needed: branch counts do not prove a PDE estimate.  The residue must bound
the real vortex-stretching integral.

Intuitive solution: define `BraidResidue369(K)` as a functional of
`u`, `omega`, `p`, strain alignment, phase, Leray projection, and shell data,
then prove:

```text
abs (PhysicalShellStretching K)
  <= C * BraidResidue369 K * 2^(K/2) * DissipationShell K
```

The audit bridge must also prove:

```text
Q_K <= C * R_K
```

Before this bridge is proved, transition-count ratios are carrier diagnostics
only and cannot promote Navier-Stokes.

### Lemma 3: `DynamicBraidResidueDecayForNS`

ELI5: real water must be forced to lose badness at every smaller scale.  It is
not enough that most symbolic branches are good.

Why needed: Clay is worst-case deterministic.

Intuitive solution: prove that actual Navier-Stokes evolution, via
incompressibility/Leray projection/strain-vorticity geometry, forces

```text
Residue(K+1) <= r * Residue(K)
```

for some `r < 1/sqrt(2)`.

### Lemma 4: `CoherentTubeExclusion`

ELI5: prove the water rope cannot keep choosing the “stretch harder” branch
forever.

Why needed: a coherent vortex tube is the adversary that defeats residue
decay.

### Lemma 5: Stretch Absorption and No Blowup

ELI5: once bad stretching is small, soap wins; then spin stays finite.

Why needed: this is the Gronwall/continuation endpoint.

### Why This Direction

Rejected directions:

```text
Static Leray/Sobolev estimates only.
Beltrami identity alone.
Pressure as direct dissipation.
Branch counting without physical stretching control.
```

Reasons:

- static estimates leave the half-derivative gap,
- Beltrami cancellation is an identity, not dynamic production,
- pressure is projection/gauge, not direct enstrophy dissipation,
- branch counts do not control amplitudes or worst-case PDE trajectories.

Therefore the correct route is analytic residue plus deterministic dynamic
depletion.

## Yang-Mills: Longer Clay Route

### Lemma 1: `NonperturbativeCorrectionBudget`

ELI5: the toy one-loop forecast says the glue becomes safe.  This lemma says
how wrong that forecast may be before the safety margin fails.

Why needed: the useful target is `rho <= 0.90`, equivalently
`beta_true >= 14.16373`.

Intuitive solution:

```text
beta_true(k) >= beta_one_loop(k) - eta(k)
eta(k) <= beta_one_loop(k) - 14.16373
=> beta_true(k) >= 14.16373
```

### Lemma 2: `ContinuumUniformRhoBoundAtSafeScale`

ELI5: no matter how fine the grid gets, the glue blocks must keep sticking
with enough margin.

Why needed: Clay requires continuum-uniform control, not a finite calculation.

### Lemma 3: `ContinuumUniformLeakageBound`

ELI5: when blocks are grouped, no hidden mess may leak forever.

Why needed: contraction without leakage control is not a constructive QFT
construction.

### Lemma 4: Constructive QFT Terminals

ELI5: after the block machine works, the energy machine still has to be real,
the gap must survive the infinite limit, and the final theory must be
interacting SU(3).

Why needed: Clay YM is a continuum quantum field theory problem, not only a
block-spin estimate.

### Why This Direction

Rejected directions:

```text
One-loop as proof.
T7A/KP counting as continuum proof.
Beta/rho algebra as Balaban construction.
```

Reasons:

- one-loop is diagnostic only,
- T7A/KP is entropy/counting bookkeeping,
- beta/rho algebra says what margin is needed, not that the real
  nonperturbative flow achieves it.

Therefore the correct route is continuum-uniform nonperturbative RG plus
constructive QFT terminals.

## Worker Plan

1. Gate3 shortest support path: power-law density.
2. Gate3 Mosco/no-pollution transfer.
3. NS analytic residue and `Q_K`.
4. NS dynamic decay and coherent-tube exclusion.
5. YM correction/rho/leakage.
6. Optimality governance and docs.

All Gate3, Navier-Stokes, Yang-Mills, and Clay promotion flags remain false.
