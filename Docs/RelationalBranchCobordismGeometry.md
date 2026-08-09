# Finite Relational Branch Cobordism Geometry

## Scope

`DASHI.Reasoning.RelationalBranchCobordismGeometry` supplies an exact finite boundary-and-channel carrier for one coarse proposition or process splitting into several fine continuations.

The construction uses the pants/cobordism picture as structural provenance, but it does not claim:

- a smooth manifold;
- a topological quantum field theory functor;
- a Hilbert-space interpretation;
- a continuous angle reconstruction;
- a literal modular `j`-invariant;
- a clinical interpretation of path markers.

The exact object is combinatorial:

```text
coarse boundary
    -> finite list of typed branch channels
    -> optional gluing into a further one-to-n junction.
```

## Boundary and channel types

A `BoundaryInterface` records:

- a proposition type;
- a coarse/fine scale label;
- finite capacity;
- a phase label on the existing four-phase carrier;
- openness;
- provenance.

A `BranchChannel` adds a finite wave and destination basin. A `OneToNBranching` contains one coarse input channel and a finite list of fine outputs.

The carrier retains two distinct conservation questions:

```text
output capacity = input capacity
```

and

```text
sum of output waves = input wave.
```

Capacity may be conserved while the recombined state retains a non-zero phase/path residual.

## Exact composition

`BranchSubstitution` glues a secondary junction into one selected output of an outer junction. The gluing witness checks:

- proposition type;
- capacity;
- phase;
- wave;
- openness.

The canonical example composes:

```text
3 -> (2, 1)
```

with:

```text
2 -> (1, 1)
```

to obtain:

```text
3 -> (1, 1, 1).
```

Agda proves exactly:

```text
outputCount composedOneToThree = 3
outputCapacity composedOneToThree = inputCapacity composedOneToThree
recombinedWave composedOneToThree = coarse input wave
splitRecombineResidual composedOneToThree = 0.
```

This is finite compositional mathematics rather than a stored narrative receipt.

## Path-dependent residual memory

A second exact example conserves scalar capacity while assigning different phases to two output channels. The result is:

```text
capacity conserved
but
splitRecombineResidual = (-1, +1).
```

This supplies a concrete PNF-compatible memory distinction:

```text
same coarse amount
!=
same fine transport history.
```

A reduction that stores only total capacity would erase the retained path residual.

## Attractor projection

Each branch can be assigned a balanced attractor orientation:

```text
+1  toward the target attractor
 0  orthogonal/open
-1  away from the target attractor.
```

The module computes both:

- squared coherent intensity, which retains magnitude;
- signed attractor flux, which retains direction.

This avoids the error:

```text
large coherent magnitude
=>
progress toward the desired basin.
```

For example, two opposed branches have coherent intensity four but signed flux minus two.

## Marker suppression and relational memory

A path-marker relation is either:

```text
indistinguishablePaths
```

or:

```text
distinguishablePaths.
```

On the finite carrier, distinguishable path markers suppress the cross term. Agda computes:

```text
in-phase indistinguishable intensity = 4
in-phase distinguishable intensity   = 2

opposed indistinguishable intensity  = 0
opposed distinguishable intensity    = 2.
```

The point is not literal quantum cognition. It is an exact demonstration that whether path provenance is retained or quotiented changes the interaction term.

For relational PNF memory this creates two opposite errors:

- path erasure can create spurious constructive coherence;
- path over-separation can destroy genuine constructive coherence.

The memory system must therefore preserve path identity only at the resolution justified by evidence.

## Branch marginal law

For one branch and a finite list of other branches, the module proves:

```text
intensity(branch :: others)
=
branch diagonal intensity
+ intensity(others)
+ every cross term touching branch.
```

Closing a branch therefore removes both its own diagonal mass and all interactions incident to it. This is the exact branch-level version of the earlier marginal-attractor principle: the value of one option depends on the currently live branch ecology.

## PNF, trauma, and hyperfabric integration

The cobordism carrier is imported by `DASHI.Reasoning.RelationalEverything`, which is imported by `DASHI.RelationalFlowRepairAtlas` alongside:

- `DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge`;
- `DASHI.Biology.PredictiveMetastabilityTraumaBridge`;
- `DASHI.Core.RelationalHypervoxelBraidCore`;
- `DASHI.FullRelationalFlowRepairHyperfabric`.

A trauma-related deformation may preserve a historical path marker too broadly or erase relevant path distinctions too quickly. The module does not diagnose either condition; it provides the finite carrier on which a later evidence-bearing transport witness can be stated.

## Source provenance

The source atlas records:

Michael F. Atiyah, *Topological quantum field theory*, `Publications Mathematiques de l'IHES` 68 (1988), DOI `10.1007/BF02698547`.

The imported relationship is strictly bounded: cobordism, boundary, and compositional provenance for the finite pants analogy. Smooth topology, TQFT functoriality, Hilbert spaces, and physical field theory remain outside the theorem surface.

## Central invariant

```text
A coarse split/recombine account is adequate only when it preserves the
boundary, capacity, phase, path, residual, and provenance information needed
for later reconstruction.
```
