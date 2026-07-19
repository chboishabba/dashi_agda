# Nonlinear exploded sparsity and threshold-CSP geometry

This module formalises the narrow bridge between the DASHI ternary kernel,
exact support/sign explosion, nonlinear sparsification, and graph-structured
constraint satisfaction.

Implementation:

- `DASHI/Core/NonlinearExplodedSparsity.agda`
- `DASHI/Core/NonlinearExplodedSparsityTests.agda`

It extends the minimal kernel algebra rather than introducing another primitive
kernel. Balanced ternary remains primitive; support and sign remain derived.

## 1. Atomic and exploded states

An atomic state is a field

```text
s : X → Trit
```

with `Trit = { neg, zer, pos }`.

The exploded atom is the exact support/sign factorisation already supplied by
`MinimalKernelAlgebra`:

```text
neg ↔ active negative
zer ↔ inactive
pos ↔ active positive
```

`explodeAtom` carries a proof that decoding returns the original trit. Hence
explosion is lossless. Sparse atoms are represented by the dependent carriers

```text
ActiveAtom  s = Σ x : X , s x ≠ zer
NeutralAtom s = Σ x : X , s x = zer
```

Explosion does not itself assert that active or neutral support is small. It
makes support explicit so a later sparsity or MDL theorem can quantify it.

## 2. Affine/local field and nonlinear projection

A `ThresholdKernel X L` consists of:

1. a local or affine field `localField : State X → X → L`; and
2. a ternary partition of `L` into negative, neutral, and positive regions.

The kernel is their composite:

```text
K(s)(x) = classify (localField s x)
```

This keeps the DASHI order explicit:

```text
atomic state → affine/local aggregation → nonlinear ternary projection
             → exact exploded support/sign observation
```

The theorem `nonlinearSparsityExact` states that projected zero support is
exactly the preimage of the neutral/deadzone region. Positive and negative
analogues are also proved.

## 3. Fixed-point margin theorem

For a kernel-closed state `K(s) = s`, each atomic value has the matching local
margin:

- `s(x)=zer` implies the local field lies in the neutral region;
- `s(x)=pos` implies the local field lies in the positive region;
- `s(x)=neg` implies the local field lies in the negative region.

This is exact and constructive.

## 4. Conditional nonlinear sparsity theorem

Thresholding always creates an exact zero pattern, but sparse neutral or defect
support is **not** a universal theorem for arbitrary graphs.

The module therefore makes the required hypothesis explicit. A
`MarginControl K s LowMargin` proves that every node outside `LowMargin`
already satisfies its local kernel constraint. It follows that:

```text
KernelDefect K s x → ¬¬ LowMargin x
```

and, when membership in `LowMargin` is decidable:

```text
KernelDefect K s x → LowMargin x
```

Thus a sparse low-margin carrier entails sparse defect support. Cardinality or
measure bounds belong in a finite-carrier extension and are not silently
assumed here.

## 5. Exact threshold-CSP correspondence

Each node indexes one local weighted-threshold clause:

```text
LocalConstraint K s x = (K(s)(x) = s(x))
```

The module proves:

```text
KernelClosed K s ↔ SatisfiesAllLocalConstraints K s
```

Kernel defects are exactly violated local clauses, up to equality orientation.
This is a graph-structured threshold CSP. The formalisation deliberately does
**not** identify defects with minimal unsatisfiable cores; that requires an
additional subset-minimality theorem.

## 6. Contrast with ℓ1 and ReLU sparsity

### ℓ1

An ℓ1 penalty is an optimisation objective over coordinates. Its zero pattern
comes from minimising a separable convex cost subject to other constraints.
The present theorem uses no penalty and no optimisation oracle. Zero support is
the exact nonlinear preimage of the kernel's neutral region.

### ReLU or coordinate thresholding

A ReLU-like rule is coordinate-wise:

```text
coordinateLift f s x = f (s x)
```

The theorem `coordinateRuleIsPointwise` proves that such a rule cannot distinguish
two global states that agree at `x`.

`NonCoordinateWitness K` supplies two states that agree at one node but yield
different kernel outputs there. The theorem
`nonCoordinateWitnessRulesOutCoordinateRepresentation` then proves that no
coordinate-only rule represents that adjacency-dependent kernel. The test
module gives a constructive two-node witness.

## 7. Safe claim boundary

The formal result is:

> Exact nonlinear projection exposes sparse atoms as support/sign data; defect
> support is confined to a chosen low-margin carrier when stability outside
> that carrier is proved; kernel closure is exactly satisfaction of all local
> threshold constraints.

It does not claim that every graph has sparse defects, that every neutral node
is biological conflict, or that every defect is a minimal SAT core. Those are
consumer-level hypotheses requiring finite counts, graph geometry, or
application-specific evidence.
