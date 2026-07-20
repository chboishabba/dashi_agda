# Triadic exploded-transform codec formalism

## Status

This is a **bridge/specification surface**. It does not promote an analytic
universal-approximation theorem, continuum geometry, empirical codec advantage,
or physical closure.

The checked implementation is split across:

- `DASHI.Geometry.TriadicExplodedTransformTower`
- `DASHI.Codec.TriadicExplodedTransformBridge`

It reuses the existing formal spine rather than replacing it:

- `DASHI.Geometry.SSP369TreeAutomorphism` for finite tree-action,
  prefix, and depth preservation;
- `DASHI.Physics.Closure.W9MDLTerminationSeamRoute` for the accepted
  non-pressure MDL/Lyapunov termination seam.

## Core carrier

The primitive carrier is balanced ternary

\[
T=\{-1,0,+1\},\qquad \iota(t)=-t.
\]

The implementation proves that `ιT` is involutive and extends it pointwise to
state fields `Geometry -> Channel -> Trit`.

The support/sign representation is derived, not primitive:

- `0` maps to `atZero`;
- `-1` maps to `onSupport negative`;
- `+1` maps to `onSupport positive`.

Both round trips are proved exactly.

## Geometric action

A warp acts on indices by pullback. Since the warp does not modify ternary
values, pullback commutes definitionally with sign involution.

An **atomic transform** contains:

1. a Boolean support region;
2. a local index warp.

An **exploded transform** is an ordered finite list of atomic transforms.
The implementation proves pointwise involution equivariance for every atomic
and exploded transform without assuming continuity, invertibility, or disjoint
support.

A separate `ExplodedPartitionReceipt` carries the stronger partition-tree and
recognisability obligations. This keeps executable geometry distinct from the
claim that atoms are coherent leaves of a particular tree.

## Renormalisation tower

`ScaleSystem` packages geometry, channels, controls, and an update operation.
`ScaleMap` requires two commuting laws:

\[
\Pi(\iota s)=\iota(\Pi s),
\]

and

\[
\Pi(F(s,u))=F'(\Pi s,\Pi_U u).
\]

Thus atomic/exploded geometry is integrated into the multiscale tower without
claiming that every existing DASHI scale map already supplies such a receipt.

## Causality and charts

`CausalChart` makes chart choice history-indexed. A concrete codec supplies its
history/filtration carrier, sampler, lag semantics, predictor, and residual
algebra. The structural chart contains tree depth, reference lag, exploded
transform, and side cost.

## MDL

`GeometricControl` records tree depth, lag, exploded transform, and side cost.
`MDLChoice` requires the chosen chart's total description length to be no larger
than every alternative under a supplied residual cost.

This is deliberately distinct from the existing W9 theorem: the new module
imports W9's accepted MDL termination witness as a live reference, but does not
reinterpret W9 as a video-codec theorem.

## Universality boundary

The earlier prose claim

> every geometric map can be approximated by exploded affine transforms

is **not valid without hypotheses**. At minimum one must specify:

- the geometric domain and codomain;
- the atomic family, such as affine maps;
- a metric or sampling error relation;
- regularity assumptions on the target map;
- a refinement construction;
- a proof for every target and tolerance.

Accordingly, `UniversalityReceipt` is a gate requiring a selected exploded
approximation and a proof that it satisfies the chosen approximation relation.
No unconditional universality theorem is asserted.

## Relation to the p-adic codec

For a concrete video codec, one may instantiate:

- geometry as pixel/block coordinates;
- channels as image channels;
- history as already-decoded frames and metadata;
- atomic warps as local translation/similarity/affine samplers;
- exploded transforms as tree-indexed piecewise motion;
- residuals as balanced-ternary digit planes;
- support/sign folding via `FoldedTrit`;
- chart selection via `MDLChoice`;
- analytic approximation and measured bitrate through separate receipts.

This establishes the missing affine/warp/atomic/exploded-transform stratum while
preserving the repository's proof/bridge/empirical boundaries.
