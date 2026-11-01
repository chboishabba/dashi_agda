# YM Repo Frontier Checklist

Date: 2026-07-10

## Purpose

This note compresses the live repo-local Yang-Mills frontier after the recent
P06 graph-combinatorics cleanup.

It does three things:

- isolates what is already wired
- names the exact theorem surfaces still missing
- orders the remaining work by dependency

It is a working checklist only. It does not claim any new theorem closure.

## Current state

Closed or materially improved on the active repo-local P06 chain:

- `VertexLabeling -> vertexOrder -> vertexOrderIsTotalOrder`
- rooted spanning-tree extraction for connected skeletons
- DFS walk cover of rooted connected skeletons
- reverse containment of the DFS walk range back into the skeleton
- canonical vertex-list equality from `NoDuplicates + Sorted + SameVertexSet`
- canonical DFS injectivity infrastructure from canonical vertex lists

Still open on the active P06 chain:

- existence of `VertexLabeling` for the actual graph
- graph-ball semantics and ball containment proof
- finite ball enumeration
- subset enumeration over a finite ball
- concrete `CanonicalSkeletonEnumeration`
- concrete `WalkEnumeration` / bounded neighbour-code route
- final `encode/decode/decenc` closure for the canonical P06 encoding lane

Important correction:

- `P06a3aDiameterShellContainedInRootBall` is not mathematically discharged.
- What exists now is an exposed containment interface, not a finished
  root-ball containment proof.

## Already wired

These surfaces exist and should be treated as consumers waiting for real
inhabitants, not as missing bookkeeping.

### Graph order and canonical list infrastructure

Primary file:

- `DASHI/Physics/YangMills/GraphCombinatorics.agda`

Ready surfaces:

- `VertexLabeling`
- `vertexOrder`
- `vertexOrderIsTotalOrder`
- `CanonicalVertexList`
- `SameVertexSetCanonicalListEq.sameVertexSetCanonicalListEq`

Status:

- the old artificial `vertexOrderIsTotalOrder` postulate has been replaced by
  a constructive reduction to injective labels in `Nat`
- this does not yet prove that the actual support graph comes equipped with a
  concrete `VertexLabeling`

### DFS cover side of P06a2

Primary file:

- `DASHI/Physics/YangMills/GraphCombinatorics.agda`

Ready lemmas:

- `P06a2bConnectedSkeletonHasRootedSpanningTree`
- `P06a2cRootedTreeDFSWalk`
- `P06a2dBoundedDegreeWalkCount`
- `P06a2eConnectedSkeletonCoveredByDFSWalk`
- `P06a2eConnectedSkeletonWalkRangeContained`

Interpretation:

- every rooted connected skeleton is reduced to a rooted spanning tree
- the spanning tree yields a DFS walk of controlled length
- the DFS walk both covers the skeleton and does not leave it

This is already enough to support exact vertex-set equality between the DFS
walk range and the skeleton vertex set once a specific skeleton witness is
given.

### Partial canonical encoding carrier

Primary file:

- `DASHI/Physics/YangMills/P06EncodingWitness.agda`

Ready surfaces:

- `dfsEncoding`
- `encodeWalkOnlyVisitsSkeleton`
- `encodeWalkCoversSkeleton`
- `encodeWalkRangeExact`
- `partialP06CanonicalCarrier`

Status:

- the carrier is structurally wired
- `bridgeProofClosed = false` remains the correct state
- the remaining leaves are the actual encoding/decoding and counting witnesses

### Canonical enumeration consumer layer

Primary file:

- `DASHI/Physics/YangMills/GraphCombinatorics.agda`

Ready consumer records:

- `CanonicalSkeletonObject`
- `SkeletonEnumerationCanonical`
- `CanonicalSkeletonEnumeration`
- `CanonicalDFSMap`
- `enumerationsToEncodingData`
- `canonicalDFSMapToEncodingData`

Interpretation:

- the repo already knows how to consume a concrete finite skeleton
  enumeration and a concrete finite walk enumeration
- what is missing is constructing those enumerations from actual finite graph
  combinatorics

## Live theorem frontier

## 1. Ball containment theorem

Primary file:

- `DASHI/Physics/YangMills/GraphCombinatorics.agda`

This is the first real missing theorem, not another wrapper.

The exact live surfaces are:

- `connectedGivesPathInSkeleton`
- `simplePathInsideSkeletonLengthBound`
- `pathBoundGivesBallMembership`
- `connectedSkeletonContainedInBall`

Exact mathematical content still missing:

- for every `x ∈ X`, build an internal path from the root `r` to `x`
- prove a simple path inside an `n`-vertex skeleton has length at most
  `n ∸ 1`
- convert that path-length bound into graph-ball membership
- conclude `X ⊆ ball G r (n ∸ 1)`

This is the theorem that turns the currently exposed root-ball interface into
actual graph geometry.

## 2. Finite ball enumeration

Primary file:

- `DASHI/Physics/YangMills/GraphCombinatorics.agda`

The next exact surface is:

- `FiniteBallEnumeration`

Required fields to inhabit:

- `ballList`
- `ballSoundList`
- `ballCompleteList`
- `ballNoDup`
- `ballSorted`

Interpretation:

- after containment is proved, the relevant carrier must become a concrete
  finite sorted list of vertices

## 3. Subset enumeration over the finite ball

Primary target location:

- `DASHI/Physics/YangMills/GraphCombinatorics.agda`

The next missing combinatorial objects are:

- `chooseN`
- `chooseNSound`
- `chooseNComplete`

Required theorem content:

- every member of `chooseN xs n` is an `n`-element subset of `xs`
- every sorted duplicate-free `n`-subset of `xs` appears in `chooseN xs n`

This is the step that converts finite-ball geometry into an actual finite
carrier for skeleton enumeration.

## 4. Canonical skeleton enumeration

Primary file:

- `DASHI/Physics/YangMills/GraphCombinatorics.agda`

Consumer record already exists:

- `CanonicalSkeletonEnumeration`

What is still missing is the concrete constructor route:

- rooted connected size-`n` skeleton
- `⊆ ball(r , n ∸ 1)`
- member of the finite `n`-subset list of that ball
- filtered by root/connectedness/reducedness
- therefore assigned a canonical finite index

Open exact bridge surfaces still left postulated:

- `bridgeSkeletonIndex`
- `bridgeSkeletonIndexOf`

Those should disappear only after the actual finite enumeration exists.

## 5. Walk enumeration via bounded neighbour codes

Primary file:

- `DASHI/Physics/YangMills/GraphCombinatorics.agda`

The next exact witness record is:

- `BoundedNeighbourEnumeration`

Required fields:

- `neighbours`
- `neighbourSound`
- `neighbourComplete`
- `neighbourBound`

Then the walk side should be replaced by a concrete bounded-code route:

- walk of length `L`
- mapped to a length-`L` sequence of neighbour indices
- injected into `Fin Δ ^ L`

This is the constructive replacement for the abstract `WalkEnumeration` layer.

## 6. Final P06 canonical encoding closeout

Primary file:

- `DASHI/Physics/YangMills/P06EncodingWitness.agda`

The exact remaining postulated leaves are:

- `encode`
- `decode`
- `decenc`
- `skeletonVertices`
- `walkRange`
- `skeletonVerticesSize`
- `skeletonWitness`
- `walkRangeOfEncode`
- `skeletonCountBound`

Interpretation:

- once concrete skeleton and walk enumerations exist, these should collapse
  into actual constructions rather than abstract finite-index promises

## Dependency order

The remaining repo-local work should be done in this order.

### A. Ball geometry first

Prove:

- `connectedGivesPathInSkeleton`
- `simplePathInsideSkeletonLengthBound`
- `pathBoundGivesBallMembership`
- `connectedSkeletonContainedInBall`

Reason:

- everything downstream depends on replacing the current semantic
  root-ball interface with an actual theorem

### B. Finite carrier next

Construct:

- `FiniteBallEnumeration`

Reason:

- once the skeleton is known to live in a finite ball, the next blocker is an
  actual finite list of candidate vertices

### C. Subset enumeration after the finite carrier

Construct:

- `chooseN`
- soundness/completeness lemmas

Reason:

- canonical skeleton enumeration is naturally a filtered `n`-subset
  enumeration of the finite ball

### D. Canonical skeleton enumeration

Construct:

- concrete `CanonicalSkeletonEnumeration`

Reason:

- this removes the remaining abstract skeleton-index bridge postulates and
  supplies the finite carrier needed by the encoding layer

### E. Walk enumeration from bounded neighbours

Construct:

- `BoundedNeighbourEnumeration`
- concrete `WalkEnumeration`

Reason:

- the canonical encoding route needs a real finite walk carrier, not an
  abstract walk-index oracle

### F. Final P06 encoding depostulation

Close:

- `encode`
- `decode`
- `decenc`
- `walkRangeOfEncode`
- `skeletonCountBound`

Reason:

- once both finite carriers exist, the remaining canonical P06 route should
  reduce to explicit finite combinatorics and injectivity

## Relationship to `ym_plan.txt`

`ym_plan.txt` is still directionally correct that the live local frontier is
P06, then P33/radius, then downstream depostulation.

The stale point is the exact status of `P06a3aDiameterShellContainedInRootBall`:

- old framing: diameter-shell containment was effectively an exposed theorem
- corrected framing: the repo now exposes the ball-containment interface, but
  the actual graph-theoretic ball-containment proof remains open

This checklist should be treated as the local source of truth for the current
repo frontier until `ym_plan.txt` is updated.
