module DASHI.Physics.YangMills.P06a2MiniCheck where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy

p06a2-rooted-spanning-tree-wired :
  Entropy.P06a2RootedConnectedSkeletonSizeShellCounting.rootedSpanningTreeWitness
    Entropy.currentP06a2RootedConnectedSkeletonSizeShellCounting
  ≡ Entropy.currentConnectedSkeletonHasRootedSpanningTree
p06a2-rooted-spanning-tree-wired = refl

p06a2-dfs-walk-wired :
  Entropy.P06a2RootedConnectedSkeletonSizeShellCounting.dfsWalkWitness
    Entropy.currentP06a2RootedConnectedSkeletonSizeShellCounting
  ≡ Entropy.currentRootedTreeDFSWalk
p06a2-dfs-walk-wired = refl

p06a2-walk-count-wired :
  Entropy.P06a2RootedConnectedSkeletonSizeShellCounting.walkCountWitness
    Entropy.currentP06a2RootedConnectedSkeletonSizeShellCounting
  ≡ Entropy.currentBoundedDegreeWalkCount
p06a2-walk-count-wired = refl

p06a2-walk-cover-wired :
  Entropy.P06a2RootedConnectedSkeletonSizeShellCounting.walkCoverWitness
    Entropy.currentP06a2RootedConnectedSkeletonSizeShellCounting
  ≡ Entropy.currentConnectedSkeletonCoveredByDFSWalk
p06a2-walk-cover-wired = refl

p06a3-reduced-cardinality-wired :
  Entropy.P06a3DiameterShellSkeletonCounting.reducedSkeletonCardinality
    Entropy.currentP06a3DiameterShellSkeletonCounting
  ≡ Entropy.currentReducedSkeletonCardinalityBound
p06a3-reduced-cardinality-wired = refl

p06a-rooted-spanning-tree-wired :
  Entropy.P06aRootedConnectedSkeletonCounting.rootedSpanningTreeWitness
    Entropy.currentP06aRootedConnectedSkeletonCounting
  ≡ Entropy.currentConnectedSkeletonHasRootedSpanningTree
p06a-rooted-spanning-tree-wired = refl

p06a-size-shell-counting-wired :
  Entropy.P06aRootedConnectedSkeletonCounting.sizeShellCounting
    Entropy.currentP06aRootedConnectedSkeletonCounting
  ≡ Entropy.currentP06a2RootedConnectedSkeletonSizeShellCounting
p06a-size-shell-counting-wired = refl

p06a-reduced-cardinality-wired :
  Entropy.P06aRootedConnectedSkeletonCounting.reducedSkeletonCardinality
    Entropy.currentP06aRootedConnectedSkeletonCounting
  ≡ Entropy.currentReducedSkeletonCardinalityBound
p06a-reduced-cardinality-wired = refl
