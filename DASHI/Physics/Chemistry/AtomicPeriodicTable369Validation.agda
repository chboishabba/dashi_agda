module DASHI.Physics.Chemistry.AtomicPeriodicTable369Validation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as G
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProvenanceSnowballExact as P

------------------------------------------------------------------------
-- Focused validation root.  Importing this module forces both the generative
-- formalism and its provenance/snowball companion through the Agda checker.

capacityRegression :
  G.subshellCapacity 0 ≡ 2
  × G.subshellCapacity 1 ≡ 6
  × G.subshellCapacity 2 ≡ 10
capacityRegression =
  G.sCapacity , (G.pCapacity , G.dCapacity)

shellCapacityRegression :
  G.shellCapacity 1 ≡ 2
  × G.shellCapacity 2 ≡ 8
  × G.shellCapacity 3 ≡ 18
shellCapacityRegression =
  G.firstShellCapacity , (G.secondShellCapacity , G.thirdShellCapacity)

historicalClosureCoordinateRegression :
  G.historicalClosureZ G.heliumLikeClosure ≡ 2
  × G.historicalClosureZ G.neonLikeClosure ≡ 10
  × G.historicalClosureZ G.argonLikeClosure ≡ 18
historicalClosureCoordinateRegression =
  G.heliumLikeZ , (G.neonLikeZ , G.argonLikeZ)

closedValenceRegression :
  G.valenceClass
    DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact.closedValencePattern
  ≡
  DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact.nobleLikeClass
closedValenceRegression = G.closedValenceIsNobleLike

nonPromotionRegression :
  G.Atomic369NonPromotionBoundary.triadicCardinalityDerivesOrbitalQuantumNumbers
    G.canonicalAtomic369NonPromotionBoundary
  ≡ false
nonPromotionRegression = refl

snowballRegression :
  P.SnowballDiscipline.acquisitionMayBeOutOfDependencyOrder
    P.canonicalSnowballDiscipline
  ≡ true
  ×
  P.SnowballDiscipline.retainedLaterEvidencePaysEarlierMissingDependency
    P.canonicalSnowballDiscipline
  ≡ false
snowballRegression = refl , refl
