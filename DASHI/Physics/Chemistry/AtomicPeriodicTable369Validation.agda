module DASHI.Physics.Chemistry.AtomicPeriodicTable369Validation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as G
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProvenanceSnowballExact as P
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChronologyStatusExact as C
import DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact as V

------------------------------------------------------------------------
-- Focused validation root.  Importing this module forces the generative
-- formalism, provenance/snowball companion, and chronology/status ledger
-- through the Agda checker when this file is actually checked.
--
-- The existence of this file is not itself a typecheck receipt.  See the
-- chronology/status owner for the distinction between authored source and a
-- recorded checker run.

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
  G.valenceClass V.closedValencePattern ≡ V.nobleLikeClass
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

publicationDisciplineRegression :
  C.PublicationDiscipline.repoCommitEqualsExternalPublication
    C.canonicalPublicationDiscipline
  ≡ false
  ×
  C.PublicationDiscipline.historicalConversationDateEqualsPublicationDate
    C.canonicalPublicationDiscipline
  ≡ false
publicationDisciplineRegression = refl , refl
