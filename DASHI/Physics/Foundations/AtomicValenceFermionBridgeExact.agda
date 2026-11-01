module DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.OddGrassmannLaneCore as Grassmann
import DASHI.Physics.Foundations.AtomicFermionShellExact as Atomic

------------------------------------------------------------------------
-- Finite antisymmetric exchange carrier.

data FermionLabel : Set where
  fermionAlpha : FermionLabel
  fermionBeta : FermionLabel

data ExchangePhase : Set where
  positiveExchangePhase : ExchangePhase
  negativeExchangePhase : ExchangePhase

record OrderedFermionPair : Set where
  constructor orderedFermionPair
  field
    firstLabel : FermionLabel
    secondLabel : FermionLabel
    exchangePhase : ExchangePhase

open OrderedFermionPair public

swapFermions : OrderedFermionPair → OrderedFermionPair
swapFermions
  (orderedFermionPair first second positiveExchangePhase) =
  orderedFermionPair second first negativeExchangePhase
swapFermions
  (orderedFermionPair first second negativeExchangePhase) =
  orderedFermionPair second first positiveExchangePhase

canonicalAntisymmetricPair : OrderedFermionPair
canonicalAntisymmetricPair =
  orderedFermionPair fermionAlpha fermionBeta negativeExchangePhase

swapTwiceReturnsCanonicalPair :
  swapFermions (swapFermions canonicalAntisymmetricPair)
  ≡
  canonicalAntisymmetricPair
swapTwiceReturnsCanonicalPair = refl

data ExteriorOccupancyStatus : Set where
  exteriorStateAllowed : ExteriorOccupancyStatus
  duplicateOneParticleStateVanishing : ExteriorOccupancyStatus

exteriorStatus : FermionLabel → FermionLabel → ExteriorOccupancyStatus
exteriorStatus fermionAlpha fermionAlpha = duplicateOneParticleStateVanishing
exteriorStatus fermionBeta fermionBeta = duplicateOneParticleStateVanishing
exteriorStatus fermionAlpha fermionBeta = exteriorStateAllowed
exteriorStatus fermionBeta fermionAlpha = exteriorStateAllowed

duplicateAlphaStateVanishes :
  exteriorStatus fermionAlpha fermionAlpha
  ≡
  duplicateOneParticleStateVanishing
duplicateAlphaStateVanishes = refl

mixedPairIsAllowed :
  exteriorStatus fermionAlpha fermionBeta ≡ exteriorStateAllowed
mixedPairIsAllowed = refl

existingGrassmannCandidateCarrier : Set
existingGrassmannCandidateCarrier = Grassmann.OddGrassmannLaneReceipt

------------------------------------------------------------------------
-- Periodicity requires an equivalence class of active valence structure.

data ValencePattern : Set where
  twoActiveSStates : ValencePattern
  twoActivePStates : ValencePattern
  sixActivePStates : ValencePattern
  closedValencePattern : ValencePattern

data ValenceEquivalenceClass : Set where
  alkalineEarthLikeClass : ValenceEquivalenceClass
  chalcogenLikeClass : ValenceEquivalenceClass
  nobleLikeClass : ValenceEquivalenceClass

valenceClass : ValencePattern → ValenceEquivalenceClass
valenceClass twoActiveSStates = alkalineEarthLikeClass
valenceClass twoActivePStates = chalcogenLikeClass
valenceClass sixActivePStates = chalcogenLikeClass
valenceClass closedValencePattern = nobleLikeClass

sameClassAcrossDifferentValenceRepresentatives :
  valenceClass twoActivePStates ≡ valenceClass sixActivePStates
sameClassAcrossDifferentValenceRepresentatives = refl

record AtomicValenceFermionBoundary : Set where
  constructor atomicValenceFermionBoundary
  field
    pauliPrincipleIsOnlyACapacityCount : Bool
    pauliPrincipleIsOnlyACapacityCountIsFalse :
      pauliPrincipleIsOnlyACapacityCount ≡ false

    grassmannCandidateReceiptCompletesExteriorAlgebra : Bool
    grassmannCandidateReceiptCompletesExteriorAlgebraIsFalse :
      grassmannCandidateReceiptCompletesExteriorAlgebra ≡ false

    periodicityFollowsFromProtonNumberWithoutValenceEquivalence : Bool
    periodicityFollowsFromProtonNumberWithoutValenceEquivalenceIsFalse :
      periodicityFollowsFromProtonNumberWithoutValenceEquivalence ≡ false

    valenceClassAlonePredictsAllChemistry : Bool
    valenceClassAlonePredictsAllChemistryIsFalse :
      valenceClassAlonePredictsAllChemistry ≡ false

open AtomicValenceFermionBoundary public

canonicalAtomicValenceFermionBoundary : AtomicValenceFermionBoundary
canonicalAtomicValenceFermionBoundary =
  atomicValenceFermionBoundary false refl false refl false refl false refl
