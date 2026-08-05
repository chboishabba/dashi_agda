module DASHI.Biology.SparseExpertRoutingCoalition where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Mixture-of-experts analogy: sparse production plus broad conditional
-- readability.  Global availability does not require every expert to be
-- simultaneously active.
--
-- This is an architectural analogy, not a claim that the brain literally
-- implements a contemporary machine-learning MoE router.

data Expert : Set where
  sensoryExpert : Expert
  memoryExpert : Expert
  interoceptiveExpert : Expert
  planningExpert : Expert

data RoutingContext : Set where
  sensoryDominantContext : RoutingContext
  reflectiveContext : RoutingContext

allExperts : List Expert
allExperts =
  sensoryExpert
  ∷ memoryExpert
  ∷ interoceptiveExpert
  ∷ planningExpert
  ∷ []

routeExperts : RoutingContext → List Expert
routeExperts sensoryDominantContext =
  sensoryExpert
  ∷ interoceptiveExpert
  ∷ []
routeExperts reflectiveContext =
  memoryExpert
  ∷ planningExpert
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

allExpertCount : Nat
allExpertCount = listCount allExperts

sensoryRouteCount : Nat
sensoryRouteCount = listCount (routeExperts sensoryDominantContext)

reflectiveRouteCount : Nat
reflectiveRouteCount = listCount (routeExperts reflectiveContext)

sensoryRouteIsSparse : sensoryRouteCount ≤ allExpertCount
sensoryRouteIsSparse = s≤s (s≤s z≤n)

reflectiveRouteIsSparse : reflectiveRouteCount ≤ allExpertCount
reflectiveRouteIsSparse = s≤s (s≤s z≤n)

data Addressability : Set where
  localAddressability : Addressability
  globalConditionalAddressability : Addressability

readable : Addressability → Expert → Bool
readable localAddressability sensoryExpert = true
readable localAddressability _ = false
readable globalConditionalAddressability _ = true

producedBySensoryRoute : Bool
producedBySensoryRoute = true

planningCanReadGloballyAddressedContent :
  readable globalConditionalAddressability planningExpert ≡ true
planningCanReadGloballyAddressedContent = refl

planningCannotReadSensoryLocalOnlyContent :
  readable localAddressability planningExpert ≡ false
planningCannotReadSensoryLocalOnlyContent = refl

record SparseExpertCoalitionBoundary : Set where
  constructor sparseExpertCoalitionBoundary
  field
    allExpertsMustBeActiveForGlobalAccess : Bool
    allExpertsMustBeActiveForGlobalAccessIsFalse :
      allExpertsMustBeActiveForGlobalAccess ≡ false

    sparseProductionTracked : Bool
    sparseProductionTrackedIsTrue :
      sparseProductionTracked ≡ true

    broadConditionalReadabilityTracked : Bool
    broadConditionalReadabilityTrackedIsTrue :
      broadConditionalReadabilityTracked ≡ true

    literalBrainMoEArchitecturePromoted : Bool
    literalBrainMoEArchitecturePromotedIsFalse :
      literalBrainMoEArchitecturePromoted ≡ false

canonicalSparseExpertCoalitionBoundary : SparseExpertCoalitionBoundary
canonicalSparseExpertCoalitionBoundary =
  sparseExpertCoalitionBoundary
    false refl
    true refl
    true refl
    false refl
