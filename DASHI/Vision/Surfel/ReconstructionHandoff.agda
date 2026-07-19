module DASHI.Vision.Surfel.ReconstructionHandoff where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Empty using (⊥)

open import DASHI.Vision.Surfel.PromotionOrder
open import DASHI.Vision.Surfel.CoreExpansion

data ReconstructionInputTier : Set where
  ascendedCore : ReconstructionInputTier
  coreExpanded : ReconstructionInputTier
  rawAscendedPlateau : ReconstructionInputTier

record ReconstructionHandoff
       (C : SurfelCarrier)
       : Set₁ where
  field
    inputTier : ReconstructionInputTier
    Selected : Surfel C → Set

    selectedIsGoverned :
      {s : Surfel C} →
      Selected s →
      CoreExpandedSelection C s

    containsAscendedAnchor :
      PromotedCluster C

    qualityOrderingChecked : Bool
    qualityOrderingCheckedIsTrue : qualityOrderingChecked ≡ true

open ReconstructionHandoff public

handoffHasAscendedAnchor :
  {C : SurfelCarrier} →
  (handoff : ReconstructionHandoff C) →
  Σ (Surfel C) λ s →
    PromotedCluster.Member (containsAscendedAnchor handoff) s
    × state C s ≡ ascended
handoffHasAscendedAnchor handoff =
  promotedClusterHasAscendedMember (containsAscendedAnchor handoff)

data RawAscendedPlateauAuthority : Set where

rawAscendedPlateauCannotBypassSelection :
  RawAscendedPlateauAuthority →
  ⊥
rawAscendedPlateauCannotBypassSelection ()

data ReconstructionBackend : Set where
  poisson ballPivoting splatMesh : ReconstructionBackend

record BackendReceipt : Set where
  constructor backendReceipt
  field
    backend : ReconstructionBackend
    preservesSelectionBoundary : Bool
    preservesSelectionBoundaryIsTrue :
      preservesSelectionBoundary ≡ true

canonicalPoissonBoundary : BackendReceipt
canonicalPoissonBoundary =
  backendReceipt poisson true refl
