module DASHI.Vision.Surfel.ReconstructionHandoff where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Vision.Surfel.PromotionOrder
open import DASHI.Vision.Surfel.CoreExpansion

------------------------------------------------------------------------
-- Surface reconstruction is downstream of DASHI selection.  Poisson, BPA,
-- splat meshing, or another backend may consume the selected carrier, but may
-- not silently widen it to unanchored plateau/background support.

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

------------------------------------------------------------------------
-- The handoff contains a trusted core independently of the reconstruction
-- backend selected later.

handoffHasAscendedAnchor :
  {C : SurfelCarrier} →
  (handoff : ReconstructionHandoff C) →
  Agda.Builtin.Sigma.Σ (Surfel C) λ s →
    PromotedCluster.Member (containsAscendedAnchor handoff) s
    × state C s ≡ ascended
handoffHasAscendedAnchor handoff =
  promotedClusterHasAscendedMember (containsAscendedAnchor handoff)

------------------------------------------------------------------------
-- Raw ascended+plateau input has no authority at this boundary.  It must first
-- be converted to a core-expanded selection carrying per-surfel anchors.

data RawAscendedPlateauAuthority : Set where

rawAscendedPlateauCannotBypassSelection :
  RawAscendedPlateauAuthority →
  ⊥
rawAscendedPlateauCannotBypassSelection ()

------------------------------------------------------------------------
-- A backend receipt records only the algorithm used after governance.  It does
-- not upgrade the trust state of its input.

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
