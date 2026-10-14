module DASHI.Reasoning.TrialecticHypersheafHypercoverFrontierExact where

------------------------------------------------------------------------
-- HYPERSHEAF / HYPERCOVER FRONTIER
--
-- The concrete triadic-site stack and its phase 2-cell layer are now paid.
-- The remaining word "hypersheaf" is reserved for a stronger hyperdescent
-- claim.  This owner makes that final bridge explicit rather than hiding it
-- behind a generic false flag.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticWavePhaseHigherStackExact as Higher
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric

higherBoundary : Higher.TrialecticWavePhaseHigherStackBoundary
higherBoundary = Higher.canonicalTrialecticWavePhaseHigherStackBoundary

hyperfabricBoundary : Hyperfabric.TypedHyperfabricAuthorityBoundary
hyperfabricBoundary = Hyperfabric.canonicalTypedHyperfabricAuthorityBoundary

higherStackPrerequisitePaid :
  Higher.certifiedHigherStackOnTriadicSite higherBoundary ≡ true
higherStackPrerequisitePaid = refl

higherArityHyperfabricPrerequisitePaid :
  Hyperfabric.higherArityRelationsRepresentable hyperfabricBoundary ≡ true
higherArityHyperfabricPrerequisitePaid = refl

stalkRestrictionPrerequisitePaid :
  Hyperfabric.restrictionMapsRepresentable hyperfabricBoundary ≡ true
stalkRestrictionPrerequisitePaid = refl

------------------------------------------------------------------------
-- Two legitimate promotion routes.
--
-- Route A supplies direct descent for the chosen hypercover notion.
-- Route B supplies a theorem/adapter proving that the already-constructed
-- 1-truncated groupoid stack is hypercomplete in that hypercover semantics.
------------------------------------------------------------------------

record HypercoverDescentReceipt : Set₁ where
  field
    Hypercover : Set
    hypercoverDescent : Hypercover → Set
    everyDeclaredHypercoverDescends :
      (cover : Hypercover) → hypercoverDescent cover

record TruncatedStackHypercompleteReceipt : Set₁ where
  field
    hypercomplete : Set
    oneTruncatedStackImpliesHypercomplete : hypercomplete

record HypersheafPromotionReceipt : Set₁ where
  constructor hypersheaf-promotion-receipt
  field
    directHypercoverReceipt : HypercoverDescentReceipt

record HypersheafPromotionViaTruncation : Set₁ where
  constructor hypersheaf-promotion-via-truncation
  field
    truncationReceipt : TruncatedStackHypercompleteReceipt

------------------------------------------------------------------------
-- No fake inhabitant is manufactured here.  Either route is sufficient once
-- supplied, and all lower prerequisites are already discharged.
------------------------------------------------------------------------

promoteFromDirectHypercover :
  HypersheafPromotionReceipt → Bool
promoteFromDirectHypercover receipt = true

promoteFromTruncation :
  HypersheafPromotionViaTruncation → Bool
promoteFromTruncation receipt = true

record TrialecticHypersheafHypercoverFrontierBoundary : Set where
  constructor trialectic-hypersheaf-hypercover-frontier-boundary
  field
    higherStackPrerequisiteReady : Bool
    typedHyperfabricPrerequisiteReady : Bool
    effectiveObjectMorphismDescentReady : Bool
    generalTwoCellCocycleReady : Bool
    policyIndexedDepthReady : Bool
    directHypercoverAPIAlreadyFoundInRepo : Bool
    truncationHypercompleteTheoremAlreadyWelded : Bool
    allNonHypercoverPrerequisitesPaid : Bool
    hypersheafPromotionNowHasSingleTypedFrontier : Bool

open TrialecticHypersheafHypercoverFrontierBoundary public

canonicalTrialecticHypersheafHypercoverFrontierBoundary :
  TrialecticHypersheafHypercoverFrontierBoundary
canonicalTrialecticHypersheafHypercoverFrontierBoundary =
  trialectic-hypersheaf-hypercover-frontier-boundary
    true true true true true
    false false
    true true
