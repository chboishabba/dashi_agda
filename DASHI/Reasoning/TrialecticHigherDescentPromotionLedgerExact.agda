module DASHI.Reasoning.TrialecticHigherDescentPromotionLedgerExact where

------------------------------------------------------------------------
-- TRIALECTIC HIGHER-DESCENT PROMOTION LEDGER
--
-- This module records exactly what the current relational/trialectic stack has
-- constructed after the structured 27-cell / Grothendieck / attached-2-cell
-- tranche, and what is still missing before stronger categorical language is
-- licensed.
--
-- Positive results:
--   * genuine non-discrete finite Grothendieck site;
--   * explicit triadic relational sheaf interface;
--   * T^3 overlap sections, T^9 edge sections, T^18 global boundary section;
--   * exact gluing/restriction recovery;
--   * attached irreducible 2-cell beyond ordinary Cech one-skeleton descent;
--   * explicit face-mediation interface to a next-depth T^3 cell;
--   * independent relational-depth bidescent interface with commuting squares.
--
-- Still open:
--   * a transport groupoid with typed composition/identity/inverse laws;
--   * a groupoid-valued presheaf over the relational site;
--   * restriction/transport pseudofunctorial coherence;
--   * overlap cocycle 2-morphisms and their coherence;
--   * descent morphisms and effective descent;
--   * uniqueness up to typed isomorphism/equivalence;
--   * coherent iteration of the attached 2-cell across all depths.
--
-- Therefore "2-sheaf", "higher stack", and "hypersheaf" remain unpromoted.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RelationalTrialecticDisambiguationExact as Disambiguation
import DASHI.Core.RelationalTransportDescentSheafExact as Transport
import DASHI.Foundations.RelationalDepthBidescentExact as Bidescent
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Groth
import DASHI.Foundations.RelationalStageTwelveSiteExact as Site
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as CellDescent
import DASHI.Reasoning.TrialecticGrothendieckAttachedTwoCellDescentExact as TwoCell

data HigherDescentFeature : Set where
  finiteGrothendieckSite : HigherDescentFeature
  triadicSheafDescent : HigherDescentFeature
  structuredT3T9T18Carrier : HigherDescentFeature
  attachedIrreducibleTwoCell : HigherDescentFeature
  faceMediationInterface : HigherDescentFeature
  relationalDepthBidescent : HigherDescentFeature
  typedTransportFamily : HigherDescentFeature

  transportGroupoid : HigherDescentFeature
  groupoidValuedPresheaf : HigherDescentFeature
  restrictionTransportPseudofunctor : HigherDescentFeature
  overlapCocycleTwoMorphisms : HigherDescentFeature
  effectiveDescentMorphisms : HigherDescentFeature
  uniquenessUpToTypedIso : HigherDescentFeature
  coherentAllDepthIteration : HigherDescentFeature
  certifiedTwoSheaf : HigherDescentFeature
  certifiedHigherStack : HigherDescentFeature
  certifiedHypersheaf : HigherDescentFeature

featureConstructed : HigherDescentFeature → Bool
featureConstructed finiteGrothendieckSite = true
featureConstructed triadicSheafDescent = true
featureConstructed structuredT3T9T18Carrier = true
featureConstructed attachedIrreducibleTwoCell = true
featureConstructed faceMediationInterface = true
featureConstructed relationalDepthBidescent = true
featureConstructed typedTransportFamily = true

featureConstructed transportGroupoid = false
featureConstructed groupoidValuedPresheaf = false
featureConstructed restrictionTransportPseudofunctor = false
featureConstructed overlapCocycleTwoMorphisms = false
featureConstructed effectiveDescentMorphisms = false
featureConstructed uniquenessUpToTypedIso = false
featureConstructed coherentAllDepthIteration = false
featureConstructed certifiedTwoSheaf = false
featureConstructed certifiedHigherStack = false
featureConstructed certifiedHypersheaf = false

grothendieckSiteConstructed :
  featureConstructed finiteGrothendieckSite ≡ true
grothendieckSiteConstructed = refl

triadicSheafConstructed :
  featureConstructed triadicSheafDescent ≡ true
triadicSheafConstructed = refl

attachedTwoCellConstructed :
  featureConstructed attachedIrreducibleTwoCell ≡ true
attachedTwoCellConstructed = refl

higherStackStillOpen :
  featureConstructed certifiedHigherStack ≡ false
higherStackStillOpen = refl

hypersheafStillOpen :
  featureConstructed certifiedHypersheaf ≡ false
hypersheafStillOpen = refl

------------------------------------------------------------------------
-- Existing donor boundaries are threaded explicitly.
------------------------------------------------------------------------

grothendieckBoundary :
  Groth.RelationalStageTwelveGrothendieckBoundary
grothendieckBoundary =
  Groth.canonicalRelationalStageTwelveGrothendieckBoundary

siteBoundary :
  Site.RelationalStageTwelveSiteBoundary
siteBoundary =
  Site.canonicalRelationalStageTwelveSiteBoundary

cellDescentBoundary :
  CellDescent.TrialecticGrothendieckThreeCellDescentBoundary
cellDescentBoundary =
  CellDescent.canonicalTrialecticGrothendieckThreeCellDescentBoundary

twoCellBoundary :
  TwoCell.TrialecticGrothendieckAttachedTwoCellBoundary
twoCellBoundary =
  TwoCell.canonicalTrialecticGrothendieckAttachedTwoCellBoundary

transportBoundary :
  Transport.RelationalTransportDescentBoundary
transportBoundary =
  Transport.canonicalRelationalTransportDescentBoundary

bidescentBoundary :
  Bidescent.RelationalDepthBidescentBoundary
bidescentBoundary =
  Bidescent.canonicalRelationalDepthBidescentBoundary

existingStackPromotionObligation :
  Disambiguation.StackPromotionObligation
existingStackPromotionObligation =
  Disambiguation.currentStackPromotionObligation

------------------------------------------------------------------------
-- Exact next cut.
------------------------------------------------------------------------

data NextHigherDescentObligation : Set where
  constructTransportComposition : NextHigherDescentObligation
  proveTransportIdentityLaws : NextHigherDescentObligation
  proveTransportCompositionLaws : NextHigherDescentObligation
  indexTransportOverRelationalSite : NextHigherDescentObligation
  proveRestrictionTransportCoherence : NextHigherDescentObligation
  constructOverlapCocycleTwoMorphisms : NextHigherDescentObligation
  proveCocycleCoherence : NextHigherDescentObligation
  constructDescentMorphisms : NextHigherDescentObligation
  proveEffectiveDescent : NextHigherDescentObligation
  proveUniquenessUpToTypedIso : NextHigherDescentObligation
  connectTwoCellMediationAcrossDepth : NextHigherDescentObligation

nextHigherDescentObligations :
  List NextHigherDescentObligation
nextHigherDescentObligations =
  constructTransportComposition
  ∷ proveTransportIdentityLaws
  ∷ proveTransportCompositionLaws
  ∷ indexTransportOverRelationalSite
  ∷ proveRestrictionTransportCoherence
  ∷ constructOverlapCocycleTwoMorphisms
  ∷ proveCocycleCoherence
  ∷ constructDescentMorphisms
  ∷ proveEffectiveDescent
  ∷ proveUniquenessUpToTypedIso
  ∷ connectTwoCellMediationAcrossDepth
  ∷ []

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data CurrentTrancheIsEffectiveStack : Set where
data CurrentTrancheIsHypersheaf : Set where
data AttachedTwoCellAloneSuppliesCocycleCoherence : Set where

currentTrancheDoesNotPromoteToEffectiveStack :
  CurrentTrancheIsEffectiveStack → ⊥
currentTrancheDoesNotPromoteToEffectiveStack ()

currentTrancheDoesNotPromoteToHypersheaf :
  CurrentTrancheIsHypersheaf → ⊥
currentTrancheDoesNotPromoteToHypersheaf ()

attachedTwoCellDoesNotByItselfSupplyCocycleCoherence :
  AttachedTwoCellAloneSuppliesCocycleCoherence → ⊥
attachedTwoCellDoesNotByItselfSupplyCocycleCoherence ()

record TrialecticHigherDescentPromotionBoundary : Set where
  constructor trialectic-higher-descent-promotion-boundary
  field
    grothendieckSiteReady : Bool
    sheafDescentReady : Bool
    structuredCarrierReady : Bool
    attachedTwoCellReady : Bool
    faceMediationInterfaceReady : Bool
    depthBidescentInterfaceReady : Bool
    transportFamilyReady : Bool
    transportGroupoidReady : Bool
    groupoidPresheafReady : Bool
    cocycleTwoMorphismsReady : Bool
    effectiveStackReady : Bool
    coherentAllDepthIterationReady : Bool
    hypersheafReady : Bool

canonicalTrialecticHigherDescentPromotionBoundary :
  TrialecticHigherDescentPromotionBoundary
canonicalTrialecticHigherDescentPromotionBoundary =
  trialectic-higher-descent-promotion-boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
