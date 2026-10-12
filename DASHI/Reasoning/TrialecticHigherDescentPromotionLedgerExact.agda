module DASHI.Reasoning.TrialecticHigherDescentPromotionLedgerExact where

------------------------------------------------------------------------
-- TRIALECTIC HIGHER-DESCENT PROMOTION LEDGER
--
-- Current paid layers:
--   * non-discrete finite Grothendieck site;
--   * explicit triadic relational sheaf and T^3/T^9/T^18 descent;
--   * attached irreducible 2-cell and face mediation interface;
--   * relational-depth bidescent;
--   * edge-patch extensional transport groupoid action;
--   * nonconstant Set-valued site presheaf;
--   * concrete cyclic restriction/transport coherence and action 2-cells;
--   * concrete C3 transition cocycle;
--   * Set-level global realization for every compatible local family;
--   * observational uniqueness of those global realizations;
--   * exact obstruction showing the existing three-edge transport index does
--     not cover globalABC or the three vertex objects of the seven-object site.
--
-- The next wall is therefore not another edge C3 calculation.  A genuine
-- groupoid-valued presheaf requires new global/vertex fibre groupoids,
-- restriction functors and general pseudofunctor/cocycle coherence.  Groupoid
-- morphism descent, effective stack descent, typed-iso uniqueness and coherent
-- all-depth face mediation remain open.  Hence 2-sheaf/higher-stack/hypersheaf
-- promotion remains false.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RelationalTrialecticDisambiguationExact as Disambiguation
import DASHI.Core.RelationalTransportDescentSheafExact as Transport
import DASHI.Core.RelationalTransportGroupoidActionExact as GroupoidAction
import DASHI.Foundations.RelationalDepthBidescentExact as Bidescent
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Groth
import DASHI.Foundations.RelationalStageTwelveSiteExact as Site
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as CellDescent
import DASHI.Reasoning.TrialecticGrothendieckCellPresheafExact as CellPresheaf
import DASHI.Reasoning.TrialecticGrothendieckTransportCoherenceExact as TransportCoherence
import DASHI.Core.RelationalTransportActionTwoCellExact as ActionTwoCell
import DASHI.Reasoning.TrialecticGrothendieckTransitionCocycleExact as TransitionCocycle
import DASHI.Reasoning.TrialecticGrothendieckAttachedTwoCellDescentExact as TwoCell
import DASHI.Reasoning.TrialecticSetEffectiveDescentExact as SetEffective
import DASHI.Reasoning.TrialecticRelationalSiteTransportEnrichmentFrontierExact as SiteTransport

data HigherDescentFeature : Set where
  finiteGrothendieckSite : HigherDescentFeature
  triadicSheafDescent : HigherDescentFeature
  structuredT3T9T18Carrier : HigherDescentFeature
  attachedIrreducibleTwoCell : HigherDescentFeature
  faceMediationInterface : HigherDescentFeature
  relationalDepthBidescent : HigherDescentFeature
  typedTransportFamily : HigherDescentFeature
  extensionalTransportGroupoidAction : HigherDescentFeature
  nonconstantSetValuedSitePresheaf : HigherDescentFeature
  cyclicRestrictionTransportCoherence : HigherDescentFeature
  transportActionTwoCellCalculus : HigherDescentFeature
  cyclicTransitionCocycleTwoCell : HigherDescentFeature
  setLevelEffectiveDescentRealization : HigherDescentFeature
  observationalGlobalUniqueness : HigherDescentFeature
  fullSiteTransportCoverageObstruction : HigherDescentFeature

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
featureConstructed extensionalTransportGroupoidAction = true
featureConstructed nonconstantSetValuedSitePresheaf = true
featureConstructed cyclicRestrictionTransportCoherence = true
featureConstructed transportActionTwoCellCalculus = true
featureConstructed cyclicTransitionCocycleTwoCell = true
featureConstructed setLevelEffectiveDescentRealization = true
featureConstructed observationalGlobalUniqueness = true
featureConstructed fullSiteTransportCoverageObstruction = true

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

setEffectiveDescentConstructed :
  featureConstructed setLevelEffectiveDescentRealization ≡ true
setEffectiveDescentConstructed = refl

siteTransportCoverageObstructionConstructed :
  featureConstructed fullSiteTransportCoverageObstruction ≡ true
siteTransportCoverageObstructionConstructed = refl

higherStackStillOpen :
  featureConstructed certifiedHigherStack ≡ false
higherStackStillOpen = refl

hypersheafStillOpen :
  featureConstructed certifiedHypersheaf ≡ false
hypersheafStillOpen = refl

------------------------------------------------------------------------
-- Existing donor boundaries are threaded explicitly.
------------------------------------------------------------------------

grothendieckBoundary : Groth.RelationalStageTwelveGrothendieckBoundary
grothendieckBoundary = Groth.canonicalRelationalStageTwelveGrothendieckBoundary

siteBoundary : Site.RelationalStageTwelveSiteBoundary
siteBoundary = Site.canonicalRelationalStageTwelveSiteBoundary

cellDescentBoundary : CellDescent.TrialecticGrothendieckThreeCellDescentBoundary
cellDescentBoundary = CellDescent.canonicalTrialecticGrothendieckThreeCellDescentBoundary

twoCellBoundary : TwoCell.TrialecticGrothendieckAttachedTwoCellBoundary
twoCellBoundary = TwoCell.canonicalTrialecticGrothendieckAttachedTwoCellBoundary

transportBoundary : Transport.RelationalTransportDescentBoundary
transportBoundary = Transport.canonicalRelationalTransportDescentBoundary

transportGroupoidActionBoundary : GroupoidAction.RelationalTransportGroupoidActionBoundary
transportGroupoidActionBoundary = GroupoidAction.canonicalRelationalTransportGroupoidActionBoundary

cellPresheafBoundary : CellPresheaf.TrialecticGrothendieckCellPresheafBoundary
cellPresheafBoundary = CellPresheaf.canonicalTrialecticGrothendieckCellPresheafBoundary

transportCoherenceBoundary : TransportCoherence.TrialecticGrothendieckTransportCoherenceBoundary
transportCoherenceBoundary = TransportCoherence.canonicalTrialecticGrothendieckTransportCoherenceBoundary

actionTwoCellBoundary : ActionTwoCell.RelationalTransportActionTwoCellBoundary
actionTwoCellBoundary = ActionTwoCell.canonicalRelationalTransportActionTwoCellBoundary

transitionCocycleBoundary : TransitionCocycle.TrialecticGrothendieckTransitionCocycleBoundary
transitionCocycleBoundary = TransitionCocycle.canonicalTrialecticGrothendieckTransitionCocycleBoundary

bidescentBoundary : Bidescent.RelationalDepthBidescentBoundary
bidescentBoundary = Bidescent.canonicalRelationalDepthBidescentBoundary

setEffectiveDescentBoundary : SetEffective.TrialecticSetEffectiveDescentBoundary
setEffectiveDescentBoundary = SetEffective.canonicalTrialecticSetEffectiveDescentBoundary

siteTransportEnrichmentBoundary : SiteTransport.TrialecticRelationalSiteTransportEnrichmentBoundary
siteTransportEnrichmentBoundary = SiteTransport.canonicalTrialecticRelationalSiteTransportEnrichmentBoundary

existingStackPromotionObligation : Disambiguation.StackPromotionObligation
existingStackPromotionObligation = Disambiguation.currentStackPromotionObligation

------------------------------------------------------------------------
-- Exact next cut.
------------------------------------------------------------------------

data NextHigherDescentObligation : Set where
  supplyGlobalVertexFiberGroupoids : NextHigherDescentObligation
  defineRestrictionFunctors : NextHigherDescentObligation
  proveGeneralPseudofunctorCoherence : NextHigherDescentObligation
  proveGeneralCocycleCoherence : NextHigherDescentObligation
  constructGroupoidDescentMorphisms : NextHigherDescentObligation
  proveEffectiveGroupoidDescent : NextHigherDescentObligation
  proveUniquenessUpToTypedIso : NextHigherDescentObligation
  connectTwoCellMediationAcrossDepth : NextHigherDescentObligation

nextHigherDescentObligations : List NextHigherDescentObligation
nextHigherDescentObligations =
  supplyGlobalVertexFiberGroupoids
  ∷ defineRestrictionFunctors
  ∷ proveGeneralPseudofunctorCoherence
  ∷ proveGeneralCocycleCoherence
  ∷ constructGroupoidDescentMorphisms
  ∷ proveEffectiveGroupoidDescent
  ∷ proveUniquenessUpToTypedIso
  ∷ connectTwoCellMediationAcrossDepth
  ∷ []

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data CurrentTrancheIsEffectiveStack : Set where
data CurrentTrancheIsHypersheaf : Set where
data SetEffectiveDescentAutomaticallySuppliesGroupoidDescent : Set where

currentTrancheDoesNotPromoteToEffectiveStack :
  CurrentTrancheIsEffectiveStack → ⊥
currentTrancheDoesNotPromoteToEffectiveStack ()

currentTrancheDoesNotPromoteToHypersheaf :
  CurrentTrancheIsHypersheaf → ⊥
currentTrancheDoesNotPromoteToHypersheaf ()

setEffectiveDescentDoesNotCreateGroupoidDescent :
  SetEffectiveDescentAutomaticallySuppliesGroupoidDescent → ⊥
setEffectiveDescentDoesNotCreateGroupoidDescent ()

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
    extensionalTransportGroupoidActionReady : Bool
    setValuedSitePresheafReady : Bool
    cyclicRestrictionTransportCoherenceReady : Bool
    actionTwoCellCalculusReady : Bool
    cyclicTransitionCocycleReady : Bool
    setLevelEffectiveDescentReady : Bool
    observationalGlobalUniquenessReady : Bool
    siteTransportCoverageObstructionReady : Bool
    strictTransportGroupoidReady : Bool
    groupoidPresheafReady : Bool
    generalPseudofunctorCoherenceReady : Bool
    cocycleTwoMorphismsReady : Bool
    groupoidDescentMorphismsReady : Bool
    effectiveStackReady : Bool
    coherentAllDepthIterationReady : Bool
    hypersheafReady : Bool

open TrialecticHigherDescentPromotionBoundary public

-- Keep the historical constructor and `cocycleTwoMorphismsReady` field name
-- stable for downstream imports; the field now denotes the still-unpaid
-- *general* site-wide cocycle layer, while the concrete C3 cocycle remains
-- separately recorded by `cyclicTransitionCocycleReady`.
canonicalTrialecticHigherDescentPromotionBoundary :
  TrialecticHigherDescentPromotionBoundary
canonicalTrialecticHigherDescentPromotionBoundary =
  trialectic-higher-descent-promotion-boundary
    true true true true true true true true true true true true
    true true true
    false false false false false false false false
