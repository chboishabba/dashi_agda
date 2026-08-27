module DASHI.Biology.RelationalEmbodiedCoregulationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- RELATIONAL CO-REGULATION WITHOUT INSTITUTIONAL ANTHROPOMORPHISM
------------------------------------------------------------------------

data BodyRegime : Set where
  regulated mobilised : BodyRegime

data SocialSignal : Set where
  calmingSignal escalatingSignal : SocialSignal

record DyadState : Set where
  constructor dyadState
  field
    firstBody : BodyRegime
    secondBody : BodyRegime

open DyadState public

bothMobilised : DyadState
bothMobilised = dyadState mobilised mobilised

bothRegulated : DyadState
bothRegulated = dyadState regulated regulated

interactionUpdate : SocialSignal → DyadState → DyadState
interactionUpdate calmingSignal state = bothRegulated
interactionUpdate escalatingSignal state = bothMobilised

calmingCanCoregulateBoth :
  interactionUpdate calmingSignal bothMobilised ≡ bothRegulated
calmingCanCoregulateBoth = refl

escalatingCanShiftBoth :
  interactionUpdate escalatingSignal bothRegulated ≡ bothMobilised
escalatingCanShiftBoth = refl

data CollectiveAttractor : Set where
  escalationAttractor mutualCalmingAttractor mixedAttractor : CollectiveAttractor

collectiveAttractor : DyadState → CollectiveAttractor
collectiveAttractor (dyadState mobilised mobilised) = escalationAttractor
collectiveAttractor (dyadState regulated regulated) = mutualCalmingAttractor
collectiveAttractor (dyadState mobilised regulated) = mixedAttractor
collectiveAttractor (dyadState regulated mobilised) = mixedAttractor

attractorsRemainDistinct :
  collectiveAttractor bothMobilised
  ≡ collectiveAttractor bothRegulated → ⊥
attractorsRemainDistinct ()

------------------------------------------------------------------------
-- Institutions alter world-option geometry; they do not receive a body-state
-- coordinate.
------------------------------------------------------------------------

data InstitutionalProcedure : Set where
  closedProcedure openProcedure : InstitutionalProcedure

data WorldRoute : Set where
  reviewRoute supportRoute : WorldRoute

routeAvailable : InstitutionalProcedure → WorldRoute → Bool
routeAvailable closedProcedure reviewRoute = false
routeAvailable closedProcedure supportRoute = true
routeAvailable openProcedure reviewRoute = true
routeAvailable openProcedure supportRoute = true

procedureChangesWorldReviewRoute :
  routeAvailable closedProcedure reviewRoute
  ≡ routeAvailable openProcedure reviewRoute → ⊥
procedureChangesWorldReviewRoute ()

record RelationalEmbodimentBoundary : Set where
  constructor relationalEmbodimentBoundary
  field
    dyadicSignalsCanCoupleBodyDynamics : Bool
    institutionHasCortisol : Bool
    institutionIsLiteralNervousSystem : Bool
    institutionCanChangeWorldOptionGeometry : Bool
    socialSignalDeterministicallyDiagnosesRelationship : Bool

canonicalRelationalEmbodimentBoundary : RelationalEmbodimentBoundary
canonicalRelationalEmbodimentBoundary =
  relationalEmbodimentBoundary true false false true false
