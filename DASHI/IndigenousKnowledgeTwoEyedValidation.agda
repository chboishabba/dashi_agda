module DASHI.IndigenousKnowledgeTwoEyedValidation where

open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed

------------------------------------------------------------------------
-- Focused import/consumer root for the Indigenous knowledge / storytelling /
-- Two-Eyed Seeing BIDI tranche.
------------------------------------------------------------------------

propositionDoesNotRecoverProvenance :
  NonFactor.FactorsThrough IK.extractedProposition IK.carrierProvenance -> ⊥
propositionDoesNotRecoverProvenance = IK.propositionCannotRecoverProvenance

storySurfaceDoesNotRecoverPermittedInterpretation :
  NonFactor.FactorsThrough IK.heardStory IK.permittedInterpretation -> ⊥
storySurfaceDoesNotRecoverPermittedInterpretation =
  IK.hearingStoryCannotRecoverPermittedInterpretation

sharedObservationDoesNotFuseHistories :
  NonFactor.FactorsThrough TwoEyed.observeKnowledgeHistory TwoEyed.provenance -> ⊥
sharedObservationDoesNotFuseHistories = IK.sharedObservationStillCannotRecoverProvenance

scientificResultDoesNotRecoverConsent :
  NonFactor.FactorsThrough IK.scientificResult IK.accessStatus -> ⊥
scientificResultDoesNotRecoverConsent = IK.scientificResultCannotRecoverConsent

scientificResultDoesNotRecoverBenefitSharing :
  NonFactor.FactorsThrough IK.scientificResult IK.benefitSharingStatus -> ⊥
scientificResultDoesNotRecoverBenefitSharing =
  IK.scientificResultCannotRecoverBenefitSharing

successfulRepairDoesNotRecoverMethod :
  NonFactor.FactorsThrough IK.repairOutcome IK.repairMethod -> ⊥
successfulRepairDoesNotRecoverMethod = IK.workingOutcomeCannotRecoverMethod
