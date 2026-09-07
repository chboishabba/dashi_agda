module DASHI.Cognition.PNF.SensibLawPluralEpistemicRepairMethodologyBidiExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawMaboLandBackEpistemicCompressionEverything as Law
import DASHI.Core.PluralEpistemicProgressMethodologyBidiExact as Method
import DASHI.Core.PairIndexedInformationLossLocusBidiExact as Loss
import DASHI.Core.ReformulationClosureWithoutFibreRefinementBidiExact as Reform

------------------------------------------------------------------------
-- SENSIBLAW EPISTEMIC COMPRESSION / REMEDY <-> PLURAL EPISTEMIC REPAIR
--
-- The existing SensibLaw capstone already asks which distinctions an observer
-- makes impossible to see, and already proves that post-hoc relabelling cannot
-- recover several erased Country/authority relations.  The plural methodology
-- identifies this as one route among several: new information may be required,
-- while reformulation may close a narrower question without pretending to
-- reconstruct the hidden relation.
------------------------------------------------------------------------

compressionAuditQuestion = Law.canonicalEpistemicCompressionQuestion

crownRewordingStillCannotRecoverAuthority =
  Law.posthocRewordingCannotRepairCrownProjection

incomeReweightingStillCannotRecoverLandRelation =
  Law.posthocReweightingCannotRepairIncomeProjection

biaRelabellingStillCannotRecoverStewardship =
  Law.posthocBiaRelabellingCannotRepairStewardshipProjection

collisionRepairRequiresAddedInformation :
  Law.correctionRequiresAddedInformationWhenCollisionExists
    Law.canonicalDeepEpistemicBoundary ≡ true
collisionRepairRequiresAddedInformation = refl

consultationStillDoesNotCloseFullReparation =
  Law.billyConsultationDoesNotCloseFullReparation

reformulationMayCloseWithoutClaimingRelationRecovery :
  Reform.QuestionClosed Reform.reformulatedQuestion
reformulationMayCloseWithoutClaimingRelationRecovery =
  Reform.reformulatedQuestionClosed

sensibLawMayRequireNewCoordinate : Method.EpistemicProgressRoute
sensibLawMayRequireNewCoordinate = Method.addNewCoordinate

sensibLawMayReformulateQuestion : Method.EpistemicProgressRoute
sensibLawMayReformulateQuestion = Method.reformulateQuestion

data RelabellingRestoresErasedCountryAuthority : Set where
data NarrowQuestionClosureEqualsFullRemedy : Set where

relabellingDoesNotRestoreErasedCountryAuthority :
  RelabellingRestoresErasedCountryAuthority → ⊥
relabellingDoesNotRestoreErasedCountryAuthority ()

narrowQuestionClosureDoesNotEqualFullRemedy :
  NarrowQuestionClosureEqualsFullRemedy → ⊥
narrowQuestionClosureDoesNotEqualFullRemedy ()

record SensibLawPluralEpistemicRepairBoundary : Set where
  constructor sensiblaw-plural-epistemic-repair-boundary
  field
    collisionMayRequireAddedInformation : Bool
    deterministicRelabellingMayRestoreErasedRelation : Bool
    reformulationMayCloseNarrowerConsumer : Bool
    narrowerClosureEqualsFullReparation : Bool
    consultationTransfersCommunityAuthority : Bool
    formalRepairCreatesLegalAuthority : Bool

canonicalSensibLawPluralEpistemicRepairBoundary :
  SensibLawPluralEpistemicRepairBoundary
canonicalSensibLawPluralEpistemicRepairBoundary =
  sensiblaw-plural-epistemic-repair-boundary true false true false false false
