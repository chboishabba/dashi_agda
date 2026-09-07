module DASHI.Cognition.PNF.SensibLawPluralEpistemicRepairMethodologyBidiExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawMaboLandBackEpistemicCompressionEverything as Law
import DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact as Crown
import DASHI.Cognition.PNF.SensibLawLandBackIncomeProjectionNonFactorabilityExact as Income
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueProjectionNonFactorabilityExact as Carbon
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.PluralEpistemicProgressMethodologyBidiExact as Method
import DASHI.Core.ReformulationClosureWithoutFibreRefinementBidiExact as Reform

------------------------------------------------------------------------
-- SENSIBLAW EPISTEMIC COMPRESSION / REMEDY <-> PLURAL EPISTEMIC REPAIR
------------------------------------------------------------------------

compressionAuditQuestion : Law.EpistemicCompressionQuestion
compressionAuditQuestion = Law.canonicalEpistemicCompressionQuestion

crownRewordingStillCannotRecoverAuthority :
  ∀ {Recharted : Set} →
  (rechart : Crown.CrownRecognitionObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Crown.crownRecognitionObserver state))
    Crown.indigenousAuthorityOutcome → ⊥
crownRewordingStillCannotRecoverAuthority =
  Law.posthocRewordingCannotRepairCrownProjection

incomeReweightingStillCannotRecoverLandRelation :
  ∀ {Recharted : Set} →
  (rechart : Income.CashIncomeObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Income.cashIncomeObserver state))
    Income.landAuthorityOutcome → ⊥
incomeReweightingStillCannotRecoverLandRelation =
  Law.posthocReweightingCannotRepairIncomeProjection

biaRelabellingStillCannotRecoverStewardship :
  ∀ {Recharted : Set} →
  (rechart : Carbon.TrustAssetProjection → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Carbon.trustAssetObserver state))
    Carbon.stewardshipValueOutcome → ⊥
biaRelabellingStillCannotRecoverStewardship =
  Law.posthocBiaRelabellingCannotRepairStewardshipProjection

collisionRepairRequiresAddedInformation :
  Law.correctionRequiresAddedInformationWhenCollisionExists
    Law.canonicalDeepEpistemicBoundary ≡ true
collisionRepairRequiresAddedInformation = refl

consultationStillDoesNotCloseFullReparation :
  Billy.ConsultationEqualsFullReparation → ⊥
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
