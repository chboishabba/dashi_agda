module DASHI.Governance.BOMFordhamMediaClaimAuditValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.BOMFordhamMediaClaimAuditExact as A
import DASHI.Governance.TypedGenealogyEdgeExact as Typed
import DASHI.Core.IntersectionalNonFactorability as INF

historicalErrorCannotProveFraud :
  A.rawDigitisationErrorImpliesDeliberateFraud A.canonicalNonPromotionBoundary ≡ false
historicalErrorCannotProveFraud = refl

headlineCannotProveFraud :
  A.publishedAccusatoryHeadlineProvesFraud A.canonicalNonPromotionBoundary ≡ false
headlineCannotProveFraud = refl

digitisationAndHomogenisationDistinct :
  A.homogenisationIsHistoricalTranscription A.canonicalNonPromotionBoundary ≡ false
digitisationAndHomogenisationDistinct = refl

punchCardCausationStillHypothetical :
  A.unverifiedCauseIsEstablishedCause A.canonicalNonPromotionBoundary ≡ false
punchCardCausationStillHypothetical = refl

ownershipDoesNotEstablishCommand :
  A.publisherOwnershipProvesEditorialDirection A.canonicalNonPromotionBoundary ≡ false
ownershipDoesNotEstablishCommand = refl

similarRhetoricDoesNotProveNetwork :
  A.sameRhetoricProvesTPUSAOrBannonControl A.canonicalNonPromotionBoundary ≡ false
similarRhetoricDoesNotProveNetwork = refl

bondiBroadcastIsNotAnInflammatoryQuote :
  A.bondiCoverageProvesInflammatoryContent A.canonicalNonPromotionBoundary ≡ false
bondiBroadcastIsNotAnInflammatoryQuote = refl

hansonMentionIsNotCollaboration :
  A.topicMentionProvesHansonCollaboration A.canonicalNonPromotionBoundary ≡ false
hansonMentionIsNotCollaboration = refl

kyleRivalryIsNotCoordination :
  A.radioRivalryProvesKyleCoordination A.canonicalNonPromotionBoundary ≡ false
kyleRivalryIsNotCoordination = refl

correctionRequiresSameObjectComparison :
  A.correctionNeedsSameObjectDataComparison A.canonicalNonPromotionBoundary ≡ true
correctionRequiresSameObjectComparison = refl

confirmedErrorIsHistoricalDigitalInput :
  A.layer A.confirmedDuplicate ≡ A.digitisedHistoricalObservation
confirmedErrorIsHistoricalDigitalInput = refl

punchCardsAreInstitutionHypothesis :
  A.status A.possiblePunchCards ≡ A.institutionHypothesised
punchCardsAreInstitutionHypothesis = refl

unseenAuditIsNotAcquired :
  A.canonicalOriginalAuditStatus ≡ A.notAcquired
unseenAuditIsNotAcquired = refl

publisherEdgeIsPersonnelNotTransfer :
  Typed.relationKind A.fordhamTo2GB ≡ Typed.personnelContinuity
publisherEdgeIsPersonnelNotTransfer = refl

ownershipEdgeIsOrganisationalNotTransfer :
  Typed.relationKind A.radioToTapt ≡ Typed.organisationalContinuity
ownershipEdgeIsOrganisationalNotTransfer = refl

amplificationEdgeIsAdjacencyNotTransfer :
  Typed.relationKind A.fordhamAuditBroadcast ≡ Typed.audienceAdjacency
amplificationEdgeIsAdjacencyNotTransfer = refl

noFraudPromotion : A.DuplicateImpliesFraud → ⊥
noFraudPromotion = A.duplicateDoesNotProveFraud

noTPUSAPromotion : A.RhetoricImpliesBannonControl → ⊥
noTPUSAPromotion = A.rhetoricDoesNotProveBannonControl

noMediaOwnerIntentPromotion : A.OwnershipImpliesEditorialOrder → ⊥
noMediaOwnerIntentPromotion = A.ownershipDoesNotProveEditorialOrder

noBondiInflammatoryPromotion :
  A.BondiCoverageImpliesInflammatorySpeech → ⊥
noBondiInflammatoryPromotion = A.bondiCoverageDoesNotProveInflammatorySpeech


-- From the reused, already-canonical nonfactorability theorem: reporting
-- every day as a whole degree is not an injective map back to latent
-- tenths-of-a-degree samples. Does NOT give a probability for real Palmerville
-- 2004 weather or verify the disputed 17 original readings.

palmervilleDistinctHistoriesSameSeventeenRoundedObservations :
  A.roundedSeventeenDayObservation A.allDaysExactly310Tenths ≡
  A.roundedSeventeenDayObservation A.firstDay306OtherDaysVary
palmervilleDistinctHistoriesSameSeventeenRoundedObservations = refl

palmervilleDifferentLatentDayOneIsNotRecoverable :
  A.firstDayTenths A.allDaysExactly310Tenths ≡
  A.firstDayTenths A.firstDay306OtherDaysVary → ⊥
palmervilleDifferentLatentDayOneIsNotRecoverable =
  A.palmervilleDifferentUnderlyingValue

palmervilleMeasurementPrecisionNotAProbability :
  INF.FactorsThrough A.roundedSeventeenDayObservation A.firstDayTenths → ⊥
palmervilleMeasurementPrecisionNotAProbability =
  A.palmervilleRoundedValuesCannotDetermineUnroundedDayOne
