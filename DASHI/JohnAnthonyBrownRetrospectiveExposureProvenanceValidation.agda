module DASHI.JohnAnthonyBrownRetrospectiveExposureProvenanceValidation where

open import DASHI.Core.Prelude

import DASHI.Culture.JohnAnthonyBrownRetrospectiveExposureProvenanceExact as P

retrospectiveReportIsEvidence :
  P.RetrospectiveExposureBoundary.retrospectiveReportIsEvidence
    P.canonicalRetrospectiveExposureBoundary
  ≡ true
retrospectiveReportIsEvidence = refl

retrospectiveNotContemporaneous :
  P.RetrospectiveReportPromotesContemporaneousRecord -> ⊥
retrospectiveNotContemporaneous =
  P.retrospectiveReportDoesNotPromoteContemporaneousRecord

missingRecordNotFalseRecall : P.NoContemporaneousRecordPromotesFalseRecall -> ⊥
missingRecordNotFalseRecall =
  P.absenceOfContemporaneousRecordDoesNotPromoteFalseRecall

interactionNotLatentFear : P.ContemporaneousInteractionPromotesLatentFear -> ⊥
interactionNotLatentFear = P.contemporaneousInteractionDoesNotPromoteLatentFear

adultMeaningNotChildhoodMeaningIdentity :
  P.AdultMeaningPromotesChildhoodMeaningIdentity -> ⊥
adultMeaningNotChildhoodMeaningIdentity =
  P.adultMeaningDoesNotPromoteChildhoodMeaningIdentity

adultFollowupProspective :
  P.TemporalDesignSplit.futureAdultOutcomesMeasuredProspectively
    P.johnAnthonyBrownTemporalSplit
  ≡ true
adultFollowupProspective = refl

adultFollowupDoesNotMakeExposureProspective :
  P.TemporalDesignSplit.prospectiveAdultFollowupMakesChildhoodExposureProspective
    P.johnAnthonyBrownTemporalSplit
  ≡ false
adultFollowupDoesNotMakeExposureProspective = refl

triangulationCanIncreaseConfidence :
  P.RetrospectiveExposureBoundary.triangulationCanIncreaseConfidence
    P.canonicalRetrospectiveExposureBoundary
  ≡ true
triangulationCanIncreaseConfidence = refl

triangulationDoesNotMakeInterpretationUnique :
  P.RetrospectiveExposureBoundary.triangulationMakesInterpretationUnique
    P.canonicalRetrospectiveExposureBoundary
  ≡ false
triangulationDoesNotMakeInterpretationUnique = refl
