module DASHI.Law.HerzogMultiSourceMaboValidation where

open import DASHI.Core.Prelude

import DASHI.Law.HerzogClassificationMultiSourceJoinExact as Join
import DASHI.Law.MaboHerzogMultiSourceProjectionCrossPollinationExact as Cross

fourCopiesRemainDependent :
  Join.atLeastTwoIndependentProducersClosed Join.canonicalFourCopiesOneProducer ≡ false
fourCopiesRemainDependent = refl

currentCorroborationStillNeedsCorpus :
  Join.firstJoinResidual Join.threatPropositionHasIndependentCorroboration
    Join.canonicalCurrentJoinCutset ≡ Join.corpusResidual
currentCorroborationStillNeedsCorpus = refl

countryMeaningStillNeedsLiteralAtom :
  Join.firstJoinResidual Join.countryMeaningAppearsInThreatInput
    Join.canonicalCurrentJoinCutset ≡ Join.countryMeaningResidual
countryMeaningStillNeedsLiteralAtom = refl

repeatedThreatLanguageDoesNotProveClassificationCause :
  Join.repeatedThreatLanguageProvesClassificationCausation
    Join.canonicalMultiSourceJoinBoundary ≡ false
repeatedThreatLanguageDoesNotProveClassificationCause = refl

repeatedThreatLanguageDoesNotProveIncidentCause :
  Join.repeatedThreatLanguageProvesIncidentCausation
    Join.canonicalMultiSourceJoinBoundary ≡ false
repeatedThreatLanguageDoesNotProveIncidentCause = refl

maboMultiplicityDoesNotCreateAuthority :
  Cross.repeatedCrownRecognitionCreatesCountryAuthority
    Cross.canonicalMaboHerzogMultiplicityBoundary ≡ false
maboMultiplicityDoesNotCreateAuthority = refl

sharedFailureDoesNotMergeHistories :
  Cross.sharedMultiplicityFailureMakesHistoriesIdentical
    Cross.canonicalMaboHerzogMultiplicityBoundary ≡ false
sharedFailureDoesNotMergeHistories = refl
