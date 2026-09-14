module DASHI.Law.SensibLawMaboDenaturalisationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawMaboDenaturalisationExact as Mabo

parentNaturalisationReusedRegression :
  Mabo.parentInstitutionalNormProductionReused
    Mabo.canonicalMaboDenaturalisationBoundary
  ≡ true
parentNaturalisationReusedRegression = refl

maboIdentityRetainedRegression :
  Mabo.maboNo2IdentityRetained
    Mabo.canonicalMaboDenaturalisationBoundary
  ≡ true
maboIdentityRetainedRegression = refl

laterHcaInterpretationPaidRegression :
  Mabo.laterHighCourtRecognitionSurvivalStatementPaid
    Mabo.canonicalMaboDenaturalisationBoundary
  ≡ true
laterHcaInterpretationPaidRegression = refl

recognitionCreatesUnderlyingRightsRegression :
  Mabo.judicialRecognitionAutomaticallyCreatesUnderlyingRights
    Mabo.canonicalMaboDenaturalisationBoundary
  ≡ false
recognitionCreatesUnderlyingRightsRegression = refl

nonRecognitionEstablishesNonExistenceRegression :
  Mabo.priorLegalNonRecognitionAutomaticallyEstablishesUnderlyingNonExistence
    Mabo.canonicalMaboDenaturalisationBoundary
  ≡ false
nonRecognitionEstablishesNonExistenceRegression = refl

maboAutomaticallyResolvesSovereigntyRegression :
  Mabo.maboRecognitionAutomaticallyResolvesSovereigntyQuestion
    Mabo.canonicalMaboDenaturalisationBoundary
  ≡ false
maboAutomaticallyResolvesSovereigntyRegression = refl

structuralNaturalisationEqualsHistoricalEquivalenceRegression :
  Mabo.structuralDenaturalisationAutomaticallyEstablishesCrossHistoricalEquivalence
    Mabo.canonicalMaboDenaturalisationBoundary
  ≡ false
structuralNaturalisationEqualsHistoricalEquivalenceRegression = refl
