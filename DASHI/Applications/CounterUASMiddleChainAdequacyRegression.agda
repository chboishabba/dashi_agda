module DASHI.Applications.CounterUASMiddleChainAdequacyRegression where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASMiddleChainAdequacyExact as Middle
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

record CounterUASMiddleChainAdequacyRegression : Set₁ where
  constructor counterUASMiddleChainAdequacyRegression
  field
    observationSurfaceHasAssociationAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        Middle.observationSurfaceProjection
        Middle.associationSemantics
        Middle.associationStatusQuery
    observationSurfaceAloneCannotDetermineAssociation :
      Adequacy.AdequateFor
        Middle.observationSurfaceProjection
        Middle.associationSemantics
        Middle.associationStatusQuery → ⊥
    observationAndAssociationLineageDetermineAssociation :
      Adequacy.AdequateFor
        Middle.observationAndAssociationProjection
        Middle.associationSemantics
        Middle.associationStatusQuery
    fusedObservationsDoNotCreateSameObjectAssociation :
      Middle.fusedObservationsCreateSameObjectAssociation ≡ false
    classificationOnlyHasThreatAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        Middle.classificationOnlyProjection
        Middle.threatSemantics
        Middle.threatAssessmentQuery
    classificationAloneCannotDetermineThreat :
      Adequacy.AdequateFor
        Middle.classificationOnlyProjection
        Middle.threatSemantics
        Middle.threatAssessmentQuery → ⊥
    classificationAndContextDetermineThreat :
      Adequacy.AdequateFor
        Middle.classificationAndContextProjection
        Middle.threatSemantics
        Middle.threatAssessmentQuery
    classifiedUASDoesNotCreateHostility :
      Middle.classifiedUASCreatesHostility ≡ false
    fusionConfidenceDoesNotCreateHostility :
      Middle.fusionConfidenceCreatesHostility ≡ false
    middleChainDoesNotCreateMitigationAuthority :
      Middle.middleChainCreatesMitigationAuthority ≡ false

canonicalCounterUASMiddleChainAdequacyRegression :
  CounterUASMiddleChainAdequacyRegression
canonicalCounterUASMiddleChainAdequacyRegression =
  counterUASMiddleChainAdequacyRegression
    Middle.observationSurfaceAssociationAdequacyDefect
    Middle.observationSurfaceCannotDetermineAssociation
    Middle.observationAndAssociationDetermineAssociation
    refl
    Middle.classificationOnlyThreatAdequacyDefect
    Middle.classificationOnlyCannotDetermineThreat
    Middle.classificationAndContextDetermineThreat
    refl
    refl
    refl
