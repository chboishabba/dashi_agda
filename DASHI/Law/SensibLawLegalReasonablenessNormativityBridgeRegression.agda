module DASHI.Law.SensibLawLegalReasonablenessNormativityBridgeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawLegalReasonablenessNormativityBridgeExact as Bridge

legalReasonablenessParentRegression :
  Bridge.legalReasonablenessParentReused Bridge.canonicalLegalReasonablenessNormativityBoundary
  ≡ true
legalReasonablenessParentRegression = refl

normProductionParentRegression :
  Bridge.normProductionReasonablenessBridgeReused Bridge.canonicalLegalReasonablenessNormativityBoundary
  ≡ true
normProductionParentRegression = refl

lawfulRangeNeutralityRegression :
  Bridge.lawfulRangeAutomaticallyPoliticalNeutrality Bridge.canonicalLegalReasonablenessNormativityBoundary
  ≡ false
lawfulRangeNeutralityRegression = refl

relevantFactorsValueFreeRegression :
  Bridge.legallyRelevantFactorSetAutomaticallyValueFree Bridge.canonicalLegalReasonablenessNormativityBoundary
  ≡ false
relevantFactorsValueFreeRegression = refl

judicialRestraintEndorsementRegression :
  Bridge.judicialRestraintAutomaticallyNormativeEndorsement Bridge.canonicalLegalReasonablenessNormativityBoundary
  ≡ false
judicialRestraintEndorsementRegression = refl

politicalCritiqueLegalInvalidityRegression :
  Bridge.politicalCritiqueAutomaticallyLegalInvalidity Bridge.canonicalLegalReasonablenessNormativityBoundary
  ≡ false
politicalCritiqueLegalInvalidityRegression = refl

coexistenceRegression :
  Bridge.legalApplicationAndNormativeCritiqueCanRemainDistinct Bridge.canonicalLegalReasonablenessNormativityBoundary
  ≡ true
coexistenceRegression = refl
