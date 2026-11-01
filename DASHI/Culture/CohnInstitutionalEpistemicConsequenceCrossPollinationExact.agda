module DASHI.Culture.CohnInstitutionalEpistemicConsequenceCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.CohnInstitutionalNormReasonablenessEvidenceCrossPollinationExact as LegalEvidence
import DASHI.Law.SensibLawEpistemicConsequenceBoundaryExact as Consequence

------------------------------------------------------------------------
-- COHN / INSTITUTIONAL EVIDENCE × EPISTEMIC CONSEQUENCE
--
-- Thin composition owner only.  It does not create a new legal doctrine,
-- proportionality rule, evidentiary threshold, or Cohn-authored theorem.
--
-- Core separation:
--
--   evidence/consumer adequacy
--      != consequence severity/reversibility
--
-- and neither direction may be recovered from the other on this finite
-- witness.  The parent SensibLaw owner separately retains uncertainty,
-- severity and reversibility as independent analytical coordinates.
------------------------------------------------------------------------

parentLegalEvidenceBoundary :
  LegalEvidence.CohnInstitutionalLegalEvidenceBoundary
parentLegalEvidenceBoundary =
  LegalEvidence.canonicalCohnInstitutionalLegalEvidenceBoundary

parentEpistemicConsequenceBoundary : Consequence.EpistemicConsequenceBoundary
parentEpistemicConsequenceBoundary =
  Consequence.canonicalEpistemicConsequenceBoundary

------------------------------------------------------------------------
-- Finite cross-product-style witness.
------------------------------------------------------------------------

data DecisionReviewState : Set where
  adequateExtremeIrreversible : DecisionReviewState
  inadequateExtremeIrreversible : DecisionReviewState
  adequateLowReversible : DecisionReviewState


data EvidenceAdequacySurface : Set where
  adequateSurface : EvidenceAdequacySurface
  inadequateSurface : EvidenceAdequacySurface


data ConsequenceProfile : Set where
  extremeIrreversibleProfile : ConsequenceProfile
  lowReversibleProfile : ConsequenceProfile


evidenceAdequacySurface : DecisionReviewState → EvidenceAdequacySurface
evidenceAdequacySurface adequateExtremeIrreversible = adequateSurface
evidenceAdequacySurface inadequateExtremeIrreversible = inadequateSurface
evidenceAdequacySurface adequateLowReversible = adequateSurface

consequenceProfile : DecisionReviewState → ConsequenceProfile
consequenceProfile adequateExtremeIrreversible = extremeIrreversibleProfile
consequenceProfile inadequateExtremeIrreversible = extremeIrreversibleProfile
consequenceProfile adequateLowReversible = lowReversibleProfile

sameExtremeProfileDifferentAdequacy :
  consequenceProfile adequateExtremeIrreversible
  ≡ consequenceProfile inadequateExtremeIrreversible
sameExtremeProfileDifferentAdequacy = refl

adequacyDiffersAtSameExtremeProfile :
  evidenceAdequacySurface adequateExtremeIrreversible
  ≡ evidenceAdequacySurface inadequateExtremeIrreversible → ⊥
adequacyDiffersAtSameExtremeProfile ()

consequenceCannotDetermineEvidenceAdequacy :
  INF.FactorsThrough consequenceProfile evidenceAdequacySurface → ⊥
consequenceCannotDetermineEvidenceAdequacy =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      adequateExtremeIrreversible
      inadequateExtremeIrreversible
      sameExtremeProfileDifferentAdequacy
      adequacyDiffersAtSameExtremeProfile)

sameAdequacyDifferentConsequence :
  evidenceAdequacySurface adequateExtremeIrreversible
  ≡ evidenceAdequacySurface adequateLowReversible
sameAdequacyDifferentConsequence = refl

consequenceDiffersAtSameAdequacy :
  consequenceProfile adequateExtremeIrreversible
  ≡ consequenceProfile adequateLowReversible → ⊥
consequenceDiffersAtSameAdequacy ()

evidenceAdequacyCannotDetermineConsequenceProfile :
  INF.FactorsThrough evidenceAdequacySurface consequenceProfile → ⊥
evidenceAdequacyCannotDetermineConsequenceProfile =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      adequateExtremeIrreversible
      adequateLowReversible
      sameAdequacyDifferentConsequence
      consequenceDiffersAtSameAdequacy)

------------------------------------------------------------------------
-- Direct reuse of the canonical consequence firewalls.
------------------------------------------------------------------------

highConsequenceDoesNotProveInferenceFalse :
  Consequence.highConsequenceAutomaticallyUnderlyingInferenceFalse
    parentEpistemicConsequenceBoundary ≡ false
highConsequenceDoesNotProveInferenceFalse = refl

highUncertaintyDoesNotAutomaticallyProhibitAction :
  Consequence.highUncertaintyAutomaticallyProhibitsAction
    parentEpistemicConsequenceBoundary ≡ false
highUncertaintyDoesNotAutomaticallyProhibitAction = refl

highUncertaintyDoesNotAutomaticallyEstablishIllegality :
  Consequence.highUncertaintyAutomaticallyEstablishesIllegality
    parentEpistemicConsequenceBoundary ≡ false
highUncertaintyDoesNotAutomaticallyEstablishIllegality = refl

legalAvailabilityDoesNotCreateUniversalConsumerAdequacy :
  Consequence.legalAvailabilityAutomaticallyAdequateForEveryConsumer
    parentEpistemicConsequenceBoundary ≡ false
legalAvailabilityDoesNotCreateUniversalConsumerAdequacy = refl

severityAndReversibilityRemainSeparate :
  Consequence.severityAndReversibilityAreSeparateCoordinates
    parentEpistemicConsequenceBoundary ≡ true
severityAndReversibilityRemainSeparate = refl

------------------------------------------------------------------------
-- Cross-pollination boundary.
------------------------------------------------------------------------

record CohnInstitutionalEpistemicConsequenceBoundary : Set where
  constructor cohnInstitutionalEpistemicConsequenceBoundary
  field
    evidenceAdequacyDeterminesConsequenceProfile : Bool
    evidenceAdequacyDeterminesConsequenceProfileIsFalse :
      evidenceAdequacyDeterminesConsequenceProfile ≡ false
    consequenceProfileDeterminesEvidenceAdequacy : Bool
    consequenceProfileDeterminesEvidenceAdequacyIsFalse :
      consequenceProfileDeterminesEvidenceAdequacy ≡ false
    highConsequenceProvesInferenceFalse : Bool
    highConsequenceProvesInferenceFalseIsFalse :
      highConsequenceProvesInferenceFalse ≡ false
    highUncertaintyProvesIllegality : Bool
    highUncertaintyProvesIllegalityIsFalse :
      highUncertaintyProvesIllegality ≡ false
    legalAvailabilityCreatesUniversalAdequacy : Bool
    legalAvailabilityCreatesUniversalAdequacyIsFalse :
      legalAvailabilityCreatesUniversalAdequacy ≡ false
    consequenceAuditMayRemainIndependentCoordinate : Bool
    consequenceAuditMayRemainIndependentCoordinateIsTrue :
      consequenceAuditMayRemainIndependentCoordinate ≡ true

open CohnInstitutionalEpistemicConsequenceBoundary public

canonicalCohnInstitutionalEpistemicConsequenceBoundary :
  CohnInstitutionalEpistemicConsequenceBoundary
canonicalCohnInstitutionalEpistemicConsequenceBoundary =
  cohnInstitutionalEpistemicConsequenceBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
