module DASHI.Education.EarlyLearningCrossCuttingEndorsementRiskExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.EarlyLearningReappropriationBoundaryExact as Existing

------------------------------------------------------------------------
-- CROSS-CUTTING EXPERT ENDORSEMENT RISK
--
-- Source-cue research motivates a stronger boundary than "conditions travel
-- with quotation": a credible or ideologically unexpected endorsement may be
-- especially persuasive.  This is a risk model, not proof of persuasion in any
-- particular Australian audience.
--
-- James N. Druckman, "On the Limits of Framing Effects: Who Can Frame?",
-- The Journal of Politics 63(4), 1041-1066 (2001).
-- DOI: 10.1111/0022-3816.00100.
--
-- Stephen P. Nicholson, "Dominating Cues and the Limits of Elite Influence",
-- The Journal of Politics 73(4), 1165-1177 (2011).
-- DOI: 10.1017/S002238161100082X.
------------------------------------------------------------------------

data SourceCredibility : Set where
  lowCredibility domainRelevantCredibility : SourceCredibility

data IdeologicalRelation : Set where
  expectedAlignment crossCuttingUnexpected : IdeologicalRelation

data QuoteSurface : Set where
  fullConditionalStatement atomOnlyExcerpt headlineEndorsement : QuoteSurface

record EndorsementRiskSurface : Set where
  constructor endorsementRiskSurface
  field
    sourceCredibility : SourceCredibility
    ideologicalRelation : IdeologicalRelation
    quoteSurface : QuoteSurface
    conditionsPublished : Bool
    surroundingProgrammeExplicitlyDisclaimed : Bool
    riskLabel : String

open EndorsementRiskSurface public

crossCuttingExpertRisk : EndorsementRiskSurface
crossCuttingExpertRisk =
  endorsementRiskSurface
    domainRelevantCredibility crossCuttingUnexpected atomOnlyExcerpt
    true true
    "cross-cutting expert support may remain rhetorically valuable even where the expert publishes limiting conditions"

------------------------------------------------------------------------
-- Conditions are necessary but not sufficient to prove zero reappropriation
-- risk.  We therefore block automatic promotion from a well-conditioned
-- endorsement receipt to a claim that downstream framing is harmless.
------------------------------------------------------------------------

data ConditionsTravelImpliesNoCueRiskPermission : Set where

conditionsTravelCannotProveZeroCueRisk :
  ConditionsTravelImpliesNoCueRiskPermission → ⊥
conditionsTravelCannotProveZeroCueRisk ()

canonicalConditionalReceipt : Existing.ExpertEndorsementReceipt
canonicalConditionalReceipt = Existing.canonicalConditionalExpertEndorsement

conditionalReceiptStillNeedsCueRiskAssessment : Bool
conditionalReceiptStillNeedsCueRiskAssessment = true

conditionalReceiptStillNeedsCueRiskAssessmentIsTrue :
  conditionalReceiptStillNeedsCueRiskAssessment ≡ true
conditionalReceiptStillNeedsCueRiskAssessmentIsTrue = refl

endorsementRiskReading : String
endorsementRiskReading =
  "A domain-credible, cross-cutting expert endorsement can be disproportionately informative precisely because it is unexpected. Therefore attaching conditions to an endorsement is necessary provenance discipline but cannot prove that an atom-only quotation or headline will not transfer credibility to a surrounding frame."
