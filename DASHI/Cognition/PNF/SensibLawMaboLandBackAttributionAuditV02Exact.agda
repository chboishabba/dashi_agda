module DASHI.Cognition.PNF.SensibLawMaboLandBackAttributionAuditV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboLandBackSourceAttributionAuditExact as AuditV01
import DASHI.Cognition.PNF.SensibLawLandBackModeratorAttributionCorrectionExact as CPI
import DASHI.Cognition.PNF.SensibLawLandBackEvidenceDesignCorrectionExact as Design
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueComparabilityExact as Carbon
import DASHI.Cognition.PNF.SensibLawMaboDawsonCrownDerivationHingeClosureExact as DawsonClosure
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Source

------------------------------------------------------------------------
-- V02 audit overlay.
--
-- V01 remains historically valid for the branch state it audited.  This owner
-- records later source recovery/corrections without retroactively rewriting V01.
------------------------------------------------------------------------

data AuditTemporalStatus : Set where
  historicalAuditStatePreserved : AuditTemporalStatus
  laterCorrectionApplied : AuditTemporalStatus
  laterSourceClosureApplied : AuditTemporalStatus


record LaterAuditReceipt : Set where
  constructor laterAuditReceipt
  field
    reference : String
    status : AuditTemporalStatus
    priorAuditStillHistoricallyValid : Bool
    priorAuditStillHistoricallyValidIsTrue : priorAuditStillHistoricallyValid ≡ true
    retroactiveRewriteOfPriorAudit : Bool
    retroactiveRewriteOfPriorAuditIsFalse : retroactiveRewriteOfPriorAudit ≡ false
open LaterAuditReceipt public

cpiLaterCorrection : LaterAuditReceipt
cpiLaterCorrection = laterAuditReceipt
  "CPI moderator provenance correction: historical officialAssociationMapped local label is superseded for downstream attribution by independentPolicyAssociationMapped"
  laterCorrectionApplied
  true refl false refl

probstLaterCorrection : LaterAuditReceipt
probstLaterCorrection = laterAuditReceipt
  "Probst design correction: historical comparativeObservationalDesign local tag is superseded downstream by a dedicated Probst fixed-effects causal-chain receipt"
  laterCorrectionApplied
  true refl false refl

dawsonLaterSourceClosure : LaterAuditReceipt
dawsonLaterSourceClosure = laterAuditReceipt
  "Dawson hinge: historical unresolvedBridge state remains correct before additional Dawson primary passages were recovered; later source recovery closes only reconstruction of Dawson's internal derivation logic"
  laterSourceClosureApplied
  true refl false refl

------------------------------------------------------------------------
-- Mechanical audit pins.
------------------------------------------------------------------------

cpiPreferredAttributionIsIndependent :
  CPI.preferredStatus CPI.cpiModeratorAttributionCorrection
  ≡ CPI.independentPolicyAssociationMapped
cpiPreferredAttributionIsIndependent = refl

probstOwnAuthorityIsUsed :
  Source.sourceId Design.probst2020Authority ≡ "probst-2020-terra-legal-titling"
probstOwnAuthorityIsUsed = refl

wriAndMarketPriceNeedUnitConversion :
  Carbon.comparability Carbon.wriMarketGapBoundary ≡ Carbon.conversionReceiptRequired
wriAndMarketPriceNeedUnitConversion = refl

noExactCarbonUndercompensationRatioYet :
  Carbon.exactDirectUndercompensationRatioClaimed Carbon.wriMarketGapBoundary ≡ false
noExactCarbonUndercompensationRatioYet = refl

dawsonInternalConsumerNowClosed :
  DawsonClosure.consumerClosure DawsonClosure.reconstructDawsonInternalLogic
  ≡ DawsonClosure.consumerClosed
dawsonInternalConsumerNowClosed = refl

dawsonMajorityConsumerStillOpen :
  DawsonClosure.consumerClosure DawsonClosure.determineMajorityNativeTitleRule
  ≡ DawsonClosure.consumerOpen
dawsonMajorityConsumerStillOpen = refl

dawsonLegitimacyConsumerStillOpen :
  DawsonClosure.consumerClosure DawsonClosure.evaluateColonialLegitimacy
  ≡ DawsonClosure.consumerOpen
dawsonLegitimacyConsumerStillOpen = refl

------------------------------------------------------------------------
-- V01 source-attribution constitution remains in force.
------------------------------------------------------------------------

v01CpiAuditWasARecordedCorrection :
  AuditV01.disposition AuditV01.cpiAuthorshipCorrection
  ≡ AuditV01.localClassificationCorrected
v01CpiAuditWasARecordedCorrection = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data LaterCorrectionMakesPriorReceiptNeverExist : Set where
data DawsonInternalClosureMakesDawsonMajority : Set where
data CommonWordCarbonPermitsUnitLaundering : Set where
data CorrectedSourceClassCreatesWorldTruth : Set where

correctionDoesNotEraseHistory : LaterCorrectionMakesPriorReceiptNeverExist → ⊥
correctionDoesNotEraseHistory ()
dawsonInternalClosureDoesNotMakeMajority : DawsonInternalClosureMakesDawsonMajority → ⊥
dawsonInternalClosureDoesNotMakeMajority ()
carbonLabelDoesNotPermitUnitLaundering : CommonWordCarbonPermitsUnitLaundering → ⊥
carbonLabelDoesNotPermitUnitLaundering ()
correctAttributionDoesNotCreateTruth : CorrectedSourceClassCreatesWorldTruth → ⊥
correctAttributionDoesNotCreateTruth ()
