module DASHI.Law.SensibLawLegalReasonablenessNormativityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.InstitutionalNormSituatedReasonablenessBridgeExact as NormBridge
import DASHI.Law.SensibLawLegalReasonablenessExact as LegalReason

------------------------------------------------------------------------
-- LEGAL REASONABLENESS × NORM PRODUCTION
--
-- The legal inquiry may require a court to apply a present statutory/doctrinal
-- standard while political/historical critique asks how the standard, factor
-- set or baseline was produced.  Those are distinct consumers.  Neither legal
-- application nor judicial restraint automatically proves political neutrality
-- or moral endorsement; political critique likewise does not automatically
-- establish legal invalidity.
------------------------------------------------------------------------

parentLegalReasonablenessBoundary : LegalReason.LegalReasonablenessBoundary
parentLegalReasonablenessBoundary = LegalReason.canonicalLegalReasonablenessBoundary

parentNormProductionReasonablenessBoundary :
  NormBridge.InstitutionalNormReasonablenessBoundary
parentNormProductionReasonablenessBoundary =
  NormBridge.canonicalInstitutionalNormReasonablenessBoundary

record LegalReasonablenessNormativityBoundary : Set where
  constructor legalReasonablenessNormativityBoundary
  field
    legalReasonablenessParentReused : Bool
    normProductionReasonablenessBridgeReused : Bool
    lawfulRangeAutomaticallyPoliticalNeutrality : Bool
    legallyRelevantFactorSetAutomaticallyValueFree : Bool
    judicialRestraintAutomaticallyNormativeEndorsement : Bool
    courtApplyingStatuteAutomaticallyApprovesStatutoryPolicy : Bool
    politicalCritiqueAutomaticallyLegalInvalidity : Bool
    historicalProductionCritiqueAutomaticallyMeritsReview : Bool
    doctrinalReasonablenessAutomaticallyOrdinaryLanguageReasonableness : Bool
    legalApplicationAndNormativeCritiqueCanRemainDistinct : Bool

open LegalReasonablenessNormativityBoundary public

canonicalLegalReasonablenessNormativityBoundary :
  LegalReasonablenessNormativityBoundary
canonicalLegalReasonablenessNormativityBoundary =
  legalReasonablenessNormativityBoundary
    true
    true
    false
    false
    false
    false
    false
    false
    false
    true
