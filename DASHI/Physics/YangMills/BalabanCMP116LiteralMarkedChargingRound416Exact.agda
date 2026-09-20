{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralMarkedChargingRound416Exact where

------------------------------------------------------------------------
-- ROUND416 / SOURCE-NATIVE MARKED CHARGING FOR THE EXACT R410 TERM FAMILY
--
-- R355--R363 already prove all source-independent pieces:
--
--   support/collar alternative
--   + positive decay-rate split
--       -> required charge <= combined raw charge
--       -> exp(-combined) <= exp(-required)
--
-- and R362 transports published CMP116 charged summability onto an exactly
-- attached selected family.
--
-- This owner places those ingredients on ONE exact R410 term family.  The only
-- physical fields are same-object/source attachments; the charging inequality
-- and fixed-Y sum are compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanMarkedWalkChargingCutRound354Exact as R354
import DASHI.Physics.YangMills.BalabanCoefficientCollarWeightRound357Exact as R357
import DASHI.Physics.YangMills.BalabanSourceDecayRateSplitRound359Exact as R359
import DASHI.Physics.YangMills.BalabanChargeExponentToMajorantRound361Exact as R361
import DASHI.Physics.YangMills.BalabanChargedCMP116SummabilityAttachmentRound362Exact as R362
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

record LiteralR410MarkedCharging
    (Term Operator : Set)
    (terms : List Term)
    (selectedTerm : Term → R410.SelectedCMP116PathMarkedTerm Operator)
    (envelope : ℝ)
    : Set₁ where
  field
    order : R361.NegativeExponentialOrderAuthority

    -- Source-native positive split.  This replaces three independent rate
    -- inequalities.
    rateSplit : Term → R359.SourceDecayRateSplit

    -- Exact selected source geometry for each surviving term, already expressed
    -- on the common real metric used by the source charge.
    collarRadius markedDistance treeLength : Term → ℝ
    collarRadiusNonnegative : ∀ term →
      DASHI.Foundations.RealAnalysisAxioms.0ℝ
        DASHI.Foundations.RealAnalysisAxioms.≤ℝ collarRadius term
    markedDistanceNonnegative : ∀ term →
      DASHI.Foundations.RealAnalysisAxioms.0ℝ
        DASHI.Foundations.RealAnalysisAxioms.≤ℝ markedDistance term
    treeLengthNonnegative : ∀ term →
      DASHI.Foundations.RealAnalysisAxioms.0ℝ
        DASHI.Foundations.RealAnalysisAxioms.≤ℝ treeLength term

    -- Literal CMP99/CMP109 geometry, after the support-graph/tree attachments
    -- have been made.
    collarAlternative : ∀ term →
      (collarRadius term
        DASHI.Foundations.RealAnalysisAxioms.≤ℝ markedDistance term)
      Data.Sum.⊎
      (collarRadius term
        DASHI.Foundations.RealAnalysisAxioms.≤ℝ treeLength term)

    -- Source exponentials on this exact selected term.
    chargedMajorant : Term → ℝ

    canonicalR410MajorantIsRawExponential :
      ∀ term →
      R415.canonicalTermMajorant (selectedTerm term)
      ≡ R361.negativeExp order
          (R355CombinedCharge term)

    chargedMajorantIsRequiredExponential :
      ∀ term →
      chargedMajorant term
      ≡ R361.negativeExp order
          (R355RequiredCharge term)

    -- Published CMP116 summability after identifying the charged term family.
    summabilitySource : R362.CMP116ChargedSummabilitySource Term

    selectedTermsAreSourceTerms :
      terms ≡ R362.sourceWalks summabilitySource

    selectedChargedIsSourceCharged :
      chargedMajorant ≡ R362.sourceChargedMajorant summabilitySource

    selectedEnvelopeIsSourceEnvelope :
      envelope ≡ R362.sourceEnvelope summabilitySource

  R355Application : Term → R359.SourceRateApplication
  R355Application term = record
    { R359.SourceRateApplication.split = rateSplit term
    ; R359.SourceRateApplication.collarRadius = collarRadius term
    ; R359.SourceRateApplication.markedDistance = markedDistance term
    ; R359.SourceRateApplication.treeLength = treeLength term
    ; R359.SourceRateApplication.collarRadiusNonnegative =
        collarRadiusNonnegative term
    ; R359.SourceRateApplication.markedDistanceNonnegative =
        markedDistanceNonnegative term
    ; R359.SourceRateApplication.treeLengthNonnegative =
        treeLengthNonnegative term
    }

  R355Calibration : Term → R357.CoefficientCollarWeightCalibration
  R355Calibration term = R359.asR357Calibration (R355Application term)

  R355Geometry : Term →
    DASHI.Physics.YangMills.BalabanCoefficientCollarChargeRound355Exact.CoefficientCollarChargeGeometry
  R355Geometry term =
    R357.asR355ChargeGeometry (R355Calibration term) (collarAlternative term)

  R355CombinedCharge : Term → ℝ
  R355CombinedCharge term =
    DASHI.Physics.YangMills.BalabanCoefficientCollarChargeRound355Exact.combinedMarkedTreeCharge
      (R355Geometry term)

  R355RequiredCharge : Term → ℝ
  R355RequiredCharge term =
    DASHI.Physics.YangMills.BalabanCoefficientCollarChargeRound355Exact.requiredCollarResidualCharge
      (R355Geometry term)

open LiteralR410MarkedCharging public

chargeAttachment :
  ∀ {Term Operator terms selectedTerm envelope}
    (dataSet : LiteralR410MarkedCharging Term Operator terms selectedTerm envelope)
    term →
  R361.ChargeExponentMajorantAttachment (order dataSet)
chargeAttachment dataSet term = record
  { R361.ChargeExponentMajorantAttachment.requiredCharge =
      R355RequiredCharge dataSet term
  ; R361.ChargeExponentMajorantAttachment.combinedCharge =
      R355CombinedCharge dataSet term
  ; R361.ChargeExponentMajorantAttachment.rawMarkedMajorant =
      R415.canonicalTermMajorant (selectedTerm _)
  ; R361.ChargeExponentMajorantAttachment.chargedMajorant =
      chargedMajorant dataSet term
  ; R361.ChargeExponentMajorantAttachment.requiredChargeBelowCombinedCharge =
      DASHI.Physics.YangMills.BalabanCoefficientCollarChargeRound355Exact.coefficientCollarDichotomyPaysLinearCharge
        (R355Geometry dataSet term)
  ; R361.ChargeExponentMajorantAttachment.rawMarkedMajorantIsCombinedExponential =
      canonicalR410MajorantIsRawExponential dataSet term
  ; R361.ChargeExponentMajorantAttachment.chargedMajorantIsRequiredExponential =
      chargedMajorantIsRequiredExponential dataSet term
  }

canonicalR410BelowCharged :
  ∀ {Term Operator terms selectedTerm envelope}
    (dataSet : LiteralR410MarkedCharging Term Operator terms selectedTerm envelope)
    term →
  R415.canonicalTermMajorant (selectedTerm term)
  ≤ℝ chargedMajorant dataSet term
canonicalR410BelowCharged dataSet term =
  R361.rawMarkedBelowCharged
    (order dataSet)
    (chargeAttachment dataSet term)

summabilityAttachment :
  ∀ {Term Operator terms selectedTerm envelope}
    (dataSet : LiteralR410MarkedCharging Term Operator terms selectedTerm envelope) →
  R362.CMP116ChargedSummabilityAttachment (summabilitySource dataSet)
summabilityAttachment dataSet = record
  { R362.CMP116ChargedSummabilityAttachment.selectedWalks =
      _
  ; R362.CMP116ChargedSummabilityAttachment.selectedChargedMajorant =
      chargedMajorant dataSet
  ; R362.CMP116ChargedSummabilityAttachment.selectedEnvelope =
      _
  ; R362.CMP116ChargedSummabilityAttachment.selectedWalksAreSourceWalks =
      selectedTermsAreSourceTerms dataSet
  ; R362.CMP116ChargedSummabilityAttachment.selectedChargedMajorantIsSourceMajorant =
      selectedChargedIsSourceCharged dataSet
  ; R362.CMP116ChargedSummabilityAttachment.selectedEnvelopeIsSourceEnvelope =
      selectedEnvelopeIsSourceEnvelope dataSet
  }

chargedSummability :
  ∀ {Term Operator terms selectedTerm envelope}
    (dataSet : LiteralR410MarkedCharging Term Operator terms selectedTerm envelope) →
  Resum.sumℝ (chargedMajorant dataSet) terms ≤ℝ envelope
chargedSummability dataSet =
  R362.selectedChargedSummability
    (summabilitySource dataSet)
    (summabilityAttachment dataSet)

asR354Charging :
  ∀ {Term Operator terms selectedTerm envelope} →
  LiteralR410MarkedCharging Term Operator terms selectedTerm envelope →
  R354.MarkedWalkChargingData Term
asR354Charging {terms = terms} {selectedTerm = selectedTerm} {envelope = envelope}
    dataSet = record
  { R354.MarkedWalkChargingData.survivingWalks = terms
  ; R354.MarkedWalkChargingData.rawMarkedMajorant =
      λ term → R415.canonicalTermMajorant (selectedTerm term)
  ; R354.MarkedWalkChargingData.chargedMajorant =
      chargedMajorant dataSet
  ; R354.MarkedWalkChargingData.envelope = envelope
  ; R354.MarkedWalkChargingData.rawMarkedBelowCharged =
      canonicalR410BelowCharged dataSet
  ; R354.MarkedWalkChargingData.chargedSummability =
      chargedSummability dataSet
  }

literalR410MarkedChargingCompilerLevel : ProofLevel
literalR410MarkedChargingCompilerLevel = machineChecked

-- Remaining B charge payment is now only same-object/source attachment:
-- support/collar geometry, source rate split, exact R410 exponential majorant,
-- and identification with the published CMP116 charged summability family.
literalR410MarkedChargingAttachmentLevel : ProofLevel
literalR410MarkedChargingAttachmentLevel = conditional
