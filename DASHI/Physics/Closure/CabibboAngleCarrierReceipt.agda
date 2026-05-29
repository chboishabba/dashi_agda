module DASHI.Physics.Closure.CabibboAngleCarrierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMVusCarrierPredictionTargetReceipt as Vus
import DASHI.Physics.Closure.CarrierYukawaRatioTargetReceipt as Ratios
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter

------------------------------------------------------------------------
-- Cabibbo-angle carrier receipt.
--
-- This module records the Cabibbo-angle target surface attached to the
-- existing |V_us| and carrier-Yukawa ratio receipts.  The numerical content
-- below is diagnostic bookkeeping only: it does not derive the physical
-- Cabibbo angle, an accepted alpha value, or a non-identity CKM matrix.

data CabibboAngleCarrierStatus : Set where
  cabibboAngleTargetRecordedComparisonOnly :
    CabibboAngleCarrierStatus

data CabibboAngleCarrierBlocker : Set where
  missingAcceptedCommonAlphaForCabibbo :
    CabibboAngleCarrierBlocker

  missingEvaluatedOffDiagonalCouplingG12 :
    CabibboAngleCarrierBlocker

  missingArcsinErrorBoundForCarrierForm :
    CabibboAngleCarrierBlocker

  missingNonIdentityPhysicalCKMDiagonalizers :
    CabibboAngleCarrierBlocker

  missingPDGAcceptedCabibboAngleAuthority :
    CabibboAngleCarrierBlocker

canonicalCabibboAngleCarrierBlockers :
  List CabibboAngleCarrierBlocker
canonicalCabibboAngleCarrierBlockers =
  missingAcceptedCommonAlphaForCabibbo
  ∷ missingEvaluatedOffDiagonalCouplingG12
  ∷ missingArcsinErrorBoundForCarrierForm
  ∷ missingNonIdentityPhysicalCKMDiagonalizers
  ∷ missingPDGAcceptedCabibboAngleAuthority
  ∷ []

cabibboCarrierAngleFormula : String
cabibboCarrierAngleFormula =
  "theta_C = arcsin(alpha1 * g12)"

cabibboTargetAngleLabel : String
cabibboTargetAngleLabel =
  "theta_C = arcsin(|V_us|) approximately 13 degrees"

alphaOneApproxLabel : String
alphaOneApproxLabel =
  "alpha1 approximately 0.041, recorded as 0.041240 in CarrierYukawaRatioTargetReceipt"

alphaTwoApproxLabel : String
alphaTwoApproxLabel =
  "alpha2 approximately 0.086, recorded as 0.085720 in CarrierYukawaRatioTargetReceipt"

alphaOneSquaredDiagnosticLabel : String
alphaOneSquaredDiagnosticLabel =
  "alpha1^2 approximately 0.00168, within 3 percent of m_u/m_c"

record CabibboAlphaDiagnostics : Setω where
  field
    alpha1PartsPerMillion :
      Nat

    alpha1PartsPerMillionMatchesCanonicalRatioReceipt :
      alpha1PartsPerMillion
      ≡
      Ratios.alphaFromUpOverCharmPartsPerMillion
        Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt

    alpha1ApproxLabel :
      String

    alpha1ApproxLabelIsCanonical :
      alpha1ApproxLabel ≡ alphaOneApproxLabel

    alpha2PartsPerMillion :
      Nat

    alpha2PartsPerMillionMatchesCanonicalRatioReceipt :
      alpha2PartsPerMillion
      ≡
      Ratios.alphaFromCharmOverTopPartsPerMillion
        Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt

    alpha2ApproxLabel :
      String

    alpha2ApproxLabelIsCanonical :
      alpha2ApproxLabel ≡ alphaTwoApproxLabel

    alpha1SquaredPartsPerMillion :
      Nat

    alpha1SquaredPartsPerMillionIsDiagnostic :
      alpha1SquaredPartsPerMillion ≡ 1680

    alpha1SquaredDiagnostic :
      String

    alpha1SquaredDiagnosticIsCanonical :
      alpha1SquaredDiagnostic ≡ alphaOneSquaredDiagnosticLabel

    alpha1SquaredWithinThreePercentOfMuOverCharm :
      Bool

    alpha1SquaredWithinThreePercentOfMuOverCharmIsTrue :
      alpha1SquaredWithinThreePercentOfMuOverCharm ≡ true

    derivedFromFermionMasses :
      Bool

    derivedFromFermionMassesMatchesCanonicalRatioReceipt :
      derivedFromFermionMasses
      ≡
      Ratios.derivedFromFermionMasses
        Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt

    derivedFromFermionMassesIsTrue :
      derivedFromFermionMasses ≡ true

    alphaEstimatesAgree :
      Bool

    alphaEstimatesAgreeMatchesCanonicalRatioReceipt :
      alphaEstimatesAgree
      ≡
      Ratios.alphaEstimatesAgree
        Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt

    alphaEstimatesAgreeIsFalse :
      alphaEstimatesAgree ≡ false

    acceptedCommonAlphaPromoted :
      Bool

    acceptedCommonAlphaPromotedMatchesCanonicalRatioReceipt :
      acceptedCommonAlphaPromoted
      ≡
      Ratios.acceptedAlphaTargetPromoted
        Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt

    acceptedCommonAlphaPromotedIsFalse :
      acceptedCommonAlphaPromoted ≡ false

    diagnosticsBoundary :
      List String

open CabibboAlphaDiagnostics public

canonicalCabibboAlphaDiagnostics :
  CabibboAlphaDiagnostics
canonicalCabibboAlphaDiagnostics =
  record
    { alpha1PartsPerMillion =
        Ratios.alphaFromUpOverCharmPartsPerMillion
          Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; alpha1PartsPerMillionMatchesCanonicalRatioReceipt =
        refl
    ; alpha1ApproxLabel =
        alphaOneApproxLabel
    ; alpha1ApproxLabelIsCanonical =
        refl
    ; alpha2PartsPerMillion =
        Ratios.alphaFromCharmOverTopPartsPerMillion
          Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; alpha2PartsPerMillionMatchesCanonicalRatioReceipt =
        refl
    ; alpha2ApproxLabel =
        alphaTwoApproxLabel
    ; alpha2ApproxLabelIsCanonical =
        refl
    ; alpha1SquaredPartsPerMillion =
        1680
    ; alpha1SquaredPartsPerMillionIsDiagnostic =
        refl
    ; alpha1SquaredDiagnostic =
        alphaOneSquaredDiagnosticLabel
    ; alpha1SquaredDiagnosticIsCanonical =
        refl
    ; alpha1SquaredWithinThreePercentOfMuOverCharm =
        true
    ; alpha1SquaredWithinThreePercentOfMuOverCharmIsTrue =
        refl
    ; derivedFromFermionMasses =
        Ratios.derivedFromFermionMasses
          Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; derivedFromFermionMassesMatchesCanonicalRatioReceipt =
        refl
    ; derivedFromFermionMassesIsTrue =
        Ratios.derivedFromFermionMassesIsTrue
          Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; alphaEstimatesAgree =
        Ratios.alphaEstimatesAgree
          Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; alphaEstimatesAgreeMatchesCanonicalRatioReceipt =
        refl
    ; alphaEstimatesAgreeIsFalse =
        Ratios.alphaEstimatesAgreeIsFalse
          Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; acceptedCommonAlphaPromoted =
        Ratios.acceptedAlphaTargetPromoted
          Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; acceptedCommonAlphaPromotedMatchesCanonicalRatioReceipt =
        refl
    ; acceptedCommonAlphaPromotedIsFalse =
        Ratios.acceptedAlphaTargetPromotedIsFalse
          Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; diagnosticsBoundary =
        "alpha1 is recorded from the existing m_u/m_c alpha readback as approximately 0.041"
        ∷ "alpha2 is recorded from the existing m_c/m_t alpha readback as approximately 0.086"
        ∷ "alpha1^2 is recorded as approximately 0.00168 and within 3 percent of the m_u/m_c diagnostic target"
        ∷ "The existing readback marks derivedFromFermionMasses=true, but accepted-common-alpha promotion remains false"
        ∷ "The two alpha estimates do not agree as an accepted common-alpha receipt"
        ∷ []
    }

record CabibboAngleCarrierReceipt : Setω where
  field
    status :
      CabibboAngleCarrierStatus

    ckmVusTargetReceiptIsCanonical :
      Bool

    ckmVusTargetReceiptIsCanonicalIsTrue :
      ckmVusTargetReceiptIsCanonical ≡ true

    carrierYukawaRatioTargetReceiptIsCanonical :
      Bool

    carrierYukawaRatioTargetReceiptIsCanonicalIsTrue :
      carrierYukawaRatioTargetReceiptIsCanonical ≡ true

    alphaDiagnosticsBound :
      Bool

    alphaDiagnosticsBoundIsTrue :
      alphaDiagnosticsBound ≡ true

    pdgApproxVus :
      Matter.MixingGaussianRationalDatum

    pdgApproxVusMatchesCanonicalVusReceipt :
      pdgApproxVus
      ≡
      Vus.pdgApproxVus
        Vus.canonicalCKMVusCarrierPredictionTargetReceipt

    cabibboTargetThetaLabel :
      String

    cabibboTargetThetaLabelIsCanonical :
      cabibboTargetThetaLabel ≡ cabibboTargetAngleLabel

    carrierThetaFormula :
      String

    carrierThetaFormulaIsCabibboForm :
      carrierThetaFormula ≡ cabibboCarrierAngleFormula

    carrierThetaFormulaRefinesVusAlphaCouplingTarget :
      Bool

    carrierThetaFormulaRefinesVusAlphaCouplingTargetIsTrue :
      carrierThetaFormulaRefinesVusAlphaCouplingTarget ≡ true

    cabibboAngleDerived :
      Bool

    cabibboAngleDerivedIsFalse :
      cabibboAngleDerived ≡ false

    yukawaSuppressPatternConsistent :
      Bool

    yukawaSuppressPatternConsistentIsTrue :
      yukawaSuppressPatternConsistent ≡ true

    physicalCKMPromotionConstructed :
      Bool

    physicalCKMPromotionConstructedMatchesCanonicalVusReceipt :
      physicalCKMPromotionConstructed
      ≡
      Vus.physicalCKMPromotionConstructed
        Vus.canonicalCKMVusCarrierPredictionTargetReceipt

    physicalCKMPromotionConstructedIsFalse :
      physicalCKMPromotionConstructed ≡ false

    physicalYukawaRatioPredictionsPromoted :
      Bool

    physicalYukawaRatioPredictionsPromotedMatchesCanonicalRatioReceipt :
      physicalYukawaRatioPredictionsPromoted
      ≡
      Ratios.physicalRatioPredictionsPromoted
        Ratios.canonicalCarrierYukawaRatioTargetReceipt

    physicalYukawaRatioPredictionsPromotedIsFalse :
      physicalYukawaRatioPredictionsPromoted ≡ false

    blockers :
      List CabibboAngleCarrierBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCabibboAngleCarrierBlockers

    receiptBoundary :
      List String

open CabibboAngleCarrierReceipt public

canonicalCabibboAngleCarrierReceipt :
  CabibboAngleCarrierReceipt
canonicalCabibboAngleCarrierReceipt =
  record
    { status =
        cabibboAngleTargetRecordedComparisonOnly
    ; ckmVusTargetReceiptIsCanonical =
        true
    ; ckmVusTargetReceiptIsCanonicalIsTrue =
        refl
    ; carrierYukawaRatioTargetReceiptIsCanonical =
        true
    ; carrierYukawaRatioTargetReceiptIsCanonicalIsTrue =
        refl
    ; alphaDiagnosticsBound =
        true
    ; alphaDiagnosticsBoundIsTrue =
        refl
    ; pdgApproxVus =
        Vus.pdgApproxVus
          Vus.canonicalCKMVusCarrierPredictionTargetReceipt
    ; pdgApproxVusMatchesCanonicalVusReceipt =
        refl
    ; cabibboTargetThetaLabel =
        cabibboTargetAngleLabel
    ; cabibboTargetThetaLabelIsCanonical =
        refl
    ; carrierThetaFormula =
        cabibboCarrierAngleFormula
    ; carrierThetaFormulaIsCabibboForm =
        refl
    ; carrierThetaFormulaRefinesVusAlphaCouplingTarget =
        true
    ; carrierThetaFormulaRefinesVusAlphaCouplingTargetIsTrue =
        refl
    ; cabibboAngleDerived =
        false
    ; cabibboAngleDerivedIsFalse =
        refl
    ; yukawaSuppressPatternConsistent =
        true
    ; yukawaSuppressPatternConsistentIsTrue =
        refl
    ; physicalCKMPromotionConstructed =
        Vus.physicalCKMPromotionConstructed
          Vus.canonicalCKMVusCarrierPredictionTargetReceipt
    ; physicalCKMPromotionConstructedMatchesCanonicalVusReceipt =
        refl
    ; physicalCKMPromotionConstructedIsFalse =
        Vus.physicalCKMPromotionConstructedIsFalse
          Vus.canonicalCKMVusCarrierPredictionTargetReceipt
    ; physicalYukawaRatioPredictionsPromoted =
        Ratios.physicalRatioPredictionsPromoted
          Ratios.canonicalCarrierYukawaRatioTargetReceipt
    ; physicalYukawaRatioPredictionsPromotedMatchesCanonicalRatioReceipt =
        refl
    ; physicalYukawaRatioPredictionsPromotedIsFalse =
        Ratios.physicalRatioPredictionsPromotedIsFalse
          Ratios.canonicalCarrierYukawaRatioTargetReceipt
    ; blockers =
        canonicalCabibboAngleCarrierBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "The Cabibbo target is theta_C = arcsin(|V_us|) approximately 13 degrees from the existing Vus comparison target"
        ∷ "The carrier form is theta_C = arcsin(alpha1 * g12), refining the existing |V_us|_target(alpha,g_12)=alpha*g_12 target surface"
        ∷ "alpha1 approximately 0.041, alpha2 approximately 0.086, and alpha1^2 approximately 0.00168 within 3 percent of m_u/m_c are diagnostic readbacks, not accepted physical constants"
        ∷ "alpha1^2 is recorded as within 3 percent of m_u/m_c while the common-alpha and error-bound receipts remain absent"
        ∷ "yukawaSuppressPatternConsistent is true as a pattern-level diagnostic against the existing carrier-Yukawa ratio receipt"
        ∷ "cabibboAngleDerived is false: no evaluated g12, arcsin error bound, accepted PDG authority binding, or non-identity physical CKM diagonalizer is constructed here"
        ∷ []
    }

cabibboAngleCarrierReceiptKeepsDerivationClosed :
  cabibboAngleDerived canonicalCabibboAngleCarrierReceipt
  ≡
  false
cabibboAngleCarrierReceiptKeepsDerivationClosed =
  refl

cabibboAngleCarrierReceiptRecordsYukawaPatternConsistency :
  yukawaSuppressPatternConsistent canonicalCabibboAngleCarrierReceipt
  ≡
  true
cabibboAngleCarrierReceiptRecordsYukawaPatternConsistency =
  refl

cabibboAngleCarrierReceiptThreadsVusPromotionBlocker :
  physicalCKMPromotionConstructed canonicalCabibboAngleCarrierReceipt
  ≡
  false
cabibboAngleCarrierReceiptThreadsVusPromotionBlocker =
  Vus.physicalCKMPromotionConstructedIsFalse
    Vus.canonicalCKMVusCarrierPredictionTargetReceipt

cabibboAngleCarrierReceiptThreadsYukawaRatioBlocker :
  physicalYukawaRatioPredictionsPromoted canonicalCabibboAngleCarrierReceipt
  ≡
  false
cabibboAngleCarrierReceiptThreadsYukawaRatioBlocker =
  Ratios.physicalRatioPredictionsPromotedIsFalse
    Ratios.canonicalCarrierYukawaRatioTargetReceipt
