module DASHI.Promotion.PlanckHbarSIPayloadRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.NumericAuthorityPayloadValidator as Payload

------------------------------------------------------------------------
-- Exact SI Planck / hbar payload request.
--
-- This module is request-shaped only.  It records the exact SI Planck
-- defining-constant text, the derived hbar expression needed by
-- Stone/Schrodinger consumers, and the dimension-vector shape for J s.
-- It does not load an external authority artifact, parse a decimal carrier,
-- decimalize hbar, or promote a numeric value.
-- It also does not construct Candidate256PhysicalCalibrationExternalReceipt;
-- the W4 physical-calibration receipt remains external to this request.

data PlanckHbarPayloadFieldKey : Set where
  authorityArtifactKey : PlanckHbarPayloadFieldKey
  authorityArtifactSha256Key : PlanckHbarPayloadFieldKey
  authorityAccessDateEvidenceKey : PlanckHbarPayloadFieldKey
  planckRawNumericValueTextKey : PlanckHbarPayloadFieldKey
  planckRawUncertaintyTextKey : PlanckHbarPayloadFieldKey
  planckUnitTextKey : PlanckHbarPayloadFieldKey
  planckDimensionVectorTextKey : PlanckHbarPayloadFieldKey
  planckDimensionVectorCarrierKey : PlanckHbarPayloadFieldKey
  planckDimensionVectorWitnessKey : PlanckHbarPayloadFieldKey
  hbarDerivedExpressionTextKey : PlanckHbarPayloadFieldKey
  hbarDerivationLabelKey : PlanckHbarPayloadFieldKey
  hbarRoundingPolicyKey : PlanckHbarPayloadFieldKey
  parsedNumericCarrierPayloadKey : PlanckHbarPayloadFieldKey
  covarianceMatrixOrIndependenceReceiptKey : PlanckHbarPayloadFieldKey
  consumerValueIngestionReceiptKey : PlanckHbarPayloadFieldKey

record PlanckHbarPayloadFields : Set₁ where
  field
    authorityArtifact :
      Payload.PayloadSchemaField
    authorityArtifactSha256 :
      Payload.PayloadSchemaField
    authorityAccessDateEvidence :
      Payload.PayloadSchemaField
    planckRawNumericValueText :
      String
    planckRawUncertaintyText :
      String
    planckUnitText :
      String
    planckDimensionVectorText :
      String
    planckDimensionVectorCarrier :
      Payload.PayloadSchemaField
    planckDimensionVectorWitness :
      Payload.PayloadSchemaField
    hbarDerivedExpressionText :
      String
    hbarDerivationLabel :
      String
    hbarRoundingPolicy :
      String
    parsedNumericCarrierPayload :
      Payload.PayloadSchemaField
    covarianceMatrixOrIndependenceReceipt :
      Payload.PayloadSchemaField
    consumerValueIngestionReceipt :
      Payload.PayloadSchemaField

open PlanckHbarPayloadFields public

canonicalPlanckHbarPayloadFields : PlanckHbarPayloadFields
canonicalPlanckHbarPayloadFields = record
  { authorityArtifact =
      Payload.missingAuthorityArtifactField
  ; authorityArtifactSha256 =
      Payload.missingArtifactDigestField
  ; authorityAccessDateEvidence =
      Payload.missingAccessEvidenceField
  ; planckRawNumericValueText =
      "6.62607015e-34"
  ; planckRawUncertaintyText =
      "0"
  ; planckUnitText =
      "J s"
  ; planckDimensionVectorText =
      "kg m^2 s^-1"
  ; planckDimensionVectorCarrier =
      Payload.missingDimensionVectorCarrierField
  ; planckDimensionVectorWitness =
      Payload.missingDimensionVectorWitnessField
  ; hbarDerivedExpressionText =
      "h / (2 pi)"
  ; hbarDerivationLabel =
      "reduced Planck constant derived from exact SI h and mathematical pi"
  ; hbarRoundingPolicy =
      "no decimalized hbar supplied; consumers must preserve h / (2 pi) or provide a rounding receipt"
  ; parsedNumericCarrierPayload =
      Payload.missingParsedCarrierField
  ; covarianceMatrixOrIndependenceReceipt =
      Payload.missingCovarianceField
  ; consumerValueIngestionReceipt =
      Payload.missingConsumerIngestionReceiptField
  }

canonicalPlanckHbarFieldKeys : List PlanckHbarPayloadFieldKey
canonicalPlanckHbarFieldKeys =
  authorityArtifactKey
  ∷ authorityArtifactSha256Key
  ∷ authorityAccessDateEvidenceKey
  ∷ planckRawNumericValueTextKey
  ∷ planckRawUncertaintyTextKey
  ∷ planckUnitTextKey
  ∷ planckDimensionVectorTextKey
  ∷ planckDimensionVectorCarrierKey
  ∷ planckDimensionVectorWitnessKey
  ∷ hbarDerivedExpressionTextKey
  ∷ hbarDerivationLabelKey
  ∷ hbarRoundingPolicyKey
  ∷ parsedNumericCarrierPayloadKey
  ∷ covarianceMatrixOrIndependenceReceiptKey
  ∷ consumerValueIngestionReceiptKey
  ∷ []

canonicalPlanckAuthorityFamily : String
canonicalPlanckAuthorityFamily =
  "BIPM SI defining constants"

canonicalPlanckSourceUri : String
canonicalPlanckSourceUri =
  "https://www.bipm.org/en/measurement-units/si-defining-constants"

canonicalPlanckRegistrySourceRef : String
canonicalPlanckRegistrySourceRef =
  "DASHI.Constants.Registry.canonicalSIDefiningConstants.h"

hbarAuthorityPayloadSupplied : Bool
hbarAuthorityPayloadSupplied =
  false

hbarAuthorityPayloadSuppliedIsFalse :
  hbarAuthorityPayloadSupplied ≡ false
hbarAuthorityPayloadSuppliedIsFalse =
  refl

canonicalPlanckRegistryRow : Registry.KnownConstantSlot
canonicalPlanckRegistryRow =
  Registry.mkConstant
    "Planck constant"
    "h"
    "6.62607015e-34"
    "J s"
    Registry.exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "Schrodinger"
    ∷ "QFT"
    ∷ "quantum measurement"
    ∷ "chemistry spectra"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "hbar and quantum dynamics still require representation adapters"
    ∷ []
    )

canonicalHbarRegistryRow : Registry.KnownConstantSlot
canonicalHbarRegistryRow =
  Registry.mkConstant
    "reduced Planck constant"
    "hbar"
    "h / (2 pi)"
    "J s"
    Registry.exactSIDerivedConstant
    "derived from exact SI Planck constant and mathematical pi"
    ( "Schrodinger"
    ∷ "QFT"
    ∷ "spectroscopy"
    ∷ []
    )
    ( "exact as an expression in h and pi"
    ∷ "numeric decimal use still requires chosen rounding policy"
    ∷ []
    )

data SIDimensionAxis : Set where
  metreAxis : SIDimensionAxis
  kilogramAxis : SIDimensionAxis
  secondAxis : SIDimensionAxis
  ampereAxis : SIDimensionAxis
  kelvinAxis : SIDimensionAxis
  moleAxis : SIDimensionAxis
  candelaAxis : SIDimensionAxis

record SIDimensionExponentText : Set where
  field
    axis :
      SIDimensionAxis
    exponentText :
      String

open SIDimensionExponentText public

mkDimensionExponentText :
  SIDimensionAxis →
  String →
  SIDimensionExponentText
mkDimensionExponentText axis exponent =
  record
    { axis = axis
    ; exponentText = exponent
    }

canonicalPlanckDimensionShape : List SIDimensionExponentText
canonicalPlanckDimensionShape =
  mkDimensionExponentText metreAxis "2"
  ∷ mkDimensionExponentText kilogramAxis "1"
  ∷ mkDimensionExponentText secondAxis "-1"
  ∷ mkDimensionExponentText ampereAxis "0"
  ∷ mkDimensionExponentText kelvinAxis "0"
  ∷ mkDimensionExponentText moleAxis "0"
  ∷ mkDimensionExponentText candelaAxis "0"
  ∷ []

canonicalHbarDerivationLabels : List String
canonicalHbarDerivationLabels =
  "hbar is not separately loaded from an external artifact in this module"
  ∷ "hbar is the exact expression h / (2 pi)"
  ∷ "h is the exact SI Planck defining constant 6.62607015e-34 J s"
  ∷ "pi is the mathematical circle constant, not an empirical authority token"
  ∷ "hbar has the same SI dimension shape as h: kg m^2 s^-1"
  ∷ "decimalized hbar requires an explicit rounding receipt before consumption"
  ∷ []

record PlanckHbarSIPayloadRequest : Set₁ where
  field
    requestLabel :
      String
    sourceRegistry :
      Registry.ConstantsRegistry
    planckRegistryRow :
      Registry.KnownConstantSlot
    hbarRegistryRow :
      Registry.KnownConstantSlot
    sourcePayloadValidator :
      Payload.NumericAuthorityPayloadValidatorReceipt
    payloadFields :
      PlanckHbarPayloadFields
    payloadFieldKeys :
      List PlanckHbarPayloadFieldKey
    payloadFieldKeyCount :
      Nat
    payloadFieldKeyCountIs15 :
      payloadFieldKeyCount ≡ 15
    planckSymbol :
      String
    hbarSymbol :
      String
    authorityFamily :
      String
    planckUnitConvention :
      String
    hbarUnitConvention :
      String
    sourceUri :
      String
    planckExactZeroUncertaintyText :
      String
    planckDimensionVectorText :
      String
    dimensionShape :
      List SIDimensionExponentText
    dimensionShapeIsCanonical :
      dimensionShape ≡ canonicalPlanckDimensionShape
    hbarDerivedExpressionText :
      String
    hbarDerivationLabels :
      List String
    hbarDerivationLabelsAreCanonical :
      hbarDerivationLabels ≡ canonicalHbarDerivationLabels
    stoneSchrodingerBridgeCrossReference :
      String
    authorityArtifactPresent :
      Bool
    authorityArtifactPresentIsFalse :
      authorityArtifactPresent ≡ false
    authorityArtifactSha256Present :
      Bool
    authorityArtifactSha256PresentIsFalse :
      authorityArtifactSha256Present ≡ false
    authorityAccessDateEvidencePresent :
      Bool
    authorityAccessDateEvidencePresentIsFalse :
      authorityAccessDateEvidencePresent ≡ false
    dimensionVectorCarrierPresent :
      Bool
    dimensionVectorCarrierPresentIsFalse :
      dimensionVectorCarrierPresent ≡ false
    dimensionVectorWitnessPresent :
      Bool
    dimensionVectorWitnessPresentIsFalse :
      dimensionVectorWitnessPresent ≡ false
    parsedNumericCarrierPayloadPresent :
      Bool
    parsedNumericCarrierPayloadPresentIsFalse :
      parsedNumericCarrierPayloadPresent ≡ false
    covarianceMatrixOrIndependenceReceiptPresent :
      Bool
    covarianceMatrixOrIndependenceReceiptPresentIsFalse :
      covarianceMatrixOrIndependenceReceiptPresent ≡ false
    consumerIngestionReceiptPresent :
      Bool
    consumerIngestionReceiptPresentIsFalse :
      consumerIngestionReceiptPresent ≡ false
    acceptedAuthorityTokenPresent :
      Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    planckNumericValuePromoted :
      Bool
    planckNumericValuePromotedIsFalse :
      planckNumericValuePromoted ≡ false
    hbarNumericValuePromoted :
      Bool
    hbarNumericValuePromotedIsFalse :
      hbarNumericValuePromoted ≡ false
    externalArtifactLoaded :
      Bool
    externalArtifactLoadedIsFalse :
      externalArtifactLoaded ≡ false
    externalArtifactAccepted :
      Bool
    externalArtifactAcceptedIsFalse :
      externalArtifactAccepted ≡ false
    stoneSchrodingerConsumptionEnabled :
      Bool
    stoneSchrodingerConsumptionEnabledIsFalse :
      stoneSchrodingerConsumptionEnabled ≡ false
    inheritsValidatorFailClosedTokenGuard :
      acceptedAuthorityTokenPresent
      ≡
      Payload.NumericAuthorityPayloadValidatorReceipt.acceptedAuthorityTokenPresent
        sourcePayloadValidator
    inheritsValidatorFailClosedPromotionGuard :
      planckNumericValuePromoted
      ≡
      Payload.NumericAuthorityPayloadValidatorReceipt.numericValuePromoted
        sourcePayloadValidator

open PlanckHbarSIPayloadRequest public

canonicalPlanckHbarSIPayloadRequest :
  PlanckHbarSIPayloadRequest
canonicalPlanckHbarSIPayloadRequest = record
  { requestLabel =
      "Planck h and hbar exact SI payload request"
  ; sourceRegistry =
      Registry.repoWideConstantsRegistry
  ; planckRegistryRow =
      canonicalPlanckRegistryRow
  ; hbarRegistryRow =
      canonicalHbarRegistryRow
  ; sourcePayloadValidator =
      Payload.canonicalNumericAuthorityPayloadValidatorReceipt
  ; payloadFields =
      canonicalPlanckHbarPayloadFields
  ; payloadFieldKeys =
      canonicalPlanckHbarFieldKeys
  ; payloadFieldKeyCount =
      Payload.listCount canonicalPlanckHbarFieldKeys
  ; payloadFieldKeyCountIs15 =
      refl
  ; planckSymbol =
      "h"
  ; hbarSymbol =
      "hbar"
  ; authorityFamily =
      canonicalPlanckAuthorityFamily
  ; planckUnitConvention =
      "J s"
  ; hbarUnitConvention =
      "J s"
  ; sourceUri =
      canonicalPlanckSourceUri
  ; planckExactZeroUncertaintyText =
      PlanckHbarPayloadFields.planckRawUncertaintyText
        canonicalPlanckHbarPayloadFields
  ; planckDimensionVectorText =
      PlanckHbarPayloadFields.planckDimensionVectorText
        canonicalPlanckHbarPayloadFields
  ; dimensionShape =
      canonicalPlanckDimensionShape
  ; dimensionShapeIsCanonical =
      refl
  ; hbarDerivedExpressionText =
      PlanckHbarPayloadFields.hbarDerivedExpressionText
        canonicalPlanckHbarPayloadFields
  ; hbarDerivationLabels =
      canonicalHbarDerivationLabels
  ; hbarDerivationLabelsAreCanonical =
      refl
  ; stoneSchrodingerBridgeCrossReference =
      "DASHI.Physics.Closure.StoneSISecondTimeParameterBridge"
  ; authorityArtifactPresent =
      false
  ; authorityArtifactPresentIsFalse =
      refl
  ; authorityArtifactSha256Present =
      false
  ; authorityArtifactSha256PresentIsFalse =
      refl
  ; authorityAccessDateEvidencePresent =
      false
  ; authorityAccessDateEvidencePresentIsFalse =
      refl
  ; dimensionVectorCarrierPresent =
      false
  ; dimensionVectorCarrierPresentIsFalse =
      refl
  ; dimensionVectorWitnessPresent =
      false
  ; parsedNumericCarrierPayloadPresent =
      false
  ; parsedNumericCarrierPayloadPresentIsFalse =
      refl
  ; dimensionVectorWitnessPresentIsFalse =
      refl
  ; covarianceMatrixOrIndependenceReceiptPresent =
      false
  ; covarianceMatrixOrIndependenceReceiptPresentIsFalse =
      refl
  ; consumerIngestionReceiptPresent =
      false
  ; consumerIngestionReceiptPresentIsFalse =
      refl
  ; acceptedAuthorityTokenPresent =
      false
  ; acceptedAuthorityTokenPresentIsFalse =
      refl
  ; planckNumericValuePromoted =
      false
  ; planckNumericValuePromotedIsFalse =
      refl
  ; hbarNumericValuePromoted =
      false
  ; hbarNumericValuePromotedIsFalse =
      refl
  ; externalArtifactLoaded =
      false
  ; externalArtifactLoadedIsFalse =
      refl
  ; externalArtifactAccepted =
      false
  ; externalArtifactAcceptedIsFalse =
      refl
  ; stoneSchrodingerConsumptionEnabled =
      false
  ; stoneSchrodingerConsumptionEnabledIsFalse =
      refl
  ; inheritsValidatorFailClosedTokenGuard =
      refl
  ; inheritsValidatorFailClosedPromotionGuard =
      refl
  }

canonicalPlanckRawNumericValueTextIsExactSIValue :
  PlanckHbarPayloadFields.planckRawNumericValueText
    canonicalPlanckHbarPayloadFields
  ≡ "6.62607015e-34"
canonicalPlanckRawNumericValueTextIsExactSIValue = refl

canonicalPlanckRawUncertaintyTextIsExactZero :
  PlanckHbarPayloadFields.planckRawUncertaintyText
    canonicalPlanckHbarPayloadFields
  ≡ "0"
canonicalPlanckRawUncertaintyTextIsExactZero = refl

canonicalPlanckUnitTextIsJouleSecond :
  PlanckHbarPayloadFields.planckUnitText canonicalPlanckHbarPayloadFields
  ≡ "J s"
canonicalPlanckUnitTextIsJouleSecond = refl

canonicalPlanckDimensionVectorTextIsJouleSecondShape :
  PlanckHbarPayloadFields.planckDimensionVectorText
    canonicalPlanckHbarPayloadFields
  ≡ "kg m^2 s^-1"
canonicalPlanckDimensionVectorTextIsJouleSecondShape = refl

canonicalHbarDerivedExpressionTextIsHOverTwoPi :
  PlanckHbarPayloadFields.hbarDerivedExpressionText
    canonicalPlanckHbarPayloadFields
  ≡ "h / (2 pi)"
canonicalHbarDerivedExpressionTextIsHOverTwoPi = refl

canonicalPlanckRegistryRowSymbolMatchesRequest :
  Registry.KnownConstantSlot.symbol
    (PlanckHbarSIPayloadRequest.planckRegistryRow
      canonicalPlanckHbarSIPayloadRequest)
  ≡
  PlanckHbarSIPayloadRequest.planckSymbol
    canonicalPlanckHbarSIPayloadRequest
canonicalPlanckRegistryRowSymbolMatchesRequest = refl

canonicalHbarRegistryRowSymbolMatchesRequest :
  Registry.KnownConstantSlot.symbol
    (PlanckHbarSIPayloadRequest.hbarRegistryRow
      canonicalPlanckHbarSIPayloadRequest)
  ≡
  PlanckHbarSIPayloadRequest.hbarSymbol
    canonicalPlanckHbarSIPayloadRequest
canonicalHbarRegistryRowSymbolMatchesRequest = refl

canonicalPlanckRegistryRowValueIsExactSIValue :
  Registry.KnownConstantSlot.value canonicalPlanckRegistryRow
  ≡ "6.62607015e-34"
canonicalPlanckRegistryRowValueIsExactSIValue = refl

canonicalHbarRegistryRowValueIsExactExpression :
  Registry.KnownConstantSlot.value canonicalHbarRegistryRow
  ≡ "h / (2 pi)"
canonicalHbarRegistryRowValueIsExactExpression = refl

canonicalPlanckRegistryRowUnitMatchesRequest :
  Registry.KnownConstantSlot.unit canonicalPlanckRegistryRow
  ≡
  PlanckHbarSIPayloadRequest.planckUnitConvention
    canonicalPlanckHbarSIPayloadRequest
canonicalPlanckRegistryRowUnitMatchesRequest = refl

canonicalHbarRegistryRowUnitMatchesRequest :
  Registry.KnownConstantSlot.unit canonicalHbarRegistryRow
  ≡
  PlanckHbarSIPayloadRequest.hbarUnitConvention
    canonicalPlanckHbarSIPayloadRequest
canonicalHbarRegistryRowUnitMatchesRequest = refl

canonicalPlanckRegistryRowIsSIDefiningConstant :
  Registry.KnownConstantSlot.authorityClass canonicalPlanckRegistryRow
  ≡ Registry.exactSIDefiningConstant
canonicalPlanckRegistryRowIsSIDefiningConstant = refl

canonicalHbarRegistryRowIsSIDerivedConstant :
  Registry.KnownConstantSlot.authorityClass canonicalHbarRegistryRow
  ≡ Registry.exactSIDerivedConstant
canonicalHbarRegistryRowIsSIDerivedConstant = refl

canonicalPlanckHbarPayloadFieldKeyCountIs15 :
  PlanckHbarSIPayloadRequest.payloadFieldKeyCount
    canonicalPlanckHbarSIPayloadRequest
  ≡ 15
canonicalPlanckHbarPayloadFieldKeyCountIs15 = refl

canonicalPlanckHbarAuthorityArtifactPresentIsFalse :
  PlanckHbarSIPayloadRequest.authorityArtifactPresent
    canonicalPlanckHbarSIPayloadRequest
  ≡ false
canonicalPlanckHbarAuthorityArtifactPresentIsFalse = refl

canonicalPlanckHbarAcceptedAuthorityTokenPresentIsFalse :
  PlanckHbarSIPayloadRequest.acceptedAuthorityTokenPresent
    canonicalPlanckHbarSIPayloadRequest
  ≡ false
canonicalPlanckHbarAcceptedAuthorityTokenPresentIsFalse = refl

canonicalPlanckNumericValuePromotedIsFalse :
  PlanckHbarSIPayloadRequest.planckNumericValuePromoted
    canonicalPlanckHbarSIPayloadRequest
  ≡ false
canonicalPlanckNumericValuePromotedIsFalse = refl

canonicalHbarNumericValuePromotedIsFalse :
  PlanckHbarSIPayloadRequest.hbarNumericValuePromoted
    canonicalPlanckHbarSIPayloadRequest
  ≡ false
canonicalHbarNumericValuePromotedIsFalse = refl

canonicalPlanckHbarStoneConsumptionEnabledIsFalse :
  PlanckHbarSIPayloadRequest.stoneSchrodingerConsumptionEnabled
    canonicalPlanckHbarSIPayloadRequest
  ≡ false
canonicalPlanckHbarStoneConsumptionEnabledIsFalse = refl
