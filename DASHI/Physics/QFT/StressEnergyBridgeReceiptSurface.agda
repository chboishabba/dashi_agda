module DASHI.Physics.QFT.StressEnergyBridgeReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT
import DASHI.Physics.Closure.CosmologicalConstantSequesteringReceiptSurface as CC

------------------------------------------------------------------------
-- AQFT stress-energy bridge receipt surface.
--
-- This module records target sockets for stress-energy observables,
-- state-expectation values, conservation/Bianchi compatibility, and Wald
-- renormalisation ambiguity.  It does not construct a stress tensor, select a
-- state, solve renormalisation, prove Einstein coupling, or promote GRQFT/TOE.

data StressEnergyBridgeSurfaceStatus : Set where
  stressEnergyBridgeTargetsOnlyNoPromotion :
    StressEnergyBridgeSurfaceStatus

data StressEnergyBridgePromotionAuthorityToken : Set where

data StressEnergyOpenObligation : Set where
  missingAQFTStressTensorObservable :
    StressEnergyOpenObligation

  missingStateExpectationFunctional :
    StressEnergyOpenObligation

  missingRenormalisedExpectationValue :
    StressEnergyOpenObligation

  missingConservationLaw :
    StressEnergyOpenObligation

  missingBianchiCompatibility :
    StressEnergyOpenObligation

  missingWaldAmbiguitySelection :
    StressEnergyOpenObligation

  missingEinsteinEquationCouplingAdapter :
    StressEnergyOpenObligation

  missingWaldPrescriptionAuthority :
    StressEnergyOpenObligation

  missingWaldC1C2C3CoefficientSelection :
    StressEnergyOpenObligation

  missingCosmologicalConstantSequesteringInputPack :
    StressEnergyOpenObligation

canonicalStressEnergyOpenObligations :
  List StressEnergyOpenObligation
canonicalStressEnergyOpenObligations =
  missingAQFTStressTensorObservable
  ∷ missingStateExpectationFunctional
  ∷ missingRenormalisedExpectationValue
  ∷ missingConservationLaw
  ∷ missingBianchiCompatibility
  ∷ missingEinsteinEquationCouplingAdapter
  ∷ missingWaldPrescriptionAuthority
  ∷ missingWaldC1C2C3CoefficientSelection
  ∷ missingCosmologicalConstantSequesteringInputPack
  ∷ []

data StressEnergyResolvedObligation : Set where
  waldAmbiguitySelectionReclassifiedToPrescriptionAuthority :
    StressEnergyResolvedObligation

canonicalStressEnergyResolvedObligations :
  List StressEnergyResolvedObligation
canonicalStressEnergyResolvedObligations =
  waldAmbiguitySelectionReclassifiedToPrescriptionAuthority
  ∷ []

data StressEnergyAuthorityBlockedObligation : Set where
  waldPrescriptionAuthorityBlocked :
    StressEnergyAuthorityBlockedObligation

  waldCoefficientSelectionAuthorityBlocked :
    StressEnergyAuthorityBlockedObligation

  cosmologicalConstantSequesteringInputsBlocked :
    StressEnergyAuthorityBlockedObligation

canonicalStressEnergyAuthorityBlockedObligations :
  List StressEnergyAuthorityBlockedObligation
canonicalStressEnergyAuthorityBlockedObligations =
  waldPrescriptionAuthorityBlocked
  ∷ waldCoefficientSelectionAuthorityBlocked
  ∷ cosmologicalConstantSequesteringInputsBlocked
  ∷ []

data WaldAmbiguityParameter : Set where
  cosmologicalConstantCounterterm :
    WaldAmbiguityParameter

  einsteinHilbertCounterterm :
    WaldAmbiguityParameter

  curvatureSquaredCounterterm :
    WaldAmbiguityParameter

  boxCurvatureCounterterm :
    WaldAmbiguityParameter

  stateIndependentLocalCurvatureTerm :
    WaldAmbiguityParameter

canonicalWaldAmbiguityParameters :
  List WaldAmbiguityParameter
canonicalWaldAmbiguityParameters =
  cosmologicalConstantCounterterm
  ∷ einsteinHilbertCounterterm
  ∷ curvatureSquaredCounterterm
  ∷ boxCurvatureCounterterm
  ∷ stateIndependentLocalCurvatureTerm
  ∷ []

data WaldPrescriptionAuthorityToken : Set where

data StressEnergySelectedCoefficientReceiptStatus : Set where
  stressEnergySelectedCoefficientsModuloWaldAuthorityAndCCInputs :
    StressEnergySelectedCoefficientReceiptStatus

record StressEnergySelectedWaldCoefficientReceipt
  (inputs : CC.CosmologicalConstantExplicitInputPack) : Setω where
  field
    status :
      StressEnergySelectedCoefficientReceiptStatus

    waldPrescriptionAuthority :
      WaldPrescriptionAuthorityToken

    waldCoefficientReceipt :
      CC.WaldReceiptComplete inputs

    cosmologicalConstantCoefficientDisposition :
      CC.CosmologicalConstantWaldCoefficientDispositionSurface

    dispositionRecordedFromSequesteringReceipt :
      Bool

    dispositionRecordedFromSequesteringReceiptIsTrue :
      dispositionRecordedFromSequesteringReceipt ≡ true

    selectedCoefficients :
      List CC.WaldSelectedCoefficient

    selectedCoefficientsAreCanonical :
      selectedCoefficients
      ≡
      CC.canonicalWaldSelectedCoefficients

    c1CancelledBySequestering :
      Bool

    c1CancelledBySequesteringIsTrue :
      c1CancelledBySequestering ≡ true

    c2CalibratedByNewton :
      Bool

    c2CalibratedByNewtonIsTrue :
      c2CalibratedByNewton ≡ true

    c3SelectedZeroWithinCassini :
      Bool

    c3SelectedZeroWithinCassiniIsTrue :
      c3SelectedZeroWithinCassini ≡ true

    stressEnergyBridgePromotedModuloWaldAndCoefficients :
      Bool

    stressEnergyBridgePromotedModuloWaldAndCoefficientsIsTrue :
      stressEnergyBridgePromotedModuloWaldAndCoefficients ≡ true

    unconditionalEinsteinSourcePromoted :
      Bool

    unconditionalEinsteinSourcePromotedIsFalse :
      unconditionalEinsteinSourcePromoted ≡ false

    receiptBoundary :
      List String

open StressEnergySelectedWaldCoefficientReceipt public

stressEnergySelectedWaldCoefficientReceiptFromAuthority :
  (inputs : CC.CosmologicalConstantExplicitInputPack) →
  WaldPrescriptionAuthorityToken →
  StressEnergySelectedWaldCoefficientReceipt inputs
stressEnergySelectedWaldCoefficientReceiptFromAuthority inputs authority =
  record
    { status =
        stressEnergySelectedCoefficientsModuloWaldAuthorityAndCCInputs
    ; waldPrescriptionAuthority =
        authority
    ; waldCoefficientReceipt =
        CC.waldReceiptCompleteFromExplicitInputs inputs
    ; cosmologicalConstantCoefficientDisposition =
        CC.CosmologicalConstantReceipt.coefficientDisposition
          (CC.WaldReceiptComplete.sequesteringReceipt
            (CC.waldReceiptCompleteFromExplicitInputs inputs))
    ; dispositionRecordedFromSequesteringReceipt =
        true
    ; dispositionRecordedFromSequesteringReceiptIsTrue =
        refl
    ; selectedCoefficients =
        CC.canonicalWaldSelectedCoefficients
    ; selectedCoefficientsAreCanonical =
        refl
    ; c1CancelledBySequestering =
        true
    ; c1CancelledBySequesteringIsTrue =
        refl
    ; c2CalibratedByNewton =
        true
    ; c2CalibratedByNewtonIsTrue =
        refl
    ; c3SelectedZeroWithinCassini =
        true
    ; c3SelectedZeroWithinCassiniIsTrue =
        refl
    ; stressEnergyBridgePromotedModuloWaldAndCoefficients =
        true
    ; stressEnergyBridgePromotedModuloWaldAndCoefficientsIsTrue =
        refl
    ; unconditionalEinsteinSourcePromoted =
        false
    ; unconditionalEinsteinSourcePromotedIsFalse =
        refl
    ; receiptBoundary =
        "Stress-energy bridge promotion is available only modulo Wald prescription authority and explicit c1/c2/c3 coefficient receipts"
        ∷ "the c1/c2/c3 receipts are supplied by WaldReceiptComplete: sequestering cancellation, Newton calibration, and Cassini-zero selection"
        ∷ "this receipt does not construct a stress tensor, prove conservation, or promote an unconditional sourced Einstein equation"
        ∷ []
    }

data WaldC1C2C3Parameter : Set where
  c1 :
    WaldC1C2C3Parameter

  c2 :
    WaldC1C2C3Parameter

  c3 :
    WaldC1C2C3Parameter

canonicalWaldC1C2C3Parameters :
  List WaldC1C2C3Parameter
canonicalWaldC1C2C3Parameters =
  c1
  ∷ c2
  ∷ c3
  ∷ []

data WaldAdapterParameterRole : Set where
  localCurvatureAmbiguityCoefficient :
    WaldAdapterParameterRole

  conservedTensorAmbiguityCoefficient :
    WaldAdapterParameterRole

  stateIndependentRenormalisationCoefficient :
    WaldAdapterParameterRole

data WaldAdapterParameterSurfaceStatus : Set where
  waldAdapterParametersRecordedNoCoefficientSelection :
    WaldAdapterParameterSurfaceStatus

record WaldC1C2C3AdapterParameterSurface : Setω where
  field
    status :
      WaldAdapterParameterSurfaceStatus

    c1Parameter :
      WaldC1C2C3Parameter

    c1ParameterIsC1 :
      c1Parameter ≡ c1

    c1Role :
      WaldAdapterParameterRole

    c2Parameter :
      WaldC1C2C3Parameter

    c2ParameterIsC2 :
      c2Parameter ≡ c2

    c2Role :
      WaldAdapterParameterRole

    c3Parameter :
      WaldC1C2C3Parameter

    c3ParameterIsC3 :
      c3Parameter ≡ c3

    c3Role :
      WaldAdapterParameterRole

    parameters :
      List WaldC1C2C3Parameter

    parametersAreCanonical :
      parameters
      ≡
      canonicalWaldC1C2C3Parameters

    adapterBoundary :
      String

    adapterBoundary-v :
      adapterBoundary
      ≡
      "c1-c2-c3-are-Wald-adapter-parameters-for-local-curvature-renormalisation-ambiguity-not-selected-physical-coefficients"

    coefficientValuesSelected :
      Bool

    coefficientValuesSelectedIsFalse :
      coefficientValuesSelected ≡ false

    stressEnergyAdapterPromoted :
      Bool

    stressEnergyAdapterPromotedIsFalse :
      stressEnergyAdapterPromoted ≡ false

    noSelectionWithoutAuthority :
      WaldPrescriptionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open WaldC1C2C3AdapterParameterSurface public

canonicalWaldC1C2C3AdapterParameterSurface :
  WaldC1C2C3AdapterParameterSurface
canonicalWaldC1C2C3AdapterParameterSurface =
  record
    { status =
        waldAdapterParametersRecordedNoCoefficientSelection
    ; c1Parameter =
        c1
    ; c1ParameterIsC1 =
        refl
    ; c1Role =
        localCurvatureAmbiguityCoefficient
    ; c2Parameter =
        c2
    ; c2ParameterIsC2 =
        refl
    ; c2Role =
        conservedTensorAmbiguityCoefficient
    ; c3Parameter =
        c3
    ; c3ParameterIsC3 =
        refl
    ; c3Role =
        stateIndependentRenormalisationCoefficient
    ; parameters =
        canonicalWaldC1C2C3Parameters
    ; parametersAreCanonical =
        refl
    ; adapterBoundary =
        "c1-c2-c3-are-Wald-adapter-parameters-for-local-curvature-renormalisation-ambiguity-not-selected-physical-coefficients"
    ; adapterBoundary-v =
        refl
    ; coefficientValuesSelected =
        false
    ; coefficientValuesSelectedIsFalse =
        refl
    ; stressEnergyAdapterPromoted =
        false
    ; stressEnergyAdapterPromotedIsFalse =
        refl
    ; noSelectionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "c1/c2/c3 are adapter parameters for the Wald ambiguity surface"
        ∷ "the surface records roles for the ambiguity coefficients but no coefficient carrier or values"
        ∷ "selecting coefficients still requires renormalisation-scheme authority, conservation proof, and physical normalisation"
        ∷ []
    }

data WaldAmbiguityClass : Set where
  traceAnomalyCurvatureSquaredClass :
    WaldAmbiguityClass

  conservedLocalCurvatureClass :
    WaldAmbiguityClass

  stateIndependentRenormalisationClass :
    WaldAmbiguityClass

data WaldPrescriptionStatus : Set where
  waldPrescriptionInterfaceOnlyNoSelection :
    WaldPrescriptionStatus

data WaldAmbiguityClassificationStatus : Set where
  waldAmbiguityClassifiedNoCoefficientChoice :
    WaldAmbiguityClassificationStatus

data WaldPrescriptionMissingPrimitive : Set where
  missingCoefficientValueCarrier :
    WaldPrescriptionMissingPrimitive

  missingLocalCurvatureTensorBasis :
    WaldPrescriptionMissingPrimitive

  missingRenormalisationSchemeAuthority :
    WaldPrescriptionMissingPrimitive

  missingConservationProofForSelectedCoefficients :
    WaldPrescriptionMissingPrimitive

  missingPhysicalNormalisationCondition :
    WaldPrescriptionMissingPrimitive

canonicalWaldPrescriptionMissingPrimitives :
  List WaldPrescriptionMissingPrimitive
canonicalWaldPrescriptionMissingPrimitives =
  missingCoefficientValueCarrier
  ∷ missingLocalCurvatureTensorBasis
  ∷ missingRenormalisationSchemeAuthority
  ∷ missingConservationProofForSelectedCoefficients
  ∷ missingPhysicalNormalisationCondition
  ∷ []

record WaldAmbiguityClassificationInterface : Setω where
  field
    status :
      WaldAmbiguityClassificationStatus

    c1Parameter :
      WaldC1C2C3Parameter

    c1ParameterIsC1 :
      c1Parameter ≡ c1

    c2Parameter :
      WaldC1C2C3Parameter

    c2ParameterIsC2 :
      c2Parameter ≡ c2

    c3Parameter :
      WaldC1C2C3Parameter

    c3ParameterIsC3 :
      c3Parameter ≡ c3

    c1Class :
      WaldAmbiguityClass

    c2Class :
      WaldAmbiguityClass

    c3Class :
      WaldAmbiguityClass

    cosmologicalConstantCoefficientDisposition :
      CC.CosmologicalConstantWaldCoefficientDispositionSurface

    coefficientParameters :
      List WaldC1C2C3Parameter

    coefficientParametersAreCanonical :
      coefficientParameters
      ≡
      canonicalWaldC1C2C3Parameters

    classificationBoundary :
      List String

    coefficientValuesSelected :
      Bool

    coefficientValuesSelectedIsFalse :
      coefficientValuesSelected ≡ false

open WaldAmbiguityClassificationInterface public

canonicalWaldAmbiguityClassificationInterface :
  WaldAmbiguityClassificationInterface
canonicalWaldAmbiguityClassificationInterface =
  record
    { status =
        waldAmbiguityClassifiedNoCoefficientChoice
    ; c1Parameter =
        c1
    ; c1ParameterIsC1 =
        refl
    ; c2Parameter =
        c2
    ; c2ParameterIsC2 =
        refl
    ; c3Parameter =
        c3
    ; c3ParameterIsC3 =
        refl
    ; c1Class =
        traceAnomalyCurvatureSquaredClass
    ; c2Class =
        conservedLocalCurvatureClass
    ; c3Class =
        stateIndependentRenormalisationClass
    ; cosmologicalConstantCoefficientDisposition =
        CC.canonicalCosmologicalConstantWaldCoefficientDispositionSurface
    ; coefficientParameters =
        canonicalWaldC1C2C3Parameters
    ; coefficientParametersAreCanonical =
        refl
    ; classificationBoundary =
        "c1/c2/c3 are coefficient slots for the Wald local curvature ambiguity interface"
        ∷ "cosmological-constant handling classifies c1 as sequestering-cancelled, c2 as Newton-calibrated, and c3 as observationally bounded"
        ∷ "classification names the ambiguity classes but does not provide numerical coefficient values or external input receipts"
        ∷ "the selected prescription must also prove conservation compatibility before Einstein sourcing"
        ∷ []
    ; coefficientValuesSelected =
        false
    ; coefficientValuesSelectedIsFalse =
        refl
    }

record WaldPrescription : Setω where
  field
    status :
      WaldPrescriptionStatus

    classificationInterface :
      WaldAmbiguityClassificationInterface

    adapterParameterSurface :
      WaldC1C2C3AdapterParameterSurface

    cosmologicalConstantSequesteringSurface :
      CC.CosmologicalConstantSequesteringReceiptSurface

    cosmologicalConstantCoefficientDisposition :
      CC.CosmologicalConstantWaldCoefficientDispositionSurface

    prescriptionLabel :
      String

    missingPrimitives :
      List WaldPrescriptionMissingPrimitive

    missingPrimitivesAreCanonical :
      missingPrimitives
      ≡
      canonicalWaldPrescriptionMissingPrimitives

    c1Slot :
      WaldC1C2C3Parameter

    c1SlotIsC1 :
      c1Slot ≡ c1

    c2Slot :
      WaldC1C2C3Parameter

    c2SlotIsC2 :
      c2Slot ≡ c2

    c3Slot :
      WaldC1C2C3Parameter

    c3SlotIsC3 :
      c3Slot ≡ c3

    prescriptionSelected :
      Bool

    prescriptionSelectedIsFalse :
      prescriptionSelected ≡ false

    prescriptionAuthorityBlocked :
      WaldPrescriptionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open WaldPrescription public

canonicalWaldPrescription :
  WaldPrescription
canonicalWaldPrescription =
  record
    { status =
        waldPrescriptionInterfaceOnlyNoSelection
    ; classificationInterface =
        canonicalWaldAmbiguityClassificationInterface
    ; adapterParameterSurface =
        canonicalWaldC1C2C3AdapterParameterSurface
    ; cosmologicalConstantSequesteringSurface =
        CC.canonicalCosmologicalConstantSequesteringReceiptSurface
    ; cosmologicalConstantCoefficientDisposition =
        CC.canonicalCosmologicalConstantWaldCoefficientDispositionSurface
    ; prescriptionLabel =
        "unselected-Wald-prescription-interface"
    ; missingPrimitives =
        canonicalWaldPrescriptionMissingPrimitives
    ; missingPrimitivesAreCanonical =
        refl
    ; c1Slot =
        c1
    ; c1SlotIsC1 =
        refl
    ; c2Slot =
        c2
    ; c2SlotIsC2 =
        refl
    ; c3Slot =
        c3
    ; c3SlotIsC3 =
        refl
    ; prescriptionSelected =
        false
    ; prescriptionSelectedIsFalse =
        refl
    ; prescriptionAuthorityBlocked =
        λ ()
    ; receiptBoundary =
        "WaldPrescription is an interface for selecting c1/c2/c3 ambiguity coefficients"
        ∷ "cosmological-constant use is restricted to the KP sequestering v2 input surface"
        ∷ "c1 cancellation, c2 Newton calibration, and c3 observational bound require explicit external receipt tokens"
        ∷ "no coefficient carrier, tensor basis, scheme authority, conservation proof, or physical normalisation condition is supplied here"
        ∷ "the prescription does not promote a stress-energy source or Einstein equation"
        ∷ []
    }

postulate
  StressTensorObservable :
    AQFT.Region →
    Set

  AQFTState :
    Set

  StressTensorExpectation :
    AQFT.Region →
    Set

  RenormalisedStressTensorExpectation :
    AQFT.Region →
    Set

  GeometryBackground :
    Set

  DivergenceFreeLaw :
    Set

  BianchiCompatibilityLaw :
    Set

  EinsteinCouplingAdapter :
    Set

  stressTensorObservableTarget :
    (region : AQFT.Region) →
    StressTensorObservable region

  stressTensorStateExpectationTarget :
    (region : AQFT.Region) →
    AQFTState →
    StressTensorObservable region →
    StressTensorExpectation region

  renormalisedExpectationTarget :
    (region : AQFT.Region) →
    StressTensorExpectation region →
    RenormalisedStressTensorExpectation region

record WaldAmbiguityBoundaryReceipt : Setω where
  field
    status :
      StressEnergyBridgeSurfaceStatus

    waldAmbiguityParameters :
      List WaldAmbiguityParameter

    waldAmbiguityParametersAreCanonical :
      waldAmbiguityParameters
      ≡
      canonicalWaldAmbiguityParameters

    waldClassificationInterface :
      WaldAmbiguityClassificationInterface

    waldPrescription :
      WaldPrescription

    waldAdapterParameterSurface :
      WaldC1C2C3AdapterParameterSurface

    cosmologicalConstantSequesteringSurface :
      CC.CosmologicalConstantSequesteringReceiptSurface

    cosmologicalConstantCoefficientDisposition :
      CC.CosmologicalConstantWaldCoefficientDispositionSurface

    selectedCoefficientReceiptShape :
      String

    selectedCoefficientReceiptShape-v :
      selectedCoefficientReceiptShape
      ≡
      "StressEnergySelectedWaldCoefficientReceipt-consumes-WaldPrescriptionAuthorityToken-plus-CC-WaldReceiptComplete-inputs"

    renormalisationAmbiguityBoundary :
      String

    localCurvatureCountertermBoundary :
      String

    conservationCompatibilityBoundary :
      String

    einsteinSourceBoundary :
      String

    waldAmbiguityFixed :
      Bool

    waldAmbiguityFixedIsFalse :
      waldAmbiguityFixed ≡ false

    selectedCoefficientReceiptInterfaceRecorded :
      Bool

    selectedCoefficientReceiptInterfaceRecordedIsTrue :
      selectedCoefficientReceiptInterfaceRecorded ≡ true

    stressEnergySourcePromoted :
      Bool

    stressEnergySourcePromotedIsFalse :
      stressEnergySourcePromoted ≡ false

    noPromotionWithoutAuthority :
      StressEnergyBridgePromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open WaldAmbiguityBoundaryReceipt public

canonicalWaldAmbiguityBoundaryReceipt :
  WaldAmbiguityBoundaryReceipt
canonicalWaldAmbiguityBoundaryReceipt =
  record
    { status =
        stressEnergyBridgeTargetsOnlyNoPromotion
    ; waldAmbiguityParameters =
        canonicalWaldAmbiguityParameters
    ; waldAmbiguityParametersAreCanonical =
        refl
    ; waldClassificationInterface =
        canonicalWaldAmbiguityClassificationInterface
    ; waldPrescription =
        canonicalWaldPrescription
    ; waldAdapterParameterSurface =
        canonicalWaldC1C2C3AdapterParameterSurface
    ; cosmologicalConstantSequesteringSurface =
        CC.canonicalCosmologicalConstantSequesteringReceiptSurface
    ; cosmologicalConstantCoefficientDisposition =
        CC.canonicalCosmologicalConstantWaldCoefficientDispositionSurface
    ; selectedCoefficientReceiptShape =
        "StressEnergySelectedWaldCoefficientReceipt-consumes-WaldPrescriptionAuthorityToken-plus-CC-WaldReceiptComplete-inputs"
    ; selectedCoefficientReceiptShape-v =
        refl
    ; renormalisationAmbiguityBoundary =
        "renormalised stress-energy is defined only up to Wald local curvature ambiguities until a selection receipt is supplied"
    ; localCurvatureCountertermBoundary =
        "cosmological, Einstein-Hilbert, curvature-squared, box-curvature, and state-independent curvature terms remain named parameters"
    ; conservationCompatibilityBoundary =
        "conservation and Bianchi compatibility are bridge obligations, not equations proved by this receipt"
    ; einsteinSourceBoundary =
        "no sourced Einstein equation is promoted from this Wald ambiguity boundary"
    ; waldAmbiguityFixed =
        false
    ; waldAmbiguityFixedIsFalse =
        refl
    ; selectedCoefficientReceiptInterfaceRecorded =
        true
    ; selectedCoefficientReceiptInterfaceRecordedIsTrue =
        refl
    ; stressEnergySourcePromoted =
        false
    ; stressEnergySourcePromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "WaldAmbiguityBoundaryReceipt is a non-promoting receipt for stress-energy renormalisation ambiguity"
        ∷ "it records the ambiguity parameters but does not select a renormalisation prescription"
        ∷ "it records the selected-coefficient interface: Wald authority plus CC.WaldReceiptComplete inputs select c1/c2/c3"
        ∷ "it records a c1/c2/c3 WaldPrescription classification interface without coefficient values"
        ∷ "it records the cosmological-constant sequestering surface: c1 cancelled only by KP-v2 sequestering inputs, c2 by Newton calibration, c3 by observational bound"
        ∷ "it records c1/c2/c3 as adapter parameters for local curvature ambiguity without selecting physical coefficients"
        ∷ "it does not construct a stress tensor, state expectation, conservation law, Bianchi law, or Einstein coupling"
        ∷ []
    }

record StressEnergyBridgeReceiptSurface : Setω where
  field
    status :
      StressEnergyBridgeSurfaceStatus

    aqftNetSurface :
      AQFT.AQFTTypedNetSurface

    waldAmbiguityReceipt :
      WaldAmbiguityBoundaryReceipt

    stressEnergyOpenObligations :
      List StressEnergyOpenObligation

    stressEnergyOpenObligationsAreCanonical :
      stressEnergyOpenObligations
      ≡
      canonicalStressEnergyOpenObligations

    stressEnergyResolvedObligations :
      List StressEnergyResolvedObligation

    stressEnergyResolvedObligationsAreCanonical :
      stressEnergyResolvedObligations
      ≡
      canonicalStressEnergyResolvedObligations

    stressEnergyAuthorityBlockedObligations :
      List StressEnergyAuthorityBlockedObligation

    stressEnergyAuthorityBlockedObligationsAreCanonical :
      stressEnergyAuthorityBlockedObligations
      ≡
      canonicalStressEnergyAuthorityBlockedObligations

    waldAmbiguityParameters :
      List WaldAmbiguityParameter

    waldAmbiguityParametersAreCanonical :
      waldAmbiguityParameters
      ≡
      canonicalWaldAmbiguityParameters

    waldClassificationInterface :
      WaldAmbiguityClassificationInterface

    waldPrescription :
      WaldPrescription

    waldAdapterParameterSurface :
      WaldC1C2C3AdapterParameterSurface

    cosmologicalConstantSequesteringSurface :
      CC.CosmologicalConstantSequesteringReceiptSurface

    cosmologicalConstantCoefficientDisposition :
      CC.CosmologicalConstantWaldCoefficientDispositionSurface

    selectedCoefficientReceiptShape :
      String

    selectedCoefficientReceiptShape-v :
      selectedCoefficientReceiptShape
      ≡
      "StressEnergySelectedWaldCoefficientReceipt-promotes-only-modulo-Wald-authority-and-explicit-cosmological-constant-input-pack"

    stressTensorObservable :
      (region : AQFT.Region) →
      Set

    aqftState :
      Set

    stressTensorExpectation :
      (region : AQFT.Region) →
      Set

    renormalisedStressTensorExpectation :
      (region : AQFT.Region) →
      Set

    geometryBackground :
      Set

    conservationLawTarget :
      Set

    bianchiCompatibilityTarget :
      Set

    einsteinCouplingAdapterTarget :
      Set

    observableTarget :
      (region : AQFT.Region) →
      stressTensorObservable region

    stateExpectationTarget :
      (region : AQFT.Region) →
      aqftState →
      stressTensorObservable region →
      stressTensorExpectation region

    renormalisationTarget :
      (region : AQFT.Region) →
      stressTensorExpectation region →
      renormalisedStressTensorExpectation region

    conservationEquationLabel :
      String

    bianchiCompatibilityLabel :
      String

    waldAmbiguityBoundary :
      String

    stressEnergyBridgePromoted :
      Bool

    stressEnergyBridgePromotedIsFalse :
      stressEnergyBridgePromoted ≡ false

    stressEnergyBridgePromotableModuloSelectedCoefficients :
      Bool

    stressEnergyBridgePromotableModuloSelectedCoefficientsIsTrue :
      stressEnergyBridgePromotableModuloSelectedCoefficients ≡ true

    noPromotionWithoutAuthority :
      StressEnergyBridgePromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open StressEnergyBridgeReceiptSurface public

canonicalStressEnergyBridgeReceiptSurface :
  StressEnergyBridgeReceiptSurface
canonicalStressEnergyBridgeReceiptSurface =
  record
    { status =
        stressEnergyBridgeTargetsOnlyNoPromotion
    ; aqftNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; waldAmbiguityReceipt =
        canonicalWaldAmbiguityBoundaryReceipt
    ; stressEnergyOpenObligations =
        canonicalStressEnergyOpenObligations
    ; stressEnergyOpenObligationsAreCanonical =
        refl
    ; stressEnergyResolvedObligations =
        canonicalStressEnergyResolvedObligations
    ; stressEnergyResolvedObligationsAreCanonical =
        refl
    ; stressEnergyAuthorityBlockedObligations =
        canonicalStressEnergyAuthorityBlockedObligations
    ; stressEnergyAuthorityBlockedObligationsAreCanonical =
        refl
    ; waldAmbiguityParameters =
        canonicalWaldAmbiguityParameters
    ; waldAmbiguityParametersAreCanonical =
        refl
    ; waldClassificationInterface =
        canonicalWaldAmbiguityClassificationInterface
    ; waldPrescription =
        canonicalWaldPrescription
    ; waldAdapterParameterSurface =
        canonicalWaldC1C2C3AdapterParameterSurface
    ; cosmologicalConstantSequesteringSurface =
        CC.canonicalCosmologicalConstantSequesteringReceiptSurface
    ; cosmologicalConstantCoefficientDisposition =
        CC.canonicalCosmologicalConstantWaldCoefficientDispositionSurface
    ; selectedCoefficientReceiptShape =
        "StressEnergySelectedWaldCoefficientReceipt-promotes-only-modulo-Wald-authority-and-explicit-cosmological-constant-input-pack"
    ; selectedCoefficientReceiptShape-v =
        refl
    ; stressTensorObservable =
        StressTensorObservable
    ; aqftState =
        AQFTState
    ; stressTensorExpectation =
        StressTensorExpectation
    ; renormalisedStressTensorExpectation =
        RenormalisedStressTensorExpectation
    ; geometryBackground =
        GeometryBackground
    ; conservationLawTarget =
        DivergenceFreeLaw
    ; bianchiCompatibilityTarget =
        BianchiCompatibilityLaw
    ; einsteinCouplingAdapterTarget =
        EinsteinCouplingAdapter
    ; observableTarget =
        stressTensorObservableTarget
    ; stateExpectationTarget =
        stressTensorStateExpectationTarget
    ; renormalisationTarget =
        renormalisedExpectationTarget
    ; conservationEquationLabel =
        "nabla_mu <T^{mu nu}>_ren = 0 target"
    ; bianchiCompatibilityLabel =
        "Bianchi compatibility: nabla_mu G^{mu nu} = 0 must match stress-energy conservation"
    ; waldAmbiguityBoundary =
        "Wald ambiguity parameters must be fixed before stress-energy can source a promoted Einstein equation"
    ; stressEnergyBridgePromoted =
        false
    ; stressEnergyBridgePromotedIsFalse =
        refl
    ; stressEnergyBridgePromotableModuloSelectedCoefficients =
        true
    ; stressEnergyBridgePromotableModuloSelectedCoefficientsIsTrue =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "stress tensor observable and state expectation are AQFT targets only"
        ∷ "renormalised expectation value is blocked on Wald ambiguity and state choice"
        ∷ "missingWaldAmbiguitySelection is reclassified to WaldPrescriptionAuthorityToken plus c1/c2/c3 coefficient selection"
        ∷ "Wald prescription classification exposes c1/c2/c3 slots but no selected coefficients or authority"
        ∷ "a selected-coefficient stress-energy receipt is available only from WaldPrescriptionAuthorityToken plus CC.WaldReceiptComplete explicit input pack"
        ∷ "cosmological constant treatment is KP sequestering v2 modulo compact-universe, sigma-protection, c1-cancellation, c2-Newton-calibration, c3-observational-bound, and provenance tokens"
        ∷ "c1/c2/c3 are recorded as adapter parameters for the Wald ambiguity and cannot source Einstein equations until selected by authority"
        ∷ "conservation and Bianchi compatibility are bridge obligations, not proved equations here"
        ∷ "no GRQFT, Einstein-equation, Standard Model, or TOE claim is promoted"
        ∷ []
    }
