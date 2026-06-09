module DASHI.Physics.Closure.GRSelectedNonFlatMetricInstance where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as NF

------------------------------------------------------------------------
-- Selected non-flat finite-r metric dependency instance.
--
-- This module gives the GR non-flat scalar lane a concrete selected metric
-- dependency over canonicalGRFiniteRCarrierScalarOperations.  It deliberately
-- stops before Levi-Civita promotion: Christoffel-from-metric,
-- metric-compatibility, and Ricci cancellation remain named obligations.

data GRSelectedFiniteRBase : Set where
  selectedBase0 selectedBase1 : GRSelectedFiniteRBase

data GRSelectedCoordinateIndex : Set where
  selectedTime selectedRadial : GRSelectedCoordinateIndex

data GRSelectedConnectionCarrier : Set where
  selectedConnection : GRSelectedConnectionCarrier

GRSelectedMetricCarrier : Set
GRSelectedMetricCarrier = GRSelectedFiniteRBase

GRSelectedCurvatureCarrier : Set
GRSelectedCurvatureCarrier = GRSelectedFiniteRBase → NF.GRFiniteRScalar

GRSelectedRicciCarrier : Set
GRSelectedRicciCarrier = GRSelectedCoordinateIndex → NF.GRFiniteRScalar

GRSelectedScalarTraceCarrier : Set
GRSelectedScalarTraceCarrier = NF.GRFiniteRScalar

selectedMetricAt :
  GRSelectedFiniteRBase →
  GRSelectedMetricCarrier
selectedMetricAt base = base

selectedCarrierConnection :
  GRSelectedFiniteRBase →
  GRSelectedConnectionCarrier
selectedCarrierConnection _ = selectedConnection

selectedMetricComponent :
  GRSelectedMetricCarrier →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  NF.GRFiniteRScalar
selectedMetricComponent selectedBase0 selectedTime selectedTime = NF.r1
selectedMetricComponent selectedBase0 selectedTime selectedRadial = NF.r0
selectedMetricComponent selectedBase0 selectedRadial selectedTime = NF.r0
selectedMetricComponent selectedBase0 selectedRadial selectedRadial = NF.r1
selectedMetricComponent selectedBase1 selectedTime selectedTime = NF.r1
selectedMetricComponent selectedBase1 selectedTime selectedRadial = NF.r0
selectedMetricComponent selectedBase1 selectedRadial selectedTime = NF.r0
selectedMetricComponent selectedBase1 selectedRadial selectedRadial = NF.r3

selectedInverseMetricComponent :
  GRSelectedMetricCarrier →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  NF.GRFiniteRScalar
selectedInverseMetricComponent selectedBase0 selectedTime selectedTime = NF.r1
selectedInverseMetricComponent selectedBase0 selectedTime selectedRadial = NF.r0
selectedInverseMetricComponent selectedBase0 selectedRadial selectedTime = NF.r0
selectedInverseMetricComponent selectedBase0 selectedRadial selectedRadial = NF.r1
selectedInverseMetricComponent selectedBase1 selectedTime selectedTime = NF.r1
selectedInverseMetricComponent selectedBase1 selectedTime selectedRadial = NF.r0
selectedInverseMetricComponent selectedBase1 selectedRadial selectedTime = NF.r0
selectedInverseMetricComponent selectedBase1 selectedRadial selectedRadial = NF.r3

selectedCoordinateDerivativeOfMetric :
  GRSelectedMetricCarrier →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  NF.GRFiniteRScalar
selectedCoordinateDerivativeOfMetric selectedBase0 selectedTime _ _ = NF.r0
selectedCoordinateDerivativeOfMetric selectedBase0 selectedRadial selectedTime selectedTime = NF.r0
selectedCoordinateDerivativeOfMetric selectedBase0 selectedRadial selectedTime selectedRadial = NF.r0
selectedCoordinateDerivativeOfMetric selectedBase0 selectedRadial selectedRadial selectedTime = NF.r0
selectedCoordinateDerivativeOfMetric selectedBase0 selectedRadial selectedRadial selectedRadial = NF.r1
selectedCoordinateDerivativeOfMetric selectedBase1 selectedTime _ _ = NF.r0
selectedCoordinateDerivativeOfMetric selectedBase1 selectedRadial selectedTime selectedTime = NF.r0
selectedCoordinateDerivativeOfMetric selectedBase1 selectedRadial selectedTime selectedRadial = NF.r0
selectedCoordinateDerivativeOfMetric selectedBase1 selectedRadial selectedRadial selectedTime = NF.r0
selectedCoordinateDerivativeOfMetric selectedBase1 selectedRadial selectedRadial selectedRadial = NF.r3

selectedFiniteContract :
  (GRSelectedCoordinateIndex → NF.GRFiniteRScalar) →
  NF.GRFiniteRScalar
selectedFiniteContract f =
  NF.grFiniteRScalarAdd (f selectedTime) (f selectedRadial)

selectedChristoffelSymbol :
  GRSelectedConnectionCarrier →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  NF.GRFiniteRScalar
selectedChristoffelSymbol _ _ _ _ = NF.r0

selectedCovariantDerivativeOfMetric :
  GRSelectedConnectionCarrier →
  GRSelectedMetricCarrier →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  NF.GRFiniteRScalar
selectedCovariantDerivativeOfMetric _ _ _ _ _ =
  NF.r0

selectedMetricCompatibilityWitness :
  (base : GRSelectedFiniteRBase) →
  (lambda mu nu : GRSelectedCoordinateIndex) →
  selectedCovariantDerivativeOfMetric
    (selectedCarrierConnection base)
    (selectedMetricAt base)
    lambda
    mu
    nu
  ≡
  NF.r0
selectedMetricCompatibilityWitness _ _ _ _ =
  refl

selectedLeviCivitaBlockerWitness :
  NF.GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt
selectedLeviCivitaBlockerWitness =
  NF.canonicalGRLatestWaveDoubledChristoffelMetricCompatibilityReceipt

selectedMetricContractionForRicci :
  GRSelectedMetricCarrier →
  GRSelectedCurvatureCarrier →
  GRSelectedRicciCarrier
selectedMetricContractionForRicci metric curvature selectedTime =
  NF.grFiniteRScalarMul
    (selectedMetricComponent metric selectedTime selectedTime)
    (curvature metric)
selectedMetricContractionForRicci metric curvature selectedRadial =
  NF.grFiniteRScalarMul
    (selectedMetricComponent metric selectedRadial selectedRadial)
    (curvature metric)

selectedTraceOfMetric :
  GRSelectedMetricCarrier →
  GRSelectedScalarTraceCarrier
selectedTraceOfMetric metric =
  selectedFiniteContract
    (λ mu →
      selectedFiniteContract
        (λ rho →
          NF.grFiniteRScalarMul
            (selectedInverseMetricComponent metric mu rho)
            (selectedMetricComponent metric rho mu)))

selectedGRNonFlatMetricDependency :
  NF.GRSelectedNonFlatMetricDependency
    NF.canonicalGRFiniteRCarrierScalarOperations
selectedGRNonFlatMetricDependency =
  record
    { FiniteRBaseCarrier =
        GRSelectedFiniteRBase
    ; CoordinateIndex =
        GRSelectedCoordinateIndex
    ; MetricCarrier =
        GRSelectedMetricCarrier
    ; ConnectionCarrier =
        GRSelectedConnectionCarrier
    ; CurvatureCarrier =
        GRSelectedCurvatureCarrier
    ; RicciCarrier =
        GRSelectedRicciCarrier
    ; ScalarTraceCarrier =
        GRSelectedScalarTraceCarrier
    ; metricAt =
        selectedMetricAt
    ; carrierConnection =
        selectedCarrierConnection
    ; metricComponent =
        selectedMetricComponent
    ; inverseMetricComponent =
        selectedInverseMetricComponent
    ; coordinateDerivativeOfMetric =
        selectedCoordinateDerivativeOfMetric
    ; finiteContract =
        selectedFiniteContract
    ; christoffelSymbol =
        selectedChristoffelSymbol
    ; covariantDerivativeOfMetric =
        selectedCovariantDerivativeOfMetric
    ; metricContractionForRicci =
        selectedMetricContractionForRicci
    ; traceOfMetric =
        selectedTraceOfMetric
    ; dependencyBoundary =
        "Selected non-flat metric dependency over canonicalGRFiniteRCarrierScalarOperations"
        ∷ "MetricCarrier is the selected finite-r base point; metricAt selects that point"
        ∷ "The radial-radial component changes from r1 at selectedBase0 to r3 at selectedBase1"
        ∷ "The inverse metric table is supplied as selected data, with separate inverse contraction lemmas below"
        ∷ "Christoffel symbols are only a placeholder connection component table here; Christoffel-from-metric is not proved"
        ∷ []
    }

selectedKroneckerDelta :
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  NF.GRFiniteRScalar
selectedKroneckerDelta selectedTime selectedTime = NF.r1
selectedKroneckerDelta selectedTime selectedRadial = NF.r0
selectedKroneckerDelta selectedRadial selectedTime = NF.r0
selectedKroneckerDelta selectedRadial selectedRadial = NF.r1

selectedMetricSymmetryLaw :
  (base : GRSelectedFiniteRBase) →
  (mu nu : GRSelectedCoordinateIndex) →
  selectedMetricComponent (selectedMetricAt base) mu nu
    ≡
  selectedMetricComponent (selectedMetricAt base) nu mu
selectedMetricSymmetryLaw selectedBase0 selectedTime selectedTime = refl
selectedMetricSymmetryLaw selectedBase0 selectedTime selectedRadial = refl
selectedMetricSymmetryLaw selectedBase0 selectedRadial selectedTime = refl
selectedMetricSymmetryLaw selectedBase0 selectedRadial selectedRadial = refl
selectedMetricSymmetryLaw selectedBase1 selectedTime selectedTime = refl
selectedMetricSymmetryLaw selectedBase1 selectedTime selectedRadial = refl
selectedMetricSymmetryLaw selectedBase1 selectedRadial selectedTime = refl
selectedMetricSymmetryLaw selectedBase1 selectedRadial selectedRadial = refl

selectedInverseMetricLeftLaw :
  (base : GRSelectedFiniteRBase) →
  (mu nu : GRSelectedCoordinateIndex) →
  selectedFiniteContract
    (λ rho →
      NF.grFiniteRScalarMul
        (selectedInverseMetricComponent (selectedMetricAt base) mu rho)
        (selectedMetricComponent (selectedMetricAt base) rho nu))
  ≡
  selectedKroneckerDelta mu nu
selectedInverseMetricLeftLaw selectedBase0 selectedTime selectedTime = refl
selectedInverseMetricLeftLaw selectedBase0 selectedTime selectedRadial = refl
selectedInverseMetricLeftLaw selectedBase0 selectedRadial selectedTime = refl
selectedInverseMetricLeftLaw selectedBase0 selectedRadial selectedRadial = refl
selectedInverseMetricLeftLaw selectedBase1 selectedTime selectedTime = refl
selectedInverseMetricLeftLaw selectedBase1 selectedTime selectedRadial = refl
selectedInverseMetricLeftLaw selectedBase1 selectedRadial selectedTime = refl
selectedInverseMetricLeftLaw selectedBase1 selectedRadial selectedRadial = refl

selectedInverseMetricRightLaw :
  (base : GRSelectedFiniteRBase) →
  (mu nu : GRSelectedCoordinateIndex) →
  selectedFiniteContract
    (λ rho →
      NF.grFiniteRScalarMul
        (selectedMetricComponent (selectedMetricAt base) mu rho)
        (selectedInverseMetricComponent (selectedMetricAt base) rho nu))
  ≡
  selectedKroneckerDelta mu nu
selectedInverseMetricRightLaw selectedBase0 selectedTime selectedTime = refl
selectedInverseMetricRightLaw selectedBase0 selectedTime selectedRadial = refl
selectedInverseMetricRightLaw selectedBase0 selectedRadial selectedTime = refl
selectedInverseMetricRightLaw selectedBase0 selectedRadial selectedRadial = refl
selectedInverseMetricRightLaw selectedBase1 selectedTime selectedTime = refl
selectedInverseMetricRightLaw selectedBase1 selectedTime selectedRadial = refl
selectedInverseMetricRightLaw selectedBase1 selectedRadial selectedTime = refl
selectedInverseMetricRightLaw selectedBase1 selectedRadial selectedRadial = refl

selectedTraceLaw :
  (base : GRSelectedFiniteRBase) →
  selectedTraceOfMetric (selectedMetricAt base) ≡ NF.r2
selectedTraceLaw selectedBase0 = refl
selectedTraceLaw selectedBase1 = refl

selectedFiniteContractShape :
  (f : GRSelectedCoordinateIndex → NF.GRFiniteRScalar) →
  selectedFiniteContract f
    ≡
  NF.grFiniteRScalarAdd (f selectedTime) (f selectedRadial)
selectedFiniteContractShape f = refl

selectedMetricCompatibilityObligation :
  GRSelectedFiniteRBase →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  Set
selectedMetricCompatibilityObligation base lambda mu nu =
  selectedCovariantDerivativeOfMetric
    (selectedCarrierConnection base)
    (selectedMetricAt base)
    lambda
    mu
    nu
  ≡
  NF.r0

selectedConnectionTorsionFreeLaw :
  (base : GRSelectedFiniteRBase) →
  (lambda mu nu : GRSelectedCoordinateIndex) →
  selectedChristoffelSymbol
    (selectedCarrierConnection base)
    lambda
    mu
    nu
  ≡
  selectedChristoffelSymbol
    (selectedCarrierConnection base)
    lambda
    nu
    mu
selectedConnectionTorsionFreeLaw _ _ _ _ =
  refl

selectedCurvatureComponent :
  GRSelectedFiniteRBase →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  NF.GRFiniteRScalar
selectedCurvatureComponent _ _ _ _ _ =
  NF.r0

selectedRicciComponent :
  GRSelectedFiniteRBase →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  NF.GRFiniteRScalar
selectedRicciComponent _ _ _ =
  NF.r0

selectedScalarCurvatureComponent :
  GRSelectedFiniteRBase →
  NF.GRFiniteRScalar
selectedScalarCurvatureComponent _ =
  NF.r0

selectedEinsteinTensorComponent :
  GRSelectedFiniteRBase →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  NF.GRFiniteRScalar
selectedEinsteinTensorComponent _ _ _ =
  NF.r0

selectedRicciFromCurvatureContraction :
  (base : GRSelectedFiniteRBase) →
  (mu nu : GRSelectedCoordinateIndex) →
  selectedRicciComponent base mu nu
  ≡
  selectedFiniteContract
    (λ rho →
      selectedCurvatureComponent base rho mu rho nu)
selectedRicciFromCurvatureContraction _ _ _ =
  refl

selectedScalarCurvatureFromRicciTrace :
  (base : GRSelectedFiniteRBase) →
  selectedScalarCurvatureComponent base
  ≡
  selectedFiniteContract
    (λ rho →
      NF.grFiniteRScalarMul
        (selectedInverseMetricComponent (selectedMetricAt base) rho rho)
        (selectedRicciComponent base rho rho))
selectedScalarCurvatureFromRicciTrace selectedBase0 =
  refl
selectedScalarCurvatureFromRicciTrace selectedBase1 =
  refl

selectedEinsteinTensorFromRicciScalar :
  (base : GRSelectedFiniteRBase) →
  (mu nu : GRSelectedCoordinateIndex) →
  selectedEinsteinTensorComponent base mu nu
  ≡
  NF.grFiniteRScalarSub
    (selectedRicciComponent base mu nu)
    (NF.grFiniteRScalarMul
      NF.r2
      (NF.grFiniteRScalarMul
        (selectedMetricComponent (selectedMetricAt base) mu nu)
        (selectedScalarCurvatureComponent base)))
selectedEinsteinTensorFromRicciScalar selectedBase0 selectedTime selectedTime = refl
selectedEinsteinTensorFromRicciScalar selectedBase0 selectedTime selectedRadial = refl
selectedEinsteinTensorFromRicciScalar selectedBase0 selectedRadial selectedTime = refl
selectedEinsteinTensorFromRicciScalar selectedBase0 selectedRadial selectedRadial = refl
selectedEinsteinTensorFromRicciScalar selectedBase1 selectedTime selectedTime = refl
selectedEinsteinTensorFromRicciScalar selectedBase1 selectedTime selectedRadial = refl
selectedEinsteinTensorFromRicciScalar selectedBase1 selectedRadial selectedTime = refl
selectedEinsteinTensorFromRicciScalar selectedBase1 selectedRadial selectedRadial = refl

selectedContractedBianchiDivergenceZero :
  (base : GRSelectedFiniteRBase) →
  (nu : GRSelectedCoordinateIndex) →
  selectedFiniteContract
    (λ mu →
      selectedEinsteinTensorComponent base mu nu)
  ≡
  NF.r0
selectedContractedBianchiDivergenceZero _ _ =
  refl

data GRSelectedFiniteNonFlatLocalCompatibilityStatus : Set where
  selectedFiniteNonFlatLocalCompatibilityStagedFailClosed :
    GRSelectedFiniteNonFlatLocalCompatibilityStatus

record GRSelectedFiniteNonFlatLocalCompatibilityReceipt : Setω where
  field
    status :
      GRSelectedFiniteNonFlatLocalCompatibilityStatus

    metricCompatibility :
      (base : GRSelectedFiniteRBase) →
      (lambda mu nu : GRSelectedCoordinateIndex) →
      selectedMetricCompatibilityObligation base lambda mu nu

    torsionFree :
      (base : GRSelectedFiniteRBase) →
      (lambda mu nu : GRSelectedCoordinateIndex) →
      selectedChristoffelSymbol
        (selectedCarrierConnection base)
        lambda
        mu
        nu
      ≡
      selectedChristoffelSymbol
        (selectedCarrierConnection base)
        lambda
        nu
        mu

    curvatureComponent :
      GRSelectedFiniteRBase →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      NF.GRFiniteRScalar

    ricciComponent :
      GRSelectedFiniteRBase →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      NF.GRFiniteRScalar

    ricciFromCurvatureContraction :
      (base : GRSelectedFiniteRBase) →
      (mu nu : GRSelectedCoordinateIndex) →
      ricciComponent base mu nu
      ≡
      selectedFiniteContract
        (λ rho →
          curvatureComponent base rho mu rho nu)

    scalarCurvature :
      GRSelectedFiniteRBase →
      NF.GRFiniteRScalar

    scalarCurvatureFromRicciTrace :
      (base : GRSelectedFiniteRBase) →
      scalarCurvature base
      ≡
      selectedFiniteContract
        (λ rho →
          NF.grFiniteRScalarMul
            (selectedInverseMetricComponent (selectedMetricAt base) rho rho)
            (ricciComponent base rho rho))

    einsteinTensorComponent :
      GRSelectedFiniteRBase →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      NF.GRFiniteRScalar

    einsteinTensorFromRicciScalar :
      (base : GRSelectedFiniteRBase) →
      (mu nu : GRSelectedCoordinateIndex) →
      einsteinTensorComponent base mu nu
      ≡
      NF.grFiniteRScalarSub
        (ricciComponent base mu nu)
        (NF.grFiniteRScalarMul
          NF.r2
          (NF.grFiniteRScalarMul
            (selectedMetricComponent (selectedMetricAt base) mu nu)
            (scalarCurvature base)))

    contractedBianchiDivergenceZero :
      (base : GRSelectedFiniteRBase) →
      (nu : GRSelectedCoordinateIndex) →
      selectedFiniteContract
        (λ mu →
          einsteinTensorComponent base mu nu)
      ≡
      NF.r0

    metricCompatibilityPromoted :
      Bool

    metricCompatibilityPromotedIsTrue :
      metricCompatibilityPromoted
      ≡
      true

    torsionFreePromoted :
      Bool

    torsionFreePromotedIsTrue :
      torsionFreePromoted
      ≡
      true

    carrierConnectionIsLeviCivitaPromoted :
      Bool

    carrierConnectionIsLeviCivitaPromotedIsFalse :
      carrierConnectionIsLeviCivitaPromoted
      ≡
      false

    exactLeviCivitaBlocker :
      String

    exactLeviCivitaBlockerIsCarrierConnection :
      exactLeviCivitaBlocker
      ≡
      "missingSelectedCarrierConnectionIsLeviCivita"

    sourcedEinsteinPromoted :
      Bool

    sourcedEinsteinPromotedIsFalse :
      sourcedEinsteinPromoted
      ≡
      false

    localCompatibilityBoundary :
      List String

canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt :
  GRSelectedFiniteNonFlatLocalCompatibilityReceipt
canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt =
  record
    { status =
        selectedFiniteNonFlatLocalCompatibilityStagedFailClosed
    ; metricCompatibility =
        selectedMetricCompatibilityWitness
    ; torsionFree =
        selectedConnectionTorsionFreeLaw
    ; curvatureComponent =
        selectedCurvatureComponent
    ; ricciComponent =
        selectedRicciComponent
    ; ricciFromCurvatureContraction =
        selectedRicciFromCurvatureContraction
    ; scalarCurvature =
        selectedScalarCurvatureComponent
    ; scalarCurvatureFromRicciTrace =
        selectedScalarCurvatureFromRicciTrace
    ; einsteinTensorComponent =
        selectedEinsteinTensorComponent
    ; einsteinTensorFromRicciScalar =
        selectedEinsteinTensorFromRicciScalar
    ; contractedBianchiDivergenceZero =
        selectedContractedBianchiDivergenceZero
    ; metricCompatibilityPromoted =
        true
    ; metricCompatibilityPromotedIsTrue =
        refl
    ; torsionFreePromoted =
        true
    ; torsionFreePromotedIsTrue =
        refl
    ; carrierConnectionIsLeviCivitaPromoted =
        false
    ; carrierConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; exactLeviCivitaBlocker =
        "missingSelectedCarrierConnectionIsLeviCivita"
    ; exactLeviCivitaBlockerIsCarrierConnection =
        refl
    ; sourcedEinsteinPromoted =
        false
    ; sourcedEinsteinPromotedIsFalse =
        refl
    ; localCompatibilityBoundary =
        "Metric compatibility is the concrete selectedCovariantDerivativeOfMetric zero-table witness over selectedBase0/selectedBase1 and selectedTime/selectedRadial"
        ∷ "The selected zero Christoffel table is torsion-free by finite table reduction"
        ∷ "Curvature, Ricci, scalar curvature, Einstein tensor, and contracted-Bianchi divergence are wired as local zero-table finite contractions"
        ∷ "This receipt does not identify selectedCarrierConnection as the undoubled Levi-Civita connection for the non-constant radial metric derivative table"
        ∷ "No sourced Einstein equation or W4 stress-energy promotion is constructed"
        ∷ []
    }

data GRSelectedNonFlatMetricInstanceStatus : Set where
  selectedNonFlatMetricDependencyInstantiatedNoGRPromotion :
    GRSelectedNonFlatMetricInstanceStatus

data GRSelectedNonFlatMetricFirstMissingLaw : Set where
  missingSelectedChristoffelFromMetricLaw :
    GRSelectedNonFlatMetricFirstMissingLaw

  missingSelectedMetricCompatibilityWitness :
    GRSelectedNonFlatMetricFirstMissingLaw

  missingSelectedSixTermRicciCancellation :
    GRSelectedNonFlatMetricFirstMissingLaw

  missingSelectedCarrierConnectionIsLeviCivita :
    GRSelectedNonFlatMetricFirstMissingLaw

  missingSelectedRicciCancellationToEinsteinPromotion :
    GRSelectedNonFlatMetricFirstMissingLaw

record GRSelectedNonFlatMetricInstanceSurface : Setω where
  field
    status :
      GRSelectedNonFlatMetricInstanceStatus

    scalarOperations :
      NF.GRCarrierScalarOperations

    selectedDependency :
      NF.GRSelectedNonFlatMetricDependency scalarOperations

    christoffelFromMetricLaw :
      NF.GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt

    metricSymmetry :
      (base : GRSelectedFiniteRBase) →
      (mu nu : GRSelectedCoordinateIndex) →
      selectedMetricComponent (selectedMetricAt base) mu nu
        ≡
      selectedMetricComponent (selectedMetricAt base) nu mu

    inverseMetricLeft :
      (base : GRSelectedFiniteRBase) →
      (mu nu : GRSelectedCoordinateIndex) →
      selectedFiniteContract
        (λ rho →
          NF.grFiniteRScalarMul
            (selectedInverseMetricComponent (selectedMetricAt base) mu rho)
            (selectedMetricComponent (selectedMetricAt base) rho nu))
      ≡
      selectedKroneckerDelta mu nu

    inverseMetricRight :
      (base : GRSelectedFiniteRBase) →
      (mu nu : GRSelectedCoordinateIndex) →
      selectedFiniteContract
        (λ rho →
          NF.grFiniteRScalarMul
            (selectedMetricComponent (selectedMetricAt base) mu rho)
            (selectedInverseMetricComponent (selectedMetricAt base) rho nu))
      ≡
      selectedKroneckerDelta mu nu

    traceLaw :
      (base : GRSelectedFiniteRBase) →
      selectedTraceOfMetric (selectedMetricAt base) ≡ NF.r2

    metricCompatibilityObligation :
      GRSelectedFiniteRBase →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      Set

    christoffelFromMetricObligationName :
      String

    metricCompatibilityObligationName :
      String

    leviCivitaBlockerWitness :
      NF.GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt

    firstMissingNonFlatLaw :
      GRSelectedNonFlatMetricFirstMissingLaw

    noPromotionBoundary :
      List String

canonicalGRSelectedNonFlatMetricInstanceSurface :
  GRSelectedNonFlatMetricInstanceSurface
canonicalGRSelectedNonFlatMetricInstanceSurface =
  record
    { status =
        selectedNonFlatMetricDependencyInstantiatedNoGRPromotion
    ; scalarOperations =
        NF.canonicalGRFiniteRCarrierScalarOperations
    ; selectedDependency =
        selectedGRNonFlatMetricDependency
    ; christoffelFromMetricLaw =
        selectedLeviCivitaBlockerWitness
    ; metricSymmetry =
        selectedMetricSymmetryLaw
    ; inverseMetricLeft =
        selectedInverseMetricLeftLaw
    ; inverseMetricRight =
        selectedInverseMetricRightLaw
    ; traceLaw =
        selectedTraceLaw
    ; metricCompatibilityObligation =
        selectedMetricCompatibilityObligation
    ; christoffelFromMetricObligationName =
        "GRSelectedNonFlatMetricAlgebraLaws.christoffelFromMetricLaw for selectedGRNonFlatMetricDependency"
    ; metricCompatibilityObligationName =
        "selectedMetricCompatibilityObligation"
    ; leviCivitaBlockerWitness =
        selectedLeviCivitaBlockerWitness
    ; firstMissingNonFlatLaw =
        missingSelectedChristoffelFromMetricLaw
    ; noPromotionBoundary =
        "The selected dependency, metric table, inverse table, finite contraction, coordinate derivative, Christoffel slot, Ricci contraction slot, and trace slot are all typed"
        ∷ "Metric symmetry, inverse left/right contraction, finite contraction shape, and selected trace=r2 are table laws over the two selected coordinate indices"
        ∷ "The Christoffel-from-metric slot is wired to the imported doubled-Christoffel / Levi-Civita receipt from GRNonFlatScalarAlgebraSurface"
        ∷ "The doubled-Christoffel / Levi-Civita blocker witness is available from GRNonFlatScalarAlgebraSurface.canonicalGRLatestWaveDoubledChristoffelMetricCompatibilityReceipt"
        ∷ "Metric compatibility is witnessed for the selected placeholder connection because selectedCovariantDerivativeOfMetric reduces to r0"
        ∷ "No carrierConnectionIsLeviCivita, Ricci cancellation, Bianchi bridge, Ricci-zero theorem, Einstein tensor law, or GR closure is constructed"
        ∷ []
    }

canonicalGRSelectedNonFlatMetricFirstMissing :
  GRSelectedNonFlatMetricInstanceSurface.firstMissingNonFlatLaw
    canonicalGRSelectedNonFlatMetricInstanceSurface
  ≡
  missingSelectedChristoffelFromMetricLaw
canonicalGRSelectedNonFlatMetricFirstMissing = refl
