module DASHI.Physics.Closure.GRSelectedNonFlatMetricInstance where

open import Agda.Primitive using (Setω)
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
selectedCovariantDerivativeOfMetric _ metric lambda mu nu =
  selectedCoordinateDerivativeOfMetric metric lambda mu nu

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
    ; firstMissingNonFlatLaw =
        missingSelectedChristoffelFromMetricLaw
    ; noPromotionBoundary =
        "The selected dependency, metric table, inverse table, finite contraction, coordinate derivative, Christoffel slot, Ricci contraction slot, and trace slot are all typed"
        ∷ "Metric symmetry, inverse left/right contraction, finite contraction shape, and selected trace=r2 are table laws over the two selected coordinate indices"
        ∷ "The Christoffel slot is not proved to be the Levi-Civita Christoffel expression for the non-flat metric"
        ∷ "Metric compatibility is exposed as an obligation, not as a witness"
        ∷ "No carrierConnectionIsLeviCivita, Ricci cancellation, Bianchi bridge, Ricci-zero theorem, Einstein tensor law, or GR closure is constructed"
        ∷ []
    }

canonicalGRSelectedNonFlatMetricFirstMissing :
  GRSelectedNonFlatMetricInstanceSurface.firstMissingNonFlatLaw
    canonicalGRSelectedNonFlatMetricInstanceSurface
  ≡
  missingSelectedChristoffelFromMetricLaw
canonicalGRSelectedNonFlatMetricFirstMissing = refl
