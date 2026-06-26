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

------------------------------------------------------------------------
-- QQ/symbolic-half selected doubled-Christoffel lift.
--
-- The finite-r scalar lane above intentionally keeps odd halves unavailable.
-- This local carrier records the selected Christoffel numerator over a
-- symbolic rational surface where multiplication by 1/2 is total and
-- definitional enough for 2 * (q * 1/2) = q.

data GRSelectedQQScalar : Set where
  qq0 qqHalf qqThird qq1 qq2 qq3 qq6 :
    GRSelectedQQScalar

  qqHalfProduct :
    GRSelectedQQScalar →
    GRSelectedQQScalar

  qqAddNode qqSubNode qqMulNode :
    GRSelectedQQScalar →
    GRSelectedQQScalar →
    GRSelectedQQScalar

qqAdd :
  GRSelectedQQScalar →
  GRSelectedQQScalar →
  GRSelectedQQScalar
qqAdd qq0 y = y
qqAdd x qq0 = x
qqAdd qq1 qq1 = qq2
qqAdd qq3 qq3 = qq6
qqAdd x y = qqAddNode x y

qqSub :
  GRSelectedQQScalar →
  GRSelectedQQScalar →
  GRSelectedQQScalar
qqSub x qq0 = x
qqSub qq1 qq1 = qq0
qqSub qq2 qq1 = qq1
qqSub qq6 qq3 = qq3
qqSub x y = qqSubNode x y

qqMul :
  GRSelectedQQScalar →
  GRSelectedQQScalar →
  GRSelectedQQScalar
qqMul qq0 _ = qq0
qqMul qq1 y = y
qqMul x qq0 = qq0
qqMul qqThird qq3 = qq1
qqMul qq2 qqHalf = qq1
qqMul qq2 qq1 = qq2
qqMul qq2 (qqHalfProduct q) = q
qqMul qq3 qqThird = qq1
qqMul x qqHalf = qqHalfProduct x
qqMul x y = qqMulNode x y

qqSumFin4 :
  GRSelectedQQScalar →
  GRSelectedQQScalar →
  GRSelectedQQScalar →
  GRSelectedQQScalar →
  GRSelectedQQScalar
qqSumFin4 a b c d =
  qqAdd (qqAdd (qqAdd a b) c) d

qqHalfTotal :
  GRSelectedQQScalar →
  NF.GRDiscretePartial GRSelectedQQScalar
qqHalfTotal q =
  NF.available (qqMul q qqHalf)

qqAdditiveIdentity :
  (q : GRSelectedQQScalar) →
  qqAdd qq0 q ≡ q
qqAdditiveIdentity _ = refl

qqMultiplicativeIdentity :
  (q : GRSelectedQQScalar) →
  qqMul qq1 q ≡ q
qqMultiplicativeIdentity _ = refl

undoublingLemma :
  (q : GRSelectedQQScalar) →
  qqMul qq2 (qqMul q qqHalf) ≡ q
undoublingLemma qq0 = refl
undoublingLemma qqHalf = refl
undoublingLemma qqThird = refl
undoublingLemma qq1 = refl
undoublingLemma qq2 = refl
undoublingLemma qq3 = refl
undoublingLemma qq6 = refl
undoublingLemma (qqHalfProduct q) = refl
undoublingLemma (qqAddNode q q') = refl
undoublingLemma (qqSubNode q q') = refl
undoublingLemma (qqMulNode q q') = refl

canonicalGRQQCarrierScalarOperations :
  NF.GRCarrierScalarOperations
canonicalGRQQCarrierScalarOperations =
  record
    { CarrierScalar =
        GRSelectedQQScalar
    ; zeroScalar =
        qq0
    ; oneScalar =
        qq1
    ; twoScalar =
        qq2
    ; _+_ =
        qqAdd
    ; _-_ =
        qqSub
    ; _*_ =
        qqMul
    ; sumFin4 =
        qqSumFin4
    ; discretePartial =
        NF.GRDiscretePartial
    ; half =
        qqHalfTotal
    ; additiveIdentityLaw =
        qqAdditiveIdentity
    ; multiplicativeIdentityLaw =
        qqMultiplicativeIdentity
    ; scalarBoundary =
        "Symbolic QQ scalar carrier for selected Christoffel undoubling"
        ∷ "qqHalf is total and returns q * 1/2 as a symbolic product"
        ∷ "undoublingLemma proves 2 * (q * 1/2) = q by table reduction for every symbolic QQ scalar"
        ∷ []
    }

finiteRScalarToQQ :
  NF.GRFiniteRScalar →
  GRSelectedQQScalar
finiteRScalarToQQ NF.r0 = qq0
finiteRScalarToQQ NF.r1 = qq1
finiteRScalarToQQ NF.r2 = qq2
finiteRScalarToQQ NF.r3 = qq3

qqSelectedMetricComponent :
  GRSelectedMetricCarrier →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedQQScalar
qqSelectedMetricComponent metric mu nu =
  finiteRScalarToQQ (selectedMetricComponent metric mu nu)

qqSelectedInverseMetricComponent :
  GRSelectedMetricCarrier →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedQQScalar
qqSelectedInverseMetricComponent selectedBase1 selectedRadial selectedRadial =
  qqThird
qqSelectedInverseMetricComponent metric mu nu =
  finiteRScalarToQQ (selectedInverseMetricComponent metric mu nu)

qqSelectedInverseMetricComponentBase1RadialRadialIsThird :
  qqSelectedInverseMetricComponent selectedBase1 selectedRadial selectedRadial
  ≡
  qqThird
qqSelectedInverseMetricComponentBase1RadialRadialIsThird =
  refl

qqSelectedCoordinateDerivativeOfMetric :
  GRSelectedMetricCarrier →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedQQScalar
qqSelectedCoordinateDerivativeOfMetric metric lambda mu nu =
  finiteRScalarToQQ
    (selectedCoordinateDerivativeOfMetric metric lambda mu nu)

qqSelectedFiniteContract :
  (GRSelectedCoordinateIndex → GRSelectedQQScalar) →
  GRSelectedQQScalar
qqSelectedFiniteContract f =
  qqAdd (f selectedTime) (f selectedRadial)

twoGammaTable :
  GRSelectedFiniteRBase →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedQQScalar
twoGammaTable base lambda mu nu =
  qqSelectedFiniteContract
    (λ sigma →
      qqMul
        (qqSelectedInverseMetricComponent
          (selectedMetricAt base)
          lambda
          sigma)
        (qqSub
          (qqAdd
            (qqSelectedCoordinateDerivativeOfMetric
              (selectedMetricAt base)
              mu
              nu
              sigma)
            (qqSelectedCoordinateDerivativeOfMetric
              (selectedMetricAt base)
              nu
              mu
              sigma))
          (qqSelectedCoordinateDerivativeOfMetric
            (selectedMetricAt base)
            sigma
            mu
            nu)))

qqUndoubledChristoffel :
  GRSelectedFiniteRBase →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedQQScalar
qqUndoubledChristoffel base lambda mu nu =
  qqMul (twoGammaTable base lambda mu nu) qqHalf

twoGammaTableAtInspectedSlotIsQQ1 :
  twoGammaTable
    selectedBase0
    selectedRadial
    selectedRadial
    selectedRadial
  ≡
  qq1
twoGammaTableAtInspectedSlotIsQQ1 =
  refl

twoGammaTableAtBase1RadialSlotIsQQ1 :
  twoGammaTable
    selectedBase1
    selectedRadial
    selectedRadial
    selectedRadial
  ≡
  qq1
twoGammaTableAtBase1RadialSlotIsQQ1 =
  refl

suppliedTwoGammaTable :
  GRSelectedFiniteRBase →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedQQScalar
suppliedTwoGammaTable selectedBase0 selectedRadial selectedRadial selectedRadial =
  qq1
suppliedTwoGammaTable selectedBase1 selectedRadial selectedRadial selectedRadial =
  qq1
suppliedTwoGammaTable _ _ _ _ =
  qq0

twoGammaTableMatchesSupplied :
  (base : GRSelectedFiniteRBase) →
  (lambda mu nu : GRSelectedCoordinateIndex) →
  twoGammaTable base lambda mu nu
  ≡
  suppliedTwoGammaTable base lambda mu nu
twoGammaTableMatchesSupplied selectedBase0 selectedTime selectedTime selectedTime = refl
twoGammaTableMatchesSupplied selectedBase0 selectedTime selectedTime selectedRadial = refl
twoGammaTableMatchesSupplied selectedBase0 selectedTime selectedRadial selectedTime = refl
twoGammaTableMatchesSupplied selectedBase0 selectedTime selectedRadial selectedRadial = refl
twoGammaTableMatchesSupplied selectedBase0 selectedRadial selectedTime selectedTime = refl
twoGammaTableMatchesSupplied selectedBase0 selectedRadial selectedTime selectedRadial = refl
twoGammaTableMatchesSupplied selectedBase0 selectedRadial selectedRadial selectedTime = refl
twoGammaTableMatchesSupplied selectedBase0 selectedRadial selectedRadial selectedRadial = refl
twoGammaTableMatchesSupplied selectedBase1 selectedTime selectedTime selectedTime = refl
twoGammaTableMatchesSupplied selectedBase1 selectedTime selectedTime selectedRadial = refl
twoGammaTableMatchesSupplied selectedBase1 selectedTime selectedRadial selectedTime = refl
twoGammaTableMatchesSupplied selectedBase1 selectedTime selectedRadial selectedRadial = refl
twoGammaTableMatchesSupplied selectedBase1 selectedRadial selectedTime selectedTime = refl
twoGammaTableMatchesSupplied selectedBase1 selectedRadial selectedTime selectedRadial = refl
twoGammaTableMatchesSupplied selectedBase1 selectedRadial selectedRadial selectedTime = refl
twoGammaTableMatchesSupplied selectedBase1 selectedRadial selectedRadial selectedRadial = refl

suppliedUndoubledChristoffelTable :
  GRSelectedFiniteRBase →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedCoordinateIndex →
  GRSelectedQQScalar
suppliedUndoubledChristoffelTable base lambda mu nu =
  qqMul (suppliedTwoGammaTable base lambda mu nu) qqHalf

qqUndoubledChristoffelMatchesSupplied :
  (base : GRSelectedFiniteRBase) →
  (lambda mu nu : GRSelectedCoordinateIndex) →
  qqUndoubledChristoffel base lambda mu nu
  ≡
  suppliedUndoubledChristoffelTable base lambda mu nu
qqUndoubledChristoffelMatchesSupplied selectedBase0 selectedTime selectedTime selectedTime = refl
qqUndoubledChristoffelMatchesSupplied selectedBase0 selectedTime selectedTime selectedRadial = refl
qqUndoubledChristoffelMatchesSupplied selectedBase0 selectedTime selectedRadial selectedTime = refl
qqUndoubledChristoffelMatchesSupplied selectedBase0 selectedTime selectedRadial selectedRadial = refl
qqUndoubledChristoffelMatchesSupplied selectedBase0 selectedRadial selectedTime selectedTime = refl
qqUndoubledChristoffelMatchesSupplied selectedBase0 selectedRadial selectedTime selectedRadial = refl
qqUndoubledChristoffelMatchesSupplied selectedBase0 selectedRadial selectedRadial selectedTime = refl
qqUndoubledChristoffelMatchesSupplied selectedBase0 selectedRadial selectedRadial selectedRadial = refl
qqUndoubledChristoffelMatchesSupplied selectedBase1 selectedTime selectedTime selectedTime = refl
qqUndoubledChristoffelMatchesSupplied selectedBase1 selectedTime selectedTime selectedRadial = refl
qqUndoubledChristoffelMatchesSupplied selectedBase1 selectedTime selectedRadial selectedTime = refl
qqUndoubledChristoffelMatchesSupplied selectedBase1 selectedTime selectedRadial selectedRadial = refl
qqUndoubledChristoffelMatchesSupplied selectedBase1 selectedRadial selectedTime selectedTime = refl
qqUndoubledChristoffelMatchesSupplied selectedBase1 selectedRadial selectedTime selectedRadial = refl
qqUndoubledChristoffelMatchesSupplied selectedBase1 selectedRadial selectedRadial selectedTime = refl
qqUndoubledChristoffelMatchesSupplied selectedBase1 selectedRadial selectedRadial selectedRadial = refl

qqUndoubledChristoffelAtInspectedSlotIsHalf :
  qqUndoubledChristoffel
    selectedBase0
    selectedRadial
    selectedRadial
    selectedRadial
  ≡
  qqHalf
qqUndoubledChristoffelAtInspectedSlotIsHalf =
  refl

qqUndoubledChristoffelAtBase1RadialSlotIsHalf :
  qqUndoubledChristoffel
    selectedBase1
    selectedRadial
    selectedRadial
    selectedRadial
  ≡
  qqHalf
qqUndoubledChristoffelAtBase1RadialSlotIsHalf =
  refl

record GRSelectedUndoubledChristoffelLift : Setω where
  field
    scalarOperations :
      NF.GRCarrierScalarOperations

    doubledChristoffel :
      GRSelectedFiniteRBase →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedQQScalar

    undoubledChristoffel :
      GRSelectedFiniteRBase →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedQQScalar

    doublesToDoubledChristoffel :
      (base : GRSelectedFiniteRBase) →
      (lambda mu nu : GRSelectedCoordinateIndex) →
      qqMul qq2 (undoubledChristoffel base lambda mu nu)
      ≡
      doubledChristoffel base lambda mu nu

    suppliedDoubledChristoffel :
      GRSelectedFiniteRBase →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedQQScalar

    doubledChristoffelMatchesSupplied :
      (base : GRSelectedFiniteRBase) →
      (lambda mu nu : GRSelectedCoordinateIndex) →
      doubledChristoffel base lambda mu nu
      ≡
      suppliedDoubledChristoffel base lambda mu nu

    suppliedUndoubledChristoffel :
      GRSelectedFiniteRBase →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedQQScalar

    undoubledChristoffelMatchesSupplied :
      (base : GRSelectedFiniteRBase) →
      (lambda mu nu : GRSelectedCoordinateIndex) →
      undoubledChristoffel base lambda mu nu
      ≡
      suppliedUndoubledChristoffel base lambda mu nu

    inspectedOddSlotDoublesFromQQHalf :
      qqMul
        qq2
        (undoubledChristoffel
          selectedBase0
          selectedRadial
          selectedRadial
          selectedRadial)
      ≡
      qq1

    liftBoundary :
      List String

constructQQLift :
  GRSelectedUndoubledChristoffelLift
constructQQLift =
  record
    { scalarOperations =
        canonicalGRQQCarrierScalarOperations
    ; doubledChristoffel =
        twoGammaTable
    ; undoubledChristoffel =
        qqUndoubledChristoffel
    ; doublesToDoubledChristoffel =
        λ base lambda mu nu → undoublingLemma (twoGammaTable base lambda mu nu)
    ; suppliedDoubledChristoffel =
        suppliedTwoGammaTable
    ; doubledChristoffelMatchesSupplied =
        twoGammaTableMatchesSupplied
    ; suppliedUndoubledChristoffel =
        suppliedUndoubledChristoffelTable
    ; undoubledChristoffelMatchesSupplied =
        qqUndoubledChristoffelMatchesSupplied
    ; inspectedOddSlotDoublesFromQQHalf =
        refl
    ; liftBoundary =
        "The selected doubled-Christoffel table is evaluated over symbolic QQ scalars"
        ∷ "The old finite-r odd slot is no longer impossible: undoubled Gamma at selectedBase0/radial/radial/radial is qqHalf"
        ∷ "The base1 radial/radial/radial slot also undoubles to qqHalf by adapting the supplied inverse-metric r3 slot to qqThird"
        ∷ "suppliedTwoGammaTable records exactly the two nonzero doubled radial slots, and twoGammaTableMatchesSupplied checks all selected slots"
        ∷ "doublesToDoubledChristoffel is exactly undoublingLemma applied pointwise to twoGammaTable"
        ∷ []
    }

constructQQLiftInspectedSlot :
  GRSelectedUndoubledChristoffelLift.inspectedOddSlotDoublesFromQQHalf
    constructQQLift
  ≡
  refl
constructQQLiftInspectedSlot =
  refl

data GRSelectedQQKnownNonzero :
  GRSelectedQQScalar →
  Set where
  selectedQQHalfNonzero :
    GRSelectedQQKnownNonzero qqHalf

  selectedQQThirdNonzero :
    GRSelectedQQKnownNonzero qqThird

  selectedQQOneNonzero :
    GRSelectedQQKnownNonzero qq1

record GRSelectedQQConnectionSurface : Setω where
  field
    scalarOperations :
      NF.GRCarrierScalarOperations

    selectedConnectionChristoffel :
      GRSelectedFiniteRBase →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedQQScalar

    suppliedSelectedConnectionChristoffel :
      GRSelectedFiniteRBase →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedCoordinateIndex →
      GRSelectedQQScalar

    selectedConnectionMatchesSupplied :
      (base : GRSelectedFiniteRBase) →
      (lambda mu nu : GRSelectedCoordinateIndex) →
      selectedConnectionChristoffel base lambda mu nu
      ≡
      suppliedSelectedConnectionChristoffel base lambda mu nu

    inspectedHalfAdapterSlotLaw :
      selectedConnectionChristoffel
        selectedBase1
        selectedRadial
        selectedRadial
        selectedRadial
      ≡
      qqHalf

    inspectedHalfAdapterNonzero :
      GRSelectedQQKnownNonzero
        (selectedConnectionChristoffel
          selectedBase1
          selectedRadial
          selectedRadial
          selectedRadial)

    inspectedHalfAdapterDoublesToSupplied :
      qqMul
        qq2
        (selectedConnectionChristoffel
          selectedBase1
          selectedRadial
          selectedRadial
          selectedRadial)
      ≡
      suppliedTwoGammaTable
        selectedBase1
        selectedRadial
        selectedRadial
        selectedRadial

    connectionBoundary :
      List String

canonicalGRSelectedQQConnectionSurface :
  GRSelectedQQConnectionSurface
canonicalGRSelectedQQConnectionSurface =
  record
    { scalarOperations =
        canonicalGRQQCarrierScalarOperations
    ; selectedConnectionChristoffel =
        qqUndoubledChristoffel
    ; suppliedSelectedConnectionChristoffel =
        suppliedUndoubledChristoffelTable
    ; selectedConnectionMatchesSupplied =
        qqUndoubledChristoffelMatchesSupplied
    ; inspectedHalfAdapterSlotLaw =
        qqUndoubledChristoffelAtBase1RadialSlotIsHalf
    ; inspectedHalfAdapterNonzero =
        selectedQQHalfNonzero
    ; inspectedHalfAdapterDoublesToSupplied =
        refl
    ; connectionBoundary =
        "Selected rational connection surface: Christoffel symbols are the QQ-undoubled metric-derived table"
        ∷ "The supplied selected connection is suppliedUndoubledChristoffelTable, and the exact match law is qqUndoubledChristoffelMatchesSupplied"
        ∷ "For the current selected metric tables, the inspected nonzero law is the half-adapter slot Gamma(radial,radial,radial)=qqHalf at selectedBase1"
        ∷ "This deliberately stays separate from selectedChristoffelSymbol, whose finite-r placeholder remains unchanged"
        ∷ []
    }

selectedQQConnectionInspectedHalfAdapterSlotLaw :
  GRSelectedQQConnectionSurface.selectedConnectionChristoffel
    canonicalGRSelectedQQConnectionSurface
    selectedBase1
    selectedRadial
    selectedRadial
    selectedRadial
  ≡
  qqHalf
selectedQQConnectionInspectedHalfAdapterSlotLaw =
  refl

selectedQQConnectionInspectedHalfAdapterNonzero :
  GRSelectedQQKnownNonzero
    (GRSelectedQQConnectionSurface.selectedConnectionChristoffel
      canonicalGRSelectedQQConnectionSurface
      selectedBase1
      selectedRadial
      selectedRadial
      selectedRadial)
selectedQQConnectionInspectedHalfAdapterNonzero =
  selectedQQHalfNonzero

selectedQQConnectionInspectedHalfAdapterDoublesToSupplied :
  qqMul
    qq2
    (GRSelectedQQConnectionSurface.selectedConnectionChristoffel
      canonicalGRSelectedQQConnectionSurface
      selectedBase1
      selectedRadial
      selectedRadial
      selectedRadial)
  ≡
  suppliedTwoGammaTable
    selectedBase1
    selectedRadial
    selectedRadial
    selectedRadial
selectedQQConnectionInspectedHalfAdapterDoublesToSupplied =
  refl

record GRSelectedQQUndoubledSuppliedNonzeroConnectionAdapter : Setω where
  field
    selectedQQConnectionSurface :
      GRSelectedQQConnectionSurface

    selectedQQConnectionSurfaceIsCanonical :
      Bool

    selectedQQConnectionSurfaceIsCanonicalIsTrue :
      selectedQQConnectionSurfaceIsCanonical ≡ true

    suppliedMatchLaw :
      (base : GRSelectedFiniteRBase) →
      (lambda mu nu : GRSelectedCoordinateIndex) →
      qqUndoubledChristoffel base lambda mu nu
      ≡
      suppliedUndoubledChristoffelTable base lambda mu nu

    suppliedMatchLawIsQQRoute :
      suppliedMatchLaw
      ≡
      qqUndoubledChristoffelMatchesSupplied

    nonzeroConnectionSlotLaw :
      qqUndoubledChristoffel
        selectedBase1
        selectedRadial
        selectedRadial
        selectedRadial
      ≡
      qqHalf

    nonzeroConnectionSlotWitness :
      GRSelectedQQKnownNonzero
        (qqUndoubledChristoffel
          selectedBase1
          selectedRadial
          selectedRadial
          selectedRadial)

    adapterBoundary :
      List String

canonicalGRSelectedQQUndoubledSuppliedNonzeroConnectionAdapter :
  GRSelectedQQUndoubledSuppliedNonzeroConnectionAdapter
canonicalGRSelectedQQUndoubledSuppliedNonzeroConnectionAdapter =
  record
    { selectedQQConnectionSurface =
        canonicalGRSelectedQQConnectionSurface
    ; selectedQQConnectionSurfaceIsCanonical =
        true
    ; selectedQQConnectionSurfaceIsCanonicalIsTrue =
        refl
    ; suppliedMatchLaw =
        qqUndoubledChristoffelMatchesSupplied
    ; suppliedMatchLawIsQQRoute =
        refl
    ; nonzeroConnectionSlotLaw =
        selectedQQConnectionInspectedHalfAdapterSlotLaw
    ; nonzeroConnectionSlotWitness =
        selectedQQHalfNonzero
    ; adapterBoundary =
        "Adapter tying the supplied QQ selected connection match directly to qqUndoubledChristoffelMatchesSupplied"
        ∷ "The selected connection is nonzero at selectedBase1/radial/radial/radial by the exact qqHalf slot law"
        ∷ "This is the rational half-adapter path for the current metric tables; no finite-r half or r0==r1 collapse is introduced"
        ∷ []
    }

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

selectedPairRadialUndoubledIsHalf :
  (base : GRSelectedFiniteRBase) →
  qqUndoubledChristoffel
    base
    selectedRadial
    selectedRadial
    selectedRadial
  ≡
  qqHalf
selectedPairRadialUndoubledIsHalf selectedBase0 =
  refl
selectedPairRadialUndoubledIsHalf selectedBase1 =
  refl

selectedPairRadialUndoubledNonzero :
  (base : GRSelectedFiniteRBase) →
  GRSelectedQQKnownNonzero
    (qqUndoubledChristoffel
      base
      selectedRadial
      selectedRadial
      selectedRadial)
selectedPairRadialUndoubledNonzero selectedBase0 =
  selectedQQHalfNonzero
selectedPairRadialUndoubledNonzero selectedBase1 =
  selectedQQHalfNonzero

selectedPairRadialUndoubledDoublesToDoubled :
  (base : GRSelectedFiniteRBase) →
  qqMul
    qq2
    (qqUndoubledChristoffel
      base
      selectedRadial
      selectedRadial
      selectedRadial)
  ≡
  twoGammaTable
    base
    selectedRadial
    selectedRadial
    selectedRadial
selectedPairRadialUndoubledDoublesToDoubled selectedBase0 =
  refl
selectedPairRadialUndoubledDoublesToDoubled selectedBase1 =
  refl

selectedPairRadialDoubledMatchesSupplied :
  (base : GRSelectedFiniteRBase) →
  twoGammaTable
    base
    selectedRadial
    selectedRadial
    selectedRadial
  ≡
  suppliedTwoGammaTable
    base
    selectedRadial
    selectedRadial
    selectedRadial
selectedPairRadialDoubledMatchesSupplied selectedBase0 =
  refl
selectedPairRadialDoubledMatchesSupplied selectedBase1 =
  refl

selectedPairRadialUndoubledMatchesSupplied :
  (base : GRSelectedFiniteRBase) →
  qqUndoubledChristoffel
    base
    selectedRadial
    selectedRadial
    selectedRadial
  ≡
  suppliedUndoubledChristoffelTable
    base
    selectedRadial
    selectedRadial
    selectedRadial
selectedPairRadialUndoubledMatchesSupplied selectedBase0 =
  refl
selectedPairRadialUndoubledMatchesSupplied selectedBase1 =
  refl

selectedPairRadialUndoubledDoublesToSupplied :
  (base : GRSelectedFiniteRBase) →
  qqMul
    qq2
    (qqUndoubledChristoffel
      base
      selectedRadial
      selectedRadial
      selectedRadial)
  ≡
  suppliedTwoGammaTable
    base
    selectedRadial
    selectedRadial
    selectedRadial
selectedPairRadialUndoubledDoublesToSupplied selectedBase0 =
  refl
selectedPairRadialUndoubledDoublesToSupplied selectedBase1 =
  refl

data GRSelectedQQChristoffelSelectedPairBridgeStatus : Set where
  selectedPairQQHalfUndoubledContinuumBridgeFailClosed :
    GRSelectedQQChristoffelSelectedPairBridgeStatus

record GRSelectedQQChristoffelSelectedPairContinuumBridge : Setω where
  field
    status :
      GRSelectedQQChristoffelSelectedPairBridgeStatus

    qqScalarOperations :
      NF.GRCarrierScalarOperations

    selectedQQLift :
      GRSelectedUndoubledChristoffelLift

    selectedQQConnectionAdapter :
      GRSelectedQQUndoubledSuppliedNonzeroConnectionAdapter

    continuumLawLocalReceipt :
      GRSelectedFiniteNonFlatLocalCompatibilityReceipt

    continuumLawLocalMetricCompatibilityPromoted :
      GRSelectedFiniteNonFlatLocalCompatibilityReceipt.metricCompatibilityPromoted
        continuumLawLocalReceipt
      ≡
      true

    continuumLawLocalLeviCivitaPromotionFalse :
      GRSelectedFiniteNonFlatLocalCompatibilityReceipt.carrierConnectionIsLeviCivitaPromoted
        continuumLawLocalReceipt
      ≡
      false

    base0RadialUndoubledIsHalf :
      qqUndoubledChristoffel
        selectedBase0
        selectedRadial
        selectedRadial
        selectedRadial
      ≡
      qqHalf

    base1RadialUndoubledIsHalf :
      qqUndoubledChristoffel
        selectedBase1
        selectedRadial
        selectedRadial
        selectedRadial
      ≡
      qqHalf

    selectedPairUndoubledIsHalf :
      (base : GRSelectedFiniteRBase) →
      qqUndoubledChristoffel
        base
        selectedRadial
        selectedRadial
        selectedRadial
      ≡
      qqHalf

    selectedPairUndoubledNonzero :
      (base : GRSelectedFiniteRBase) →
      GRSelectedQQKnownNonzero
        (qqUndoubledChristoffel
          base
          selectedRadial
          selectedRadial
          selectedRadial)

    selectedPairUndoubledDoublesToDoubled :
      (base : GRSelectedFiniteRBase) →
      qqMul
        qq2
        (qqUndoubledChristoffel
          base
          selectedRadial
          selectedRadial
          selectedRadial)
      ≡
      twoGammaTable
        base
        selectedRadial
        selectedRadial
        selectedRadial

    selectedPairDoubledMatchesSupplied :
      (base : GRSelectedFiniteRBase) →
      twoGammaTable
        base
        selectedRadial
        selectedRadial
        selectedRadial
      ≡
      suppliedTwoGammaTable
        base
        selectedRadial
        selectedRadial
        selectedRadial

    selectedPairUndoubledMatchesSupplied :
      (base : GRSelectedFiniteRBase) →
      qqUndoubledChristoffel
        base
        selectedRadial
        selectedRadial
        selectedRadial
      ≡
      suppliedUndoubledChristoffelTable
        base
        selectedRadial
        selectedRadial
        selectedRadial

    selectedPairUndoubledDoublesToSupplied :
      (base : GRSelectedFiniteRBase) →
      qqMul
        qq2
        (qqUndoubledChristoffel
          base
          selectedRadial
          selectedRadial
          selectedRadial)
      ≡
      suppliedTwoGammaTable
        base
        selectedRadial
        selectedRadial
        selectedRadial

    selectedQQAdapterIsCanonical :
      GRSelectedQQUndoubledSuppliedNonzeroConnectionAdapter.selectedQQConnectionSurfaceIsCanonical
        selectedQQConnectionAdapter
      ≡
      true

    selectedPairBridgeFeedsContinuumLawSurfaces :
      Bool

    selectedPairBridgeFeedsContinuumLawSurfacesIsTrue :
      selectedPairBridgeFeedsContinuumLawSurfaces
      ≡
      true

    arbitraryFiniteRChristoffelPromotion :
      Bool

    arbitraryFiniteRChristoffelPromotionIsFalse :
      arbitraryFiniteRChristoffelPromotion
      ≡
      false

    arbitraryFiniteRLeviCivitaPromotion :
      Bool

    arbitraryFiniteRLeviCivitaPromotionIsFalse :
      arbitraryFiniteRLeviCivitaPromotion
      ≡
      false

    finiteRImpossibleHalvingChanged :
      Bool

    finiteRImpossibleHalvingChangedIsFalse :
      finiteRImpossibleHalvingChanged
      ≡
      false

    arbitraryFiniteRPromotionBlockerName :
      String

    arbitraryFiniteRPromotionBlockerNameIsExplicit :
      arbitraryFiniteRPromotionBlockerName
      ≡
      "arbitraryFiniteRChristoffelOrLeviCivitaPromotionIsFalse"

    bridgeBoundary :
      List String

canonicalGRSelectedQQChristoffelSelectedPairContinuumBridge :
  GRSelectedQQChristoffelSelectedPairContinuumBridge
canonicalGRSelectedQQChristoffelSelectedPairContinuumBridge =
  record
    { status =
        selectedPairQQHalfUndoubledContinuumBridgeFailClosed
    ; qqScalarOperations =
        canonicalGRQQCarrierScalarOperations
    ; selectedQQLift =
        constructQQLift
    ; selectedQQConnectionAdapter =
        canonicalGRSelectedQQUndoubledSuppliedNonzeroConnectionAdapter
    ; continuumLawLocalReceipt =
        canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; continuumLawLocalMetricCompatibilityPromoted =
        refl
    ; continuumLawLocalLeviCivitaPromotionFalse =
        refl
    ; base0RadialUndoubledIsHalf =
        qqUndoubledChristoffelAtInspectedSlotIsHalf
    ; base1RadialUndoubledIsHalf =
        qqUndoubledChristoffelAtBase1RadialSlotIsHalf
    ; selectedPairUndoubledIsHalf =
        selectedPairRadialUndoubledIsHalf
    ; selectedPairUndoubledNonzero =
        selectedPairRadialUndoubledNonzero
    ; selectedPairUndoubledDoublesToDoubled =
        selectedPairRadialUndoubledDoublesToDoubled
    ; selectedPairDoubledMatchesSupplied =
        selectedPairRadialDoubledMatchesSupplied
    ; selectedPairUndoubledMatchesSupplied =
        selectedPairRadialUndoubledMatchesSupplied
    ; selectedPairUndoubledDoublesToSupplied =
        selectedPairRadialUndoubledDoublesToSupplied
    ; selectedQQAdapterIsCanonical =
        refl
    ; selectedPairBridgeFeedsContinuumLawSurfaces =
        true
    ; selectedPairBridgeFeedsContinuumLawSurfacesIsTrue =
        refl
    ; arbitraryFiniteRChristoffelPromotion =
        false
    ; arbitraryFiniteRChristoffelPromotionIsFalse =
        refl
    ; arbitraryFiniteRLeviCivitaPromotion =
        false
    ; arbitraryFiniteRLeviCivitaPromotionIsFalse =
        refl
    ; finiteRImpossibleHalvingChanged =
        false
    ; finiteRImpossibleHalvingChangedIsFalse =
        refl
    ; arbitraryFiniteRPromotionBlockerName =
        "arbitraryFiniteRChristoffelOrLeviCivitaPromotionIsFalse"
    ; arbitraryFiniteRPromotionBlockerNameIsExplicit =
        refl
    ; bridgeBoundary =
        "Selected-pair QQ bridge: selectedBase0 and selectedBase1 radial/radial/radial doubled Christoffel slots undouble to qqHalf"
        ∷ "The bridge path is twoGammaTable -> qqUndoubledChristoffel -> suppliedUndoubledChristoffelTable, with qqMul qq2 returning suppliedTwoGammaTable"
        ∷ "Continuum law surfaces consume this selected-pair rational adapter as evidence of the chosen Christoffel route, not as arbitrary finite-r halving"
        ∷ "Arbitrary finite-r Christoffel promotion is explicitly false"
        ∷ "Arbitrary finite-r Levi-Civita promotion is explicitly false"
        ∷ "The finite-r impossible halving table is not changed or bypassed"
        ∷ []
    }

canonicalGRSelectedQQChristoffelSelectedPairBridgeFeedsContinuum :
  GRSelectedQQChristoffelSelectedPairContinuumBridge.selectedPairBridgeFeedsContinuumLawSurfaces
    canonicalGRSelectedQQChristoffelSelectedPairContinuumBridge
  ≡
  true
canonicalGRSelectedQQChristoffelSelectedPairBridgeFeedsContinuum =
  refl

canonicalGRSelectedQQChristoffelSelectedPairBridgeFiniteRChristoffelPromotionFalse :
  GRSelectedQQChristoffelSelectedPairContinuumBridge.arbitraryFiniteRChristoffelPromotion
    canonicalGRSelectedQQChristoffelSelectedPairContinuumBridge
  ≡
  false
canonicalGRSelectedQQChristoffelSelectedPairBridgeFiniteRChristoffelPromotionFalse =
  refl

canonicalGRSelectedQQChristoffelSelectedPairBridgeFiniteRLeviCivitaPromotionFalse :
  GRSelectedQQChristoffelSelectedPairContinuumBridge.arbitraryFiniteRLeviCivitaPromotion
    canonicalGRSelectedQQChristoffelSelectedPairContinuumBridge
  ≡
  false
canonicalGRSelectedQQChristoffelSelectedPairBridgeFiniteRLeviCivitaPromotionFalse =
  refl

canonicalGRSelectedQQChristoffelSelectedPairBridgeKeepsFiniteRHalvingUnchanged :
  GRSelectedQQChristoffelSelectedPairContinuumBridge.finiteRImpossibleHalvingChanged
    canonicalGRSelectedQQChristoffelSelectedPairContinuumBridge
  ≡
  false
canonicalGRSelectedQQChristoffelSelectedPairBridgeKeepsFiniteRHalvingUnchanged =
  refl

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

    qqSelectedPairContinuumBridge :
      GRSelectedQQChristoffelSelectedPairContinuumBridge

    qqSelectedPairContinuumBridgeUsed :
      GRSelectedQQChristoffelSelectedPairContinuumBridge.selectedPairBridgeFeedsContinuumLawSurfaces
        qqSelectedPairContinuumBridge
      ≡
      true

    arbitraryFiniteRChristoffelPromotionFalse :
      GRSelectedQQChristoffelSelectedPairContinuumBridge.arbitraryFiniteRChristoffelPromotion
        qqSelectedPairContinuumBridge
      ≡
      false

    arbitraryFiniteRLeviCivitaPromotionFalse :
      GRSelectedQQChristoffelSelectedPairContinuumBridge.arbitraryFiniteRLeviCivitaPromotion
        qqSelectedPairContinuumBridge
      ≡
      false

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
    ; qqSelectedPairContinuumBridge =
        canonicalGRSelectedQQChristoffelSelectedPairContinuumBridge
    ; qqSelectedPairContinuumBridgeUsed =
        canonicalGRSelectedQQChristoffelSelectedPairBridgeFeedsContinuum
    ; arbitraryFiniteRChristoffelPromotionFalse =
        canonicalGRSelectedQQChristoffelSelectedPairBridgeFiniteRChristoffelPromotionFalse
    ; arbitraryFiniteRLeviCivitaPromotionFalse =
        canonicalGRSelectedQQChristoffelSelectedPairBridgeFiniteRLeviCivitaPromotionFalse
    ; firstMissingNonFlatLaw =
        missingSelectedChristoffelFromMetricLaw
    ; noPromotionBoundary =
        "The selected dependency, metric table, inverse table, finite contraction, coordinate derivative, Christoffel slot, Ricci contraction slot, and trace slot are all typed"
        ∷ "Metric symmetry, inverse left/right contraction, finite contraction shape, and selected trace=r2 are table laws over the two selected coordinate indices"
        ∷ "The Christoffel-from-metric slot is wired to the imported doubled-Christoffel / Levi-Civita receipt from GRNonFlatScalarAlgebraSurface"
        ∷ "The doubled-Christoffel / Levi-Civita blocker witness is available from GRNonFlatScalarAlgebraSurface.canonicalGRLatestWaveDoubledChristoffelMetricCompatibilityReceipt"
        ∷ "The QQ selected-pair continuum bridge records the undoubled qqHalf route for both selected radial/radial/radial slots"
        ∷ "The QQ bridge explicitly keeps arbitrary finite-r Christoffel and Levi-Civita promotion false"
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

canonicalGRSelectedNonFlatMetricSurfaceUsesQQSelectedPairBridge :
  GRSelectedNonFlatMetricInstanceSurface.qqSelectedPairContinuumBridgeUsed
    canonicalGRSelectedNonFlatMetricInstanceSurface
  ≡
  refl
canonicalGRSelectedNonFlatMetricSurfaceUsesQQSelectedPairBridge =
  refl

canonicalGRSelectedNonFlatMetricSurfaceFiniteRChristoffelPromotionFalse :
  GRSelectedNonFlatMetricInstanceSurface.arbitraryFiniteRChristoffelPromotionFalse
    canonicalGRSelectedNonFlatMetricInstanceSurface
  ≡
  refl
canonicalGRSelectedNonFlatMetricSurfaceFiniteRChristoffelPromotionFalse =
  refl

canonicalGRSelectedNonFlatMetricSurfaceFiniteRLeviCivitaPromotionFalse :
  GRSelectedNonFlatMetricInstanceSurface.arbitraryFiniteRLeviCivitaPromotionFalse
    canonicalGRSelectedNonFlatMetricInstanceSurface
  ≡
  refl
canonicalGRSelectedNonFlatMetricSurfaceFiniteRLeviCivitaPromotionFalse =
  refl
