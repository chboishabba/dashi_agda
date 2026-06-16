module DASHI.Physics.Closure.GRCoord4TensorCore where

open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import DASHI.Core.Q using (ℚ)

------------------------------------------------------------------------
-- Minimal four-coordinate tensor API for GR closure work.
--
-- This module supplies only the component carrier shapes that the current
-- continuum/GR obstruction receipts identify as absent: a concrete Coord4
-- index, metric/inverse metric component families, partial-derivative shape,
-- Christoffel components, and Ricci components.  It intentionally contains no
-- Christoffel formula law, inverse law, Ricci contraction theorem, convergence
-- estimate, Einstein equation, Schwarzschild authority, or GR promotion.
--
-- The diagonal helpers below stay carrier-only and are meant for future
-- Schwarzschild-friendly bookkeeping on the four independent slots only.

data Coord4 : Set where
  coord0 : Coord4
  coord1 : Coord4
  coord2 : Coord4
  coord3 : Coord4

timeCoord radialCoord thetaCoord phiCoord : Coord4
timeCoord = coord0
radialCoord = coord1
thetaCoord = coord2
phiCoord = coord3

record Coord4Slot : Set where
  constructor coord4Slot
  field
    upper :
      Coord4

    lower1 :
      Coord4

    lower2 :
      Coord4

record ScalarRadiusKey : Set where
  constructor scalarRadiusKey
  field
    scalar :
      ℚ

    radius :
      ℚ

record DiagonalCoord4Component : Set where
  constructor diagonalCoord4Component
  field
    coordinate :
      Coord4

    value :
      ℚ

schwarzschildDiagonalComponent :
  Coord4 →
  ℚ →
  DiagonalCoord4Component
schwarzschildDiagonalComponent coordinate value =
  diagonalCoord4Component coordinate value

schwarzschildSlot :
  Coord4 →
  Coord4 →
  Coord4 →
  Coord4Slot
schwarzschildSlot upper lower1 lower2 =
  coord4Slot upper lower1 lower2

Tensor0 :
  Set →
  Set
Tensor0 Scalar =
  Scalar

Tensor1 :
  Set →
  Set
Tensor1 Scalar =
  Coord4 →
  Scalar

Tensor2 :
  Set →
  Set
Tensor2 Scalar =
  Coord4 →
  Coord4 →
  Scalar

Tensor3 :
  Set →
  Set
Tensor3 Scalar =
  Coord4 →
  Coord4 →
  Coord4 →
  Scalar

Tensor4 :
  Set →
  Set
Tensor4 Scalar =
  Coord4 →
  Coord4 →
  Coord4 →
  Coord4 →
  Scalar

record DiagonalTensor2 (Scalar : Set) : Set where
  constructor diagTensor2
  field
    component00 :
      Scalar
    component11 :
      Scalar
    component22 :
      Scalar
    component33 :
      Scalar

Metric :
  Set →
  Set
Metric =
  Tensor2

MetricT :
  Set →
  Set
MetricT = Metric

InverseMetric :
  Set →
  Set
InverseMetric =
  Tensor2

InvMetric :
  Set →
  Set
InvMetric = InverseMetric

Partial :
  Set →
  Set
Partial Tensor =
  Coord4 →
  Tensor →
  Tensor

MetricPartial :
  Set →
  Set
MetricPartial Scalar =
  Partial (Metric Scalar)

PartialG :
  Set →
  Set
PartialG = MetricPartial

Christoffel :
  Set →
  Set
Christoffel =
  Tensor3

ChristoffelT :
  Set →
  Set
ChristoffelT = Christoffel

Riemann :
  Set →
  Set
Riemann =
  Tensor4

Ricci :
  Set →
  Set
Ricci =
  Tensor2

RicciT :
  Set →
  Set
RicciT = Ricci

DiagonalMetric :
  Set →
  Set
DiagonalMetric = DiagonalTensor2

DiagonalInvMetric :
  Set →
  Set
DiagonalInvMetric = DiagonalTensor2

DiagonalRicciT :
  Set →
  Set
DiagonalRicciT = DiagonalTensor2

record GRCoord4TensorPackage (Scalar : Set) : Set₁ where
  field
    metric :
      Metric Scalar

    inverseMetric :
      InverseMetric Scalar

    partial :
      MetricPartial Scalar

    christoffel :
      Christoffel Scalar

    ricci :
      Ricci Scalar

record GRCoord4TensorFormulaSurface (Scalar : Set) : Set₁ where
  field
    metric :
      Metric Scalar

    inverseMetric :
      InverseMetric Scalar

    metricPartial :
      MetricPartial Scalar

    christoffel :
      Christoffel Scalar

    ricci :
      Ricci Scalar

    ChristoffelFormula :
      Set

    RicciContraction :
      Set

    InverseMetricLaw :
      Set

    MetricCompatibilityLaw :
      Set

record DiagonalGRCoord4TensorPackage (Scalar : Set) : Set₁ where
  field
    metric :
      DiagonalMetric Scalar

    inverseMetric :
      DiagonalInvMetric Scalar

    partialG :
      PartialG Scalar

    christoffelT :
      ChristoffelT Scalar

    ricciT :
      RicciT Scalar

record SchwarzschildDiagonalMetricSurface : Set where
  constructor schwarzschildDiagonalMetricSurface
  field
    key :
      ScalarRadiusKey

    lapse :
      ℚ

    radialFactor :
      ℚ

    tangentialFactor :
      ℚ

    ttComponent :
      DiagonalCoord4Component

    rrComponent :
      DiagonalCoord4Component

    thetaThetaComponent :
      DiagonalCoord4Component

    phiPhiComponent :
      DiagonalCoord4Component

    surfaceBoundary :
      List String

schwarzschildMetricTT :
  ℚ →
  DiagonalCoord4Component
schwarzschildMetricTT lapse =
  schwarzschildDiagonalComponent timeCoord lapse

schwarzschildMetricRR :
  ℚ →
  DiagonalCoord4Component
schwarzschildMetricRR radialFactor =
  schwarzschildDiagonalComponent radialCoord radialFactor

schwarzschildMetricThetaTheta :
  ℚ →
  DiagonalCoord4Component
schwarzschildMetricThetaTheta tangentialFactor =
  schwarzschildDiagonalComponent thetaCoord tangentialFactor

schwarzschildMetricPhiPhi :
  ℚ →
  DiagonalCoord4Component
schwarzschildMetricPhiPhi tangentialFactor =
  schwarzschildDiagonalComponent phiCoord tangentialFactor

record SchwarzschildInverseDiagonalMetricSurface : Set where
  constructor schwarzschildInverseDiagonalMetricSurface
  field
    key :
      ScalarRadiusKey

    inverseLapse :
      ℚ

    inverseRadialFactor :
      ℚ

    inverseTangentialFactor :
      ℚ

    ttComponent :
      DiagonalCoord4Component

    rrComponent :
      DiagonalCoord4Component

    thetaThetaComponent :
      DiagonalCoord4Component

    phiPhiComponent :
      DiagonalCoord4Component

    surfaceBoundary :
      List String

schwarzschildInverseMetricTT :
  ℚ →
  DiagonalCoord4Component
schwarzschildInverseMetricTT inverseLapse =
  schwarzschildDiagonalComponent timeCoord inverseLapse

schwarzschildInverseMetricRR :
  ℚ →
  DiagonalCoord4Component
schwarzschildInverseMetricRR inverseRadialFactor =
  schwarzschildDiagonalComponent radialCoord inverseRadialFactor

schwarzschildInverseMetricThetaTheta :
  ℚ →
  DiagonalCoord4Component
schwarzschildInverseMetricThetaTheta inverseTangentialFactor =
  schwarzschildDiagonalComponent thetaCoord inverseTangentialFactor

schwarzschildInverseMetricPhiPhi :
  ℚ →
  DiagonalCoord4Component
schwarzschildInverseMetricPhiPhi inverseTangentialFactor =
  schwarzschildDiagonalComponent phiCoord inverseTangentialFactor

data SchwarzschildChristoffelSlot : Set where
  gammaTtr :
    SchwarzschildChristoffelSlot

  gammaRtt :
    SchwarzschildChristoffelSlot

  gammaRrr :
    SchwarzschildChristoffelSlot

  gammaRThetaTheta :
    SchwarzschildChristoffelSlot

  gammaRPhiPhi :
    SchwarzschildChristoffelSlot

  gammaThetaRTheta :
    SchwarzschildChristoffelSlot

  gammaPhiRPhi :
    SchwarzschildChristoffelSlot

record SchwarzschildChristoffelSlotFormula : Set where
  constructor schwarzschildChristoffelSlotFormula
  field
    slot :
      SchwarzschildChristoffelSlot

    coordinates :
      Coord4Slot

    value :
      ℚ

schwarzschildChristoffelSlotFormulaAt :
  SchwarzschildChristoffelSlot →
  Coord4 →
  Coord4 →
  Coord4 →
  ℚ →
  SchwarzschildChristoffelSlotFormula
schwarzschildChristoffelSlotFormulaAt slot upper lower1 lower2 value =
  schwarzschildChristoffelSlotFormula
    slot
    (schwarzschildSlot upper lower1 lower2)
    value

schwarzschildGammaTtrCoordinates :
  Coord4Slot
schwarzschildGammaTtrCoordinates =
  schwarzschildSlot timeCoord timeCoord radialCoord

schwarzschildGammaRttCoordinates :
  Coord4Slot
schwarzschildGammaRttCoordinates =
  schwarzschildSlot radialCoord timeCoord timeCoord

schwarzschildGammaRrrCoordinates :
  Coord4Slot
schwarzschildGammaRrrCoordinates =
  schwarzschildSlot radialCoord radialCoord radialCoord

schwarzschildGammaRThetaThetaCoordinates :
  Coord4Slot
schwarzschildGammaRThetaThetaCoordinates =
  schwarzschildSlot radialCoord thetaCoord thetaCoord

schwarzschildGammaRPhiPhiCoordinates :
  Coord4Slot
schwarzschildGammaRPhiPhiCoordinates =
  schwarzschildSlot radialCoord phiCoord phiCoord

schwarzschildGammaThetaRThetaCoordinates :
  Coord4Slot
schwarzschildGammaThetaRThetaCoordinates =
  schwarzschildSlot thetaCoord radialCoord thetaCoord

schwarzschildGammaPhiRPhiCoordinates :
  Coord4Slot
schwarzschildGammaPhiRPhiCoordinates =
  schwarzschildSlot phiCoord radialCoord phiCoord

schwarzschildGammaTtrFormula :
  ℚ →
  SchwarzschildChristoffelSlotFormula
schwarzschildGammaTtrFormula value =
  schwarzschildChristoffelSlotFormula
    gammaTtr
    schwarzschildGammaTtrCoordinates
    value

schwarzschildGammaRttFormula :
  ℚ →
  SchwarzschildChristoffelSlotFormula
schwarzschildGammaRttFormula value =
  schwarzschildChristoffelSlotFormula
    gammaRtt
    schwarzschildGammaRttCoordinates
    value

schwarzschildGammaRrrFormula :
  ℚ →
  SchwarzschildChristoffelSlotFormula
schwarzschildGammaRrrFormula value =
  schwarzschildChristoffelSlotFormula
    gammaRrr
    schwarzschildGammaRrrCoordinates
    value

schwarzschildGammaRThetaThetaFormula :
  ℚ →
  SchwarzschildChristoffelSlotFormula
schwarzschildGammaRThetaThetaFormula value =
  schwarzschildChristoffelSlotFormula
    gammaRThetaTheta
    schwarzschildGammaRThetaThetaCoordinates
    value

schwarzschildGammaRPhiPhiFormula :
  ℚ →
  SchwarzschildChristoffelSlotFormula
schwarzschildGammaRPhiPhiFormula value =
  schwarzschildChristoffelSlotFormula
    gammaRPhiPhi
    schwarzschildGammaRPhiPhiCoordinates
    value

schwarzschildGammaThetaRThetaFormula :
  ℚ →
  SchwarzschildChristoffelSlotFormula
schwarzschildGammaThetaRThetaFormula value =
  schwarzschildChristoffelSlotFormula
    gammaThetaRTheta
    schwarzschildGammaThetaRThetaCoordinates
    value

schwarzschildGammaPhiRPhiFormula :
  ℚ →
  SchwarzschildChristoffelSlotFormula
schwarzschildGammaPhiRPhiFormula value =
  schwarzschildChristoffelSlotFormula
    gammaPhiRPhi
    schwarzschildGammaPhiRPhiCoordinates
    value

record SchwarzschildChristoffelSevenSlotPackage : Set where
  constructor schwarzschildChristoffelSevenSlotPackage
  field
    slotTtr :
      SchwarzschildChristoffelSlotFormula

    slotRtt :
      SchwarzschildChristoffelSlotFormula

    slotRrr :
      SchwarzschildChristoffelSlotFormula

    slotRThetaTheta :
      SchwarzschildChristoffelSlotFormula

    slotRPhiPhi :
      SchwarzschildChristoffelSlotFormula

    slotThetaRTheta :
      SchwarzschildChristoffelSlotFormula

    slotPhiRPhi :
      SchwarzschildChristoffelSlotFormula

    packageBoundary :
      List String

record SchwarzschildCoord4TensorSurface : Set where
  constructor schwarzschildCoord4TensorSurface
  field
    metric :
      SchwarzschildDiagonalMetricSurface

    inverseMetric :
      SchwarzschildInverseDiagonalMetricSurface

    christoffel :
      SchwarzschildChristoffelSevenSlotPackage

    surfaceBoundary :
      List String
