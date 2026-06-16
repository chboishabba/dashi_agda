module DASHI.Physics.Closure.GRCoord4TensorCore where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false)
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

coord4Case :
  {A : Set} →
  A →
  A →
  A →
  A →
  Coord4 →
  A
coord4Case zero one two three coord with coord
... | coord0 = zero
... | coord1 = one
... | coord2 = two
... | coord3 = three

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

------------------------------------------------------------------------
-- Concrete diagonal tensor accessors for the four-coordinate core.

diagonalMetricComponent :
  {Scalar : Set} →
  Coord4 →
  DiagonalMetric Scalar →
  Scalar
diagonalMetricComponent coord (diagTensor2 tt rr th ph) with coord
... | coord0 = tt
... | coord1 = rr
... | coord2 = th
... | coord3 = ph

diagonalMetricTT :
  {Scalar : Set} →
  DiagonalMetric Scalar →
  Scalar
diagonalMetricTT = diagonalMetricComponent coord0

diagonalMetricRR :
  {Scalar : Set} →
  DiagonalMetric Scalar →
  Scalar
diagonalMetricRR = diagonalMetricComponent coord1

diagonalMetricThetaTheta :
  {Scalar : Set} →
  DiagonalMetric Scalar →
  Scalar
diagonalMetricThetaTheta = diagonalMetricComponent coord2

diagonalMetricPhiPhi :
  {Scalar : Set} →
  DiagonalMetric Scalar →
  Scalar
diagonalMetricPhiPhi = diagonalMetricComponent coord3

diagonalInverseMetricComponent :
  {Scalar : Set} →
  Coord4 →
  DiagonalInvMetric Scalar →
  Scalar
diagonalInverseMetricComponent coord (diagTensor2 tt rr th ph) with coord
... | coord0 = tt
... | coord1 = rr
... | coord2 = th
... | coord3 = ph

diagonalInverseMetricTT :
  {Scalar : Set} →
  DiagonalInvMetric Scalar →
  Scalar
diagonalInverseMetricTT = diagonalInverseMetricComponent coord0

diagonalInverseMetricRR :
  {Scalar : Set} →
  DiagonalInvMetric Scalar →
  Scalar
diagonalInverseMetricRR = diagonalInverseMetricComponent coord1

diagonalInverseMetricThetaTheta :
  {Scalar : Set} →
  DiagonalInvMetric Scalar →
  Scalar
diagonalInverseMetricThetaTheta = diagonalInverseMetricComponent coord2

diagonalInverseMetricPhiPhi :
  {Scalar : Set} →
  DiagonalInvMetric Scalar →
  Scalar
diagonalInverseMetricPhiPhi = diagonalInverseMetricComponent coord3

schwarzschildMetricDiagonalTable :
  SchwarzschildDiagonalMetricSurface →
  DiagonalMetric ℚ
schwarzschildMetricDiagonalTable surface =
  diagTensor2
    (DiagonalCoord4Component.value (SchwarzschildDiagonalMetricSurface.ttComponent surface))
    (DiagonalCoord4Component.value (SchwarzschildDiagonalMetricSurface.rrComponent surface))
    (DiagonalCoord4Component.value (SchwarzschildDiagonalMetricSurface.thetaThetaComponent surface))
    (DiagonalCoord4Component.value (SchwarzschildDiagonalMetricSurface.phiPhiComponent surface))

schwarzschildInverseMetricDiagonalTable :
  SchwarzschildInverseDiagonalMetricSurface →
  DiagonalInvMetric ℚ
schwarzschildInverseMetricDiagonalTable surface =
  diagTensor2
    (DiagonalCoord4Component.value (SchwarzschildInverseDiagonalMetricSurface.ttComponent surface))
    (DiagonalCoord4Component.value (SchwarzschildInverseDiagonalMetricSurface.rrComponent surface))
    (DiagonalCoord4Component.value (SchwarzschildInverseDiagonalMetricSurface.thetaThetaComponent surface))
    (DiagonalCoord4Component.value (SchwarzschildInverseDiagonalMetricSurface.phiPhiComponent surface))

schwarzschildMetricAt :
  SchwarzschildDiagonalMetricSurface →
  Coord4 →
  ℚ
schwarzschildMetricAt surface coord =
  diagonalMetricComponent coord
    (schwarzschildMetricDiagonalTable surface)

diagonalMetricAt :
  SchwarzschildDiagonalMetricSurface →
  Coord4 →
  ℚ
diagonalMetricAt = schwarzschildMetricAt

schwarzschildInverseMetricAt :
  SchwarzschildInverseDiagonalMetricSurface →
  Coord4 →
  ℚ
schwarzschildInverseMetricAt surface coord =
  diagonalInverseMetricComponent coord
    (schwarzschildInverseMetricDiagonalTable surface)

diagonalInvMetricAt :
  SchwarzschildInverseDiagonalMetricSurface →
  Coord4 →
  ℚ
diagonalInvMetricAt = schwarzschildInverseMetricAt

record SchwarzschildPartialGFormulaSurface : Set where
  constructor schwarzschildPartialGFormulaSurface
  field
    ttAtTime :
      ℚ

    ttAtRadial :
      ℚ

    ttAtTheta :
      ℚ

    ttAtPhi :
      ℚ

    rrAtTime :
      ℚ

    rrAtRadial :
      ℚ

    rrAtTheta :
      ℚ

    rrAtPhi :
      ℚ

    thetaThetaAtTime :
      ℚ

    thetaThetaAtRadial :
      ℚ

    thetaThetaAtTheta :
      ℚ

    thetaThetaAtPhi :
      ℚ

    phiPhiAtTime :
      ℚ

    phiPhiAtRadial :
      ℚ

    phiPhiAtTheta :
      ℚ

    phiPhiAtPhi :
      ℚ

    partialGBoundary :
      List String

schwarzschildPartialGFormula :
  SchwarzschildPartialGFormulaSurface →
  Coord4 →
  Coord4 →
  ℚ
schwarzschildPartialGFormula formulas derivative component with derivative | component
... | coord0 | coord0 = SchwarzschildPartialGFormulaSurface.ttAtTime formulas
... | coord1 | coord0 = SchwarzschildPartialGFormulaSurface.ttAtRadial formulas
... | coord2 | coord0 = SchwarzschildPartialGFormulaSurface.ttAtTheta formulas
... | coord3 | coord0 = SchwarzschildPartialGFormulaSurface.ttAtPhi formulas
... | coord0 | coord1 = SchwarzschildPartialGFormulaSurface.rrAtTime formulas
... | coord1 | coord1 = SchwarzschildPartialGFormulaSurface.rrAtRadial formulas
... | coord2 | coord1 = SchwarzschildPartialGFormulaSurface.rrAtTheta formulas
... | coord3 | coord1 = SchwarzschildPartialGFormulaSurface.rrAtPhi formulas
... | coord0 | coord2 = SchwarzschildPartialGFormulaSurface.thetaThetaAtTime formulas
... | coord1 | coord2 = SchwarzschildPartialGFormulaSurface.thetaThetaAtRadial formulas
... | coord2 | coord2 = SchwarzschildPartialGFormulaSurface.thetaThetaAtTheta formulas
... | coord3 | coord2 = SchwarzschildPartialGFormulaSurface.thetaThetaAtPhi formulas
... | coord0 | coord3 = SchwarzschildPartialGFormulaSurface.phiPhiAtTime formulas
... | coord1 | coord3 = SchwarzschildPartialGFormulaSurface.phiPhiAtRadial formulas
... | coord2 | coord3 = SchwarzschildPartialGFormulaSurface.phiPhiAtTheta formulas
... | coord3 | coord3 = SchwarzschildPartialGFormulaSurface.phiPhiAtPhi formulas

schwarzschildPartialGTT :
  SchwarzschildPartialGFormulaSurface →
  Coord4 →
  ℚ
schwarzschildPartialGTT formulas derivative =
  schwarzschildPartialGFormula formulas derivative coord0

schwarzschildPartialGRR :
  SchwarzschildPartialGFormulaSurface →
  Coord4 →
  ℚ
schwarzschildPartialGRR formulas derivative =
  schwarzschildPartialGFormula formulas derivative coord1

schwarzschildPartialGThetaTheta :
  SchwarzschildPartialGFormulaSurface →
  Coord4 →
  ℚ
schwarzschildPartialGThetaTheta formulas derivative =
  schwarzschildPartialGFormula formulas derivative coord2

schwarzschildPartialGPhiPhi :
  SchwarzschildPartialGFormulaSurface →
  Coord4 →
  ℚ
schwarzschildPartialGPhiPhi formulas derivative =
  schwarzschildPartialGFormula formulas derivative coord3

partialGAt :
  SchwarzschildPartialGFormulaSurface →
  Coord4 →
  Coord4 →
  ℚ
partialGAt = schwarzschildPartialGFormula

record SchwarzschildChristoffelFormulaSurface : Set where
  constructor schwarzschildChristoffelFormulaSurface
  field
    ttrFormula :
      SchwarzschildChristoffelSlotFormula

    rttFormula :
      SchwarzschildChristoffelSlotFormula

    rrrFormula :
      SchwarzschildChristoffelSlotFormula

    rThetaThetaFormula :
      SchwarzschildChristoffelSlotFormula

    rPhiPhiFormula :
      SchwarzschildChristoffelSlotFormula

    thetaRThetaFormula :
      SchwarzschildChristoffelSlotFormula

    phiRPhiFormula :
      SchwarzschildChristoffelSlotFormula

    formulaBoundary :
      List String

SchwarzschildMetric : Set
SchwarzschildMetric = SchwarzschildDiagonalMetricSurface

SchwarzschildInvMetric : Set
SchwarzschildInvMetric = SchwarzschildInverseDiagonalMetricSurface

SchwarzschildPartialG : Set
SchwarzschildPartialG = SchwarzschildPartialGFormulaSurface

SchwarzschildChristoffelFormulaLawShape : Set
SchwarzschildChristoffelFormulaLawShape = SchwarzschildChristoffelFormulaSurface

schwarzschildChristoffelTtrToken :
  SchwarzschildChristoffelSlot
schwarzschildChristoffelTtrToken = gammaTtr

schwarzschildChristoffelRttToken :
  SchwarzschildChristoffelSlot
schwarzschildChristoffelRttToken = gammaRtt

schwarzschildChristoffelRrrToken :
  SchwarzschildChristoffelSlot
schwarzschildChristoffelRrrToken = gammaRrr

schwarzschildChristoffelRThetaThetaToken :
  SchwarzschildChristoffelSlot
schwarzschildChristoffelRThetaThetaToken = gammaRThetaTheta

schwarzschildChristoffelRPhiPhiToken :
  SchwarzschildChristoffelSlot
schwarzschildChristoffelRPhiPhiToken = gammaRPhiPhi

schwarzschildChristoffelThetaRThetaToken :
  SchwarzschildChristoffelSlot
schwarzschildChristoffelThetaRThetaToken = gammaThetaRTheta

schwarzschildChristoffelPhiRPhiToken :
  SchwarzschildChristoffelSlot
schwarzschildChristoffelPhiRPhiToken = gammaPhiRPhi

schwarzschildChristoffelFormulaSurfaceFromPackage :
  SchwarzschildChristoffelSevenSlotPackage →
  SchwarzschildChristoffelFormulaSurface
schwarzschildChristoffelFormulaSurfaceFromPackage package =
  schwarzschildChristoffelFormulaSurface
    (SchwarzschildChristoffelSevenSlotPackage.slotTtr package)
    (SchwarzschildChristoffelSevenSlotPackage.slotRtt package)
    (SchwarzschildChristoffelSevenSlotPackage.slotRrr package)
    (SchwarzschildChristoffelSevenSlotPackage.slotRThetaTheta package)
    (SchwarzschildChristoffelSevenSlotPackage.slotRPhiPhi package)
    (SchwarzschildChristoffelSevenSlotPackage.slotThetaRTheta package)
    (SchwarzschildChristoffelSevenSlotPackage.slotPhiRPhi package)
    ( "slotTtr" ∷ "slotRtt" ∷ "slotRrr" ∷
      "slotRThetaTheta" ∷ "slotRPhiPhi" ∷
      "slotThetaRTheta" ∷ "slotPhiRPhi" ∷ [])

schwarzschildChristoffelFormulaPackageFromSurface :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelSevenSlotPackage
schwarzschildChristoffelFormulaPackageFromSurface surface =
  schwarzschildChristoffelSevenSlotPackage
    (SchwarzschildChristoffelFormulaSurface.ttrFormula surface)
    (SchwarzschildChristoffelFormulaSurface.rttFormula surface)
    (SchwarzschildChristoffelFormulaSurface.rrrFormula surface)
    (SchwarzschildChristoffelFormulaSurface.rThetaThetaFormula surface)
    (SchwarzschildChristoffelFormulaSurface.rPhiPhiFormula surface)
    (SchwarzschildChristoffelFormulaSurface.thetaRThetaFormula surface)
    (SchwarzschildChristoffelFormulaSurface.phiRPhiFormula surface)
    ( "slotTtr" ∷ "slotRtt" ∷ "slotRrr" ∷
      "slotRThetaTheta" ∷ "slotRPhiPhi" ∷
      "slotThetaRTheta" ∷ "slotPhiRPhi" ∷ [])

christoffelFormulaDiagonalShape :
  SchwarzschildChristoffelFormulaLawShape →
  SchwarzschildChristoffelSevenSlotPackage
christoffelFormulaDiagonalShape = schwarzschildChristoffelFormulaPackageFromSurface

record SchwarzschildDiagonalFormulaCarrierSurface : Set where
  constructor schwarzschildDiagonalFormulaCarrierSurface
  field
    metric :
      SchwarzschildDiagonalMetricSurface

    inverseMetric :
      SchwarzschildInverseDiagonalMetricSurface

    partialG :
      SchwarzschildPartialGFormulaSurface

    christoffelFormula :
      SchwarzschildChristoffelFormulaSurface

    formulaBoundary :
      List String

-- Concrete fail-closed law-shape rows for the diagonal Schwarzschild tensor formulas.
-- These rows intentionally record reusable shape intent only; they are not promoted
-- into continuum-level theorems.
data ChristoffelFormulaLaw : Set where
  diagonalOneTermReduction :
    ChristoffelFormulaLaw

  sevenSlotNonzeroReduction :
    ChristoffelFormulaLaw

  zeroSlot57Closure :
    ChristoffelFormulaLaw

data InverseMetricLaw : Set where
  diagonalOneTermInverseReduction :
    InverseMetricLaw

data MetricCompatibilityLaw : Set where
  diagonalMetricCompatibilityReduction :
    MetricCompatibilityLaw

record SchwarzschildChristoffelFormulaLawSurface : Set where
  constructor schwarzschildChristoffelFormulaLawSurface
  field
    metricCarrier :
      SchwarzschildDiagonalFormulaCarrierSurface

    christoffelFormulaRows :
      List ChristoffelFormulaLaw

    lawNotPromoted :
      Bool

record SchwarzschildInverseMetricLawSurface : Set where
  constructor schwarzschildInverseMetricLawSurface
  field
    metricCarrier :
      SchwarzschildDiagonalFormulaCarrierSurface

    inverseMetricLawRows :
      List InverseMetricLaw

    lawNotPromoted :
      Bool

record SchwarzschildMetricCompatibilityLawSurface : Set where
  constructor schwarzschildMetricCompatibilityLawSurface
  field
    metricCarrier :
      SchwarzschildDiagonalFormulaCarrierSurface

    metricCompatibilityRows :
      List MetricCompatibilityLaw

    lawNotPromoted :
      Bool

record SchwarzschildFormulaLawSurface : Set where
  constructor schwarzschildFormulaLawSurface
  field
    metricCarrier :
      SchwarzschildDiagonalFormulaCarrierSurface

    christoffelFormulaLaw :
      SchwarzschildChristoffelFormulaLawSurface

    inverseMetricLaw :
      SchwarzschildInverseMetricLawSurface

    metricCompatibilityLaw :
      SchwarzschildMetricCompatibilityLawSurface

    lawNotPromoted :
      Bool

schwarzschildChristoffelFormulaLawSurfaceFromCarrier :
  SchwarzschildDiagonalFormulaCarrierSurface →
  SchwarzschildChristoffelFormulaLawSurface
schwarzschildChristoffelFormulaLawSurfaceFromCarrier carrier =
  schwarzschildChristoffelFormulaLawSurface
    carrier
    ( diagonalOneTermReduction
    ∷ sevenSlotNonzeroReduction
    ∷ zeroSlot57Closure
    ∷ [] )
    false

schwarzschildInverseMetricLawSurfaceFromCarrier :
  SchwarzschildDiagonalFormulaCarrierSurface →
  SchwarzschildInverseMetricLawSurface
schwarzschildInverseMetricLawSurfaceFromCarrier carrier =
  schwarzschildInverseMetricLawSurface
    carrier
    ( diagonalOneTermInverseReduction ∷ [] )
    false

schwarzschildMetricCompatibilityLawSurfaceFromCarrier :
  SchwarzschildDiagonalFormulaCarrierSurface →
  SchwarzschildMetricCompatibilityLawSurface
schwarzschildMetricCompatibilityLawSurfaceFromCarrier carrier =
  schwarzschildMetricCompatibilityLawSurface
    carrier
    ( diagonalMetricCompatibilityReduction ∷ [] )
    false

schwarzschildFormulaLawSurfaceFromCarrier :
  SchwarzschildDiagonalFormulaCarrierSurface →
  SchwarzschildFormulaLawSurface
schwarzschildFormulaLawSurfaceFromCarrier carrier =
  schwarzschildFormulaLawSurface
    carrier
    (schwarzschildChristoffelFormulaLawSurfaceFromCarrier carrier)
    (schwarzschildInverseMetricLawSurfaceFromCarrier carrier)
    (schwarzschildMetricCompatibilityLawSurfaceFromCarrier carrier)
    false
