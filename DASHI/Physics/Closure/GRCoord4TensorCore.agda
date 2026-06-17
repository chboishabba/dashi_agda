module DASHI.Physics.Closure.GRCoord4TensorCore where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; _∷_; []; map; _++_)
open import DASHI.Core.Q using (ℚ)

------------------------------------------------------------------------
-- Minimal four-coordinate tensor API for GR closure work.
--
-- This module supplies the Coord4 index and tensor carriers used by the GR
-- obstruction receipts, together with explicit Schwarzschild diagonal
-- bookkeeping rows for formula-law, inverse-metric, and metric-compatibility
-- surfaces.
--
-- The diagonal helpers below provide typed surface rows and 64-slot
-- classification ledgers while remaining fail-closed and non-promotional.

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

schwarzschildSlotUpper :
  Coord4Slot →
  Coord4
schwarzschildSlotUpper (coord4Slot upper lower1 lower2) = upper

schwarzschildSlotLower1 :
  Coord4Slot →
  Coord4
schwarzschildSlotLower1 (coord4Slot upper lower1 lower2) = lower1

schwarzschildSlotLower2 :
  Coord4Slot →
  Coord4
schwarzschildSlotLower2 (coord4Slot upper lower1 lower2) = lower2

schwarzschildSlotCoordinates :
  Coord4Slot →
  List Coord4
schwarzschildSlotCoordinates slot =
  schwarzschildSlotUpper slot ∷
  schwarzschildSlotLower1 slot ∷
  schwarzschildSlotLower2 slot ∷ []

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

------------------------------------------------------------------------
-- Explicit slot families and full 64-slot surface coverage for Schwarzschild
-- diagonal Christoffel shape.

schwarzschildSevenNonzeroSlots :
  List SchwarzschildChristoffelSlot
schwarzschildSevenNonzeroSlots =
  gammaTtr
    ∷ gammaRtt
    ∷ gammaRrr
    ∷ gammaRThetaTheta
    ∷ gammaRPhiPhi
    ∷ gammaThetaRTheta
    ∷ gammaPhiRPhi
    ∷ []

schwarzschildSlotAxes :
  List Coord4
schwarzschildSlotAxes =
  coord0 ∷ coord1 ∷ coord2 ∷ coord3 ∷ []

schwarzschildSlotsForLower1 :
  Coord4 →
  Coord4 →
  List Coord4Slot
schwarzschildSlotsForLower1 upper lower1 =
  map (λ lower2 → schwarzschildSlot upper lower1 lower2) schwarzschildSlotAxes

schwarzschildSlotsForUpper :
  Coord4 →
  List Coord4Slot
schwarzschildSlotsForUpper upper =
  schwarzschildSlotsForLower1 upper coord0 ++
  schwarzschildSlotsForLower1 upper coord1 ++
  schwarzschildSlotsForLower1 upper coord2 ++
  schwarzschildSlotsForLower1 upper coord3

schwarzschildAllSlots :
  List Coord4Slot
schwarzschildAllSlots =
  schwarzschildSlotsForUpper coord0 ++
  schwarzschildSlotsForUpper coord1 ++
  schwarzschildSlotsForUpper coord2 ++
  schwarzschildSlotsForUpper coord3

coord4SlotCount64 :
  Nat
coord4SlotCount64 = 64

coord4NonzeroSlotCount7 :
  Nat
coord4NonzeroSlotCount7 = 7

coord4ZeroSlotCount57 :
  Nat
coord4ZeroSlotCount57 = 57

coord4SymmetricNonzeroSlotCount10 :
  Nat
coord4SymmetricNonzeroSlotCount10 = 10

coord4SymmetricZeroSlotCount54 :
  Nat
coord4SymmetricZeroSlotCount54 = 54

data SchwarzschildSlotOccupancy : Set where
  diagonalSlot :
    SchwarzschildChristoffelSlot →
    SchwarzschildSlotOccupancy

  zeroSlot :
    SchwarzschildSlotOccupancy

record SchwarzschildChristoffelSlotClassificationRow : Set where
  constructor schwarzschildChristoffelSlotClassificationRow
  field
    slot :
      Coord4Slot

    occupancy :
      SchwarzschildSlotOccupancy

    slotBoundary :
      List String

    slotNotPromoted :
      Bool

schwarzschildSlotOccupancy :
  Coord4Slot →
  SchwarzschildSlotOccupancy
schwarzschildSlotOccupancy (coord4Slot upper lower1 lower2) with upper | lower1 | lower2
... | coord0 | coord0 | coord1 = diagonalSlot gammaTtr
... | coord1 | coord0 | coord0 = diagonalSlot gammaRtt
... | coord1 | coord1 | coord1 = diagonalSlot gammaRrr
... | coord1 | coord2 | coord2 = diagonalSlot gammaRThetaTheta
... | coord1 | coord3 | coord3 = diagonalSlot gammaRPhiPhi
... | coord2 | coord1 | coord2 = diagonalSlot gammaThetaRTheta
... | coord3 | coord1 | coord3 = diagonalSlot gammaPhiRPhi
... | _ | _ | _ = zeroSlot

schwarzschildSlotOccupancyWithLowerSymmetry :
  Coord4Slot →
  SchwarzschildSlotOccupancy
schwarzschildSlotOccupancyWithLowerSymmetry (coord4Slot upper lower1 lower2) with upper | lower1 | lower2
... | coord0 | coord0 | coord1 = diagonalSlot gammaTtr
... | coord0 | coord1 | coord0 = diagonalSlot gammaTtr
... | coord1 | coord0 | coord0 = diagonalSlot gammaRtt
... | coord1 | coord1 | coord1 = diagonalSlot gammaRrr
... | coord1 | coord2 | coord2 = diagonalSlot gammaRThetaTheta
... | coord1 | coord3 | coord3 = diagonalSlot gammaRPhiPhi
... | coord2 | coord1 | coord2 = diagonalSlot gammaThetaRTheta
... | coord2 | coord2 | coord1 = diagonalSlot gammaThetaRTheta
... | coord3 | coord1 | coord3 = diagonalSlot gammaPhiRPhi
... | coord3 | coord3 | coord1 = diagonalSlot gammaPhiRPhi
... | _ | _ | _ = zeroSlot

schwarzschildChristoffelSlotClassificationRowFromSlot :
  Coord4Slot →
  SchwarzschildChristoffelSlotClassificationRow
schwarzschildChristoffelSlotClassificationRowFromSlot slot =
  schwarzschildChristoffelSlotClassificationRow
    slot
    (schwarzschildSlotOccupancy slot)
    ( "slotClassificationRow" ∷ [] )
    false

schwarzschildChristoffelSlotClassificationRows :
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildChristoffelSlotClassificationRows =
  map schwarzschildChristoffelSlotClassificationRowFromSlot
    schwarzschildAllSlots

-- Symmetric-lower projection classifies both lower-index permutations for
-- diagonal Christoffel symmetry.  This yields the 10 symmetric nonzero triples
-- and the corresponding 54 zero triples.
schwarzschildSymmetricSlotClassificationRowFromSlot :
  Coord4Slot →
  SchwarzschildChristoffelSlotClassificationRow
schwarzschildSymmetricSlotClassificationRowFromSlot slot =
  schwarzschildChristoffelSlotClassificationRow
    slot
    (schwarzschildSlotOccupancyWithLowerSymmetry slot)
    ( "slotSymmetricClassificationRow" ∷ [] )
    false

schwarzschildSymmetricSlotClassificationRows :
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildSymmetricSlotClassificationRows =
  map schwarzschildSymmetricSlotClassificationRowFromSlot
    schwarzschildAllSlots

schwarzschildNonzeroSlotClassificationRowsFromRows :
  List SchwarzschildChristoffelSlotClassificationRow →
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildNonzeroSlotClassificationRowsFromRows [] = []
schwarzschildNonzeroSlotClassificationRowsFromRows (row ∷ rows) with
  SchwarzschildChristoffelSlotClassificationRow.occupancy row
... | diagonalSlot _ =
  row ∷ schwarzschildNonzeroSlotClassificationRowsFromRows rows
... | zeroSlot = schwarzschildNonzeroSlotClassificationRowsFromRows rows

schwarzschildZeroSlotClassificationRowsFromRows :
  List SchwarzschildChristoffelSlotClassificationRow →
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildZeroSlotClassificationRowsFromRows [] = []
schwarzschildZeroSlotClassificationRowsFromRows (row ∷ rows) with
  SchwarzschildChristoffelSlotClassificationRow.occupancy row
... | diagonalSlot _ = schwarzschildZeroSlotClassificationRowsFromRows rows
... | zeroSlot = row ∷ schwarzschildZeroSlotClassificationRowsFromRows rows

schwarzschildSymmetricNonzeroSlotClassificationRows :
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildSymmetricNonzeroSlotClassificationRows =
  schwarzschildNonzeroSlotClassificationRowsFromRows
    schwarzschildSymmetricSlotClassificationRows

schwarzschildSymmetricZeroSlotClassificationRows :
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildSymmetricZeroSlotClassificationRows =
  schwarzschildZeroSlotClassificationRowsFromRows
    schwarzschildSymmetricSlotClassificationRows

schwarzschildSymmetricNonzeroSlotCoordinates :
  List Coord4Slot
schwarzschildSymmetricNonzeroSlotCoordinates =
  map SchwarzschildChristoffelSlotClassificationRow.slot
    schwarzschildSymmetricNonzeroSlotClassificationRows

schwarzschildSymmetricZeroSlotCoordinates :
  List Coord4Slot
schwarzschildSymmetricZeroSlotCoordinates =
  map SchwarzschildChristoffelSlotClassificationRow.slot
    schwarzschildSymmetricZeroSlotClassificationRows

schwarzschildNonzeroSlotClassificationRows :
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildNonzeroSlotClassificationRows =
  schwarzschildNonzeroSlotClassificationRowsFromRows
    schwarzschildChristoffelSlotClassificationRows

schwarzschildNonzeroSlotCoordinates :
  List Coord4Slot
schwarzschildNonzeroSlotCoordinates =
  map SchwarzschildChristoffelSlotClassificationRow.slot
    schwarzschildNonzeroSlotClassificationRows

-- The dedicated zero-slot closure list in this module is a human-readable
-- companion to the machine-typed zero-row extraction below.
schwarzschildZeroSlotClosureRows :
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildZeroSlotClosureRows =
  schwarzschildZeroSlotClassificationRowsFromRows
    schwarzschildChristoffelSlotClassificationRows

schwarzschildZeroSlotClassificationRows :
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildZeroSlotClassificationRows =
  schwarzschildZeroSlotClosureRows

schwarzschildZeroSlotCoordinates :
  List Coord4Slot
schwarzschildZeroSlotCoordinates =
  map SchwarzschildChristoffelSlotClassificationRow.slot
    schwarzschildZeroSlotClassificationRows

record SchwarzschildChristoffelSlotClassificationSurface : Set where
  constructor schwarzschildChristoffelSlotClassificationSurface
  field
    allSlotRows :
      List SchwarzschildChristoffelSlotClassificationRow

    nonzeroSlotRows :
      List SchwarzschildChristoffelSlotClassificationRow

    zeroSlotRows :
      List SchwarzschildChristoffelSlotClassificationRow

    allSlotCount :
      Nat

    nonzeroSlotCount :
      Nat

    zeroSlotCount :
      Nat

    classificationBoundary :
      List String

    classificationNotPromoted :
      Bool

-- This surface is intentionally non-theorem and stays fail-closed at the row
-- level.  The zero-set is supplied by the dedicated closure list below.
canonicalSchwarzschildChristoffelSlotClassificationSurface :
  SchwarzschildChristoffelSlotClassificationSurface
canonicalSchwarzschildChristoffelSlotClassificationSurface =
  schwarzschildChristoffelSlotClassificationSurface
    schwarzschildChristoffelSlotClassificationRows
    schwarzschildNonzeroSlotClassificationRows
    schwarzschildZeroSlotClassificationRows
    coord4SlotCount64
    coord4NonzeroSlotCount7
    coord4ZeroSlotCount57
    ( "64-slot classification ledger" ∷
      "7 nonzero + 57 zero diagonal Schwarzschild Christoffel slots" ∷
      [] )
    false

schwarzschildSymmetricSlotClassificationSurface :
  SchwarzschildChristoffelSlotClassificationSurface
schwarzschildSymmetricSlotClassificationSurface =
  schwarzschildChristoffelSlotClassificationSurface
    schwarzschildSymmetricSlotClassificationRows
    schwarzschildSymmetricNonzeroSlotClassificationRows
    schwarzschildSymmetricZeroSlotClassificationRows
    coord4SlotCount64
    coord4SymmetricNonzeroSlotCount10
    coord4SymmetricZeroSlotCount54
    ( "64-slot symmetric classification ledger" ∷
      "10 nonzero + 54 zero symmetric diagonal Schwarzschild Christoffel slots" ∷
      [] )
    false

schwarzschildChristoffelSlotProjectionRowsFromClassificationSurface :
  SchwarzschildChristoffelSlotClassificationSurface →
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildChristoffelSlotProjectionRowsFromClassificationSurface surface =
  SchwarzschildChristoffelSlotClassificationSurface.allSlotRows surface

record SchwarzschildChristoffelSlotProjectionSurface : Set where
  constructor schwarzschildChristoffelSlotProjectionSurface
  field
    classificationSurface :
      SchwarzschildChristoffelSlotClassificationSurface

    projectionRows :
      List SchwarzschildChristoffelSlotClassificationRow

    projectionCount :
      Nat

    projectionBoundary :
      List String

    projectionNotPromoted :
      Bool

schwarzschildChristoffelSlotProjectionSurfaceFromClassificationSurface :
  SchwarzschildChristoffelSlotClassificationSurface →
  SchwarzschildChristoffelSlotProjectionSurface
schwarzschildChristoffelSlotProjectionSurfaceFromClassificationSurface surface =
  schwarzschildChristoffelSlotProjectionSurface
    surface
    (schwarzschildChristoffelSlotProjectionRowsFromClassificationSurface surface)
    coord4SlotCount64
    ( "slotProjectionSurface"
      ∷ "64-slot classification projection ledger"
      ∷ [] )
    false

canonicalSchwarzschildChristoffelSlotProjectionSurface :
  SchwarzschildChristoffelSlotProjectionSurface
canonicalSchwarzschildChristoffelSlotProjectionSurface =
  schwarzschildChristoffelSlotProjectionSurfaceFromClassificationSurface
    canonicalSchwarzschildChristoffelSlotClassificationSurface

record SchwarzschildChristoffelSlotProjectionReceiptSurface : Set where
  constructor schwarzschildChristoffelSlotProjectionReceiptSurface
  field
    receiptRows :
      List SchwarzschildChristoffelSlotClassificationRow

    receiptCount :
      Nat

    receiptBoundary :
      List String

    receiptNotPromoted :
      Bool

schwarzschildChristoffelSlotProjectionReceiptSurfaceFromProjectionSurface :
  SchwarzschildChristoffelSlotProjectionSurface →
  SchwarzschildChristoffelSlotProjectionReceiptSurface
schwarzschildChristoffelSlotProjectionReceiptSurfaceFromProjectionSurface surface =
  schwarzschildChristoffelSlotProjectionReceiptSurface
    (SchwarzschildChristoffelSlotProjectionSurface.projectionRows surface)
    (SchwarzschildChristoffelSlotProjectionSurface.projectionCount surface)
    (SchwarzschildChristoffelSlotProjectionSurface.projectionBoundary surface)
    (SchwarzschildChristoffelSlotProjectionSurface.projectionNotPromoted surface)

canonicalSchwarzschildChristoffelSlotProjectionReceiptSurface :
  SchwarzschildChristoffelSlotProjectionReceiptSurface
canonicalSchwarzschildChristoffelSlotProjectionReceiptSurface =
  schwarzschildChristoffelSlotProjectionReceiptSurfaceFromProjectionSurface
    canonicalSchwarzschildChristoffelSlotProjectionSurface

data SchwarzschildChristoffelSlotDecision : Set where
  slotDecisionTrue :
    SchwarzschildChristoffelSlotDecision

  slotDecisionFalse :
    SchwarzschildChristoffelSlotDecision

schwarzschildChristoffelSlotDecisionToBool :
  SchwarzschildChristoffelSlotDecision →
  Bool
schwarzschildChristoffelSlotDecisionToBool slotDecisionTrue = true
schwarzschildChristoffelSlotDecisionToBool slotDecisionFalse = false

schwarzschildChristoffelSlotDecisionFromOccupancy :
  SchwarzschildSlotOccupancy →
  SchwarzschildChristoffelSlotDecision
schwarzschildChristoffelSlotDecisionFromOccupancy (diagonalSlot _) =
  slotDecisionTrue
schwarzschildChristoffelSlotDecisionFromOccupancy zeroSlot =
  slotDecisionFalse

record SchwarzschildChristoffelSlotDecisionRow : Set where
  constructor schwarzschildChristoffelSlotDecisionRow
  field
    row :
      SchwarzschildChristoffelSlotClassificationRow

    rowDecision :
      SchwarzschildChristoffelSlotDecision

    rowDecisionBool :
      Bool

    rowBoundary :
      List String

    rowNotPromoted :
      Bool

schwarzschildChristoffelSlotDecisionRowFromRow :
  SchwarzschildChristoffelSlotClassificationRow →
  SchwarzschildChristoffelSlotDecisionRow
schwarzschildChristoffelSlotDecisionRowFromRow row =
  schwarzschildChristoffelSlotDecisionRow
    row
    (schwarzschildChristoffelSlotDecisionFromOccupancy
      (SchwarzschildChristoffelSlotClassificationRow.occupancy row))
    (schwarzschildChristoffelSlotDecisionToBool
      (schwarzschildChristoffelSlotDecisionFromOccupancy
        (SchwarzschildChristoffelSlotClassificationRow.occupancy row)))
    ( "sevenSlotBooleanClassifier"
      ∷ "checkedSlotDecisionRow"
      ∷ [] )
    false

schwarzschildChristoffelSlotDecisionRows :
  List SchwarzschildChristoffelSlotDecisionRow
schwarzschildChristoffelSlotDecisionRows =
  map schwarzschildChristoffelSlotDecisionRowFromRow
    schwarzschildChristoffelSlotClassificationRows

record SchwarzschildChristoffelCheckedSlotClassifierSurface : Set where
  constructor schwarzschildChristoffelCheckedSlotClassifierSurface
  field
    classifierRows :
      List SchwarzschildChristoffelSlotDecisionRow

    classifierRowCount :
      Nat

    classifierTrueCount :
      Nat

    classifierFalseCount :
      Nat

    classifierBoundary :
      List String

    classifierNotPromoted :
      Bool

canonicalSchwarzschildChristoffelCheckedSlotClassifierSurface :
  SchwarzschildChristoffelCheckedSlotClassifierSurface
canonicalSchwarzschildChristoffelCheckedSlotClassifierSurface =
  schwarzschildChristoffelCheckedSlotClassifierSurface
    schwarzschildChristoffelSlotDecisionRows
    coord4SlotCount64
    coord4NonzeroSlotCount7
    coord4ZeroSlotCount57
    ( "sevenSlotBooleanClassifier"
      ∷ "checkedSevenSlotBooleanClassifier"
      ∷ "7true57falseClassifierReceipt"
      ∷ [] )
    false

record SchwarzschildChristoffelCheckedSlotClassifierReceiptSurface : Set where
  constructor schwarzschildChristoffelCheckedSlotClassifierReceiptSurface
  field
    receiptRows :
      List SchwarzschildChristoffelSlotDecisionRow

    receiptRowCount :
      Nat

    receiptTrueCount :
      Nat

    receiptFalseCount :
      Nat

    receiptBoundary :
      List String

    receiptNotPromoted :
      Bool

canonicalSchwarzschildChristoffelCheckedSlotClassifierReceiptSurface :
  SchwarzschildChristoffelCheckedSlotClassifierReceiptSurface
canonicalSchwarzschildChristoffelCheckedSlotClassifierReceiptSurface =
  schwarzschildChristoffelCheckedSlotClassifierReceiptSurface
    schwarzschildChristoffelSlotDecisionRows
    coord4SlotCount64
    coord4NonzeroSlotCount7
    coord4ZeroSlotCount57
    ( "checkedSevenSlotBooleanClassifierReceipt"
      ∷ "7true57falseReceipt"
      ∷ [] )
    false

schwarzschildSymmetricNonzeroSlotDecisionRows :
  List SchwarzschildChristoffelSlotDecisionRow
schwarzschildSymmetricNonzeroSlotDecisionRows =
  map schwarzschildChristoffelSlotDecisionRowFromRow
    schwarzschildSymmetricNonzeroSlotClassificationRows

schwarzschildSymmetricSlotDecisionRows :
  List SchwarzschildChristoffelSlotDecisionRow
schwarzschildSymmetricSlotDecisionRows =
  map schwarzschildChristoffelSlotDecisionRowFromRow
    schwarzschildSymmetricSlotClassificationRows

schwarzschildSymmetricSlotCheckedSlotClassifierSurface :
  SchwarzschildChristoffelCheckedSlotClassifierSurface
schwarzschildSymmetricSlotCheckedSlotClassifierSurface =
  schwarzschildChristoffelCheckedSlotClassifierSurface
    schwarzschildSymmetricSlotDecisionRows
    coord4SlotCount64
    coord4SymmetricNonzeroSlotCount10
    coord4SymmetricZeroSlotCount54
    ( "symmetricSlotBooleanClassifier"
      ∷ "checkedSymmetricSlotBooleanClassifier"
      ∷ "10true54falseClassifierReceipt"
      ∷ [] )
    false

schwarzschildSymmetricSlotCheckedSlotClassifierReceiptSurface :
  SchwarzschildChristoffelCheckedSlotClassifierReceiptSurface
schwarzschildSymmetricSlotCheckedSlotClassifierReceiptSurface =
  schwarzschildChristoffelCheckedSlotClassifierReceiptSurface
    schwarzschildSymmetricSlotDecisionRows
    coord4SlotCount64
    coord4SymmetricNonzeroSlotCount10
    coord4SymmetricZeroSlotCount54
    ( "checkedSymmetricSlotBooleanClassifierReceipt"
      ∷ "10true54falseReceipt"
      ∷ [] )
    false

schwarzschildSevenNonzeroSlotNames :
  List String
schwarzschildSevenNonzeroSlotNames =
  "gammaTtr" ∷
  "gammaRtt" ∷
  "gammaRrr" ∷
  "gammaRThetaTheta" ∷
  "gammaRPhiPhi" ∷
  "gammaThetaRTheta" ∷
  "gammaPhiRPhi" ∷
  []

schwarzschildNonzeroSlotDecisionRows :
  List SchwarzschildChristoffelSlotDecisionRow
schwarzschildNonzeroSlotDecisionRows =
  map schwarzschildChristoffelSlotDecisionRowFromRow
    schwarzschildNonzeroSlotClassificationRows

schwarzschildDiagonalNonzeroSlotQuestionName :
  String
schwarzschildDiagonalNonzeroSlotQuestionName = "DiagonalNonzeroSlot?"

schwarzschildSymmetricDiagonalNonzeroSlotQuestionName :
  String
schwarzschildSymmetricDiagonalNonzeroSlotQuestionName =
  schwarzschildDiagonalNonzeroSlotQuestionName

schwarzschildSymmetricDiagonalNonzeroSlotBoundary :
  List String
schwarzschildSymmetricDiagonalNonzeroSlotBoundary =
  schwarzschildSymmetricDiagonalNonzeroSlotQuestionName ∷
  "10 symmetric diagonal Christoffel slots and 54 zero slots across 64 triples"
  ∷ []

schwarzschildDiagonalNonzeroSlotBoundary :
  List String
schwarzschildDiagonalNonzeroSlotBoundary =
  schwarzschildDiagonalNonzeroSlotQuestionName ∷
  "7 symmetry classes and the 64-slot diagonal Christoffel ledger remain receipt-only"
  ∷ []

record SchwarzschildDiagonalNonzeroSlotSurface : Set where
  constructor schwarzschildDiagonalNonzeroSlotSurface
  field
    predicateSurface :
      SchwarzschildChristoffelSlotClassificationSurface

    decisionSurface :
      SchwarzschildChristoffelCheckedSlotClassifierSurface

    receiptSurface :
      SchwarzschildChristoffelCheckedSlotClassifierReceiptSurface

    allSlotCount :
      Nat

    nonzeroSlotCount :
      Nat

    zeroSlotCount :
      Nat

    nonzeroSlotCoordinates :
      List Coord4Slot

    nonzeroSymmetryClassNames :
      List String

    nonzeroClassificationRows :
      List SchwarzschildChristoffelSlotClassificationRow

    nonzeroDecisionRows :
      List SchwarzschildChristoffelSlotDecisionRow

canonicalSchwarzschildDiagonalNonzeroSlotSurface :
  SchwarzschildDiagonalNonzeroSlotSurface
canonicalSchwarzschildDiagonalNonzeroSlotSurface =
  schwarzschildDiagonalNonzeroSlotSurface
    canonicalSchwarzschildChristoffelSlotClassificationSurface
    canonicalSchwarzschildChristoffelCheckedSlotClassifierSurface
    canonicalSchwarzschildChristoffelCheckedSlotClassifierReceiptSurface
    coord4SlotCount64
    coord4NonzeroSlotCount7
    coord4ZeroSlotCount57
    schwarzschildNonzeroSlotCoordinates
    schwarzschildSevenNonzeroSlotNames
    schwarzschildNonzeroSlotClassificationRows
    schwarzschildNonzeroSlotDecisionRows

schwarzschildSymmetricNonzeroSlotNames :
  List String
schwarzschildSymmetricNonzeroSlotNames =
  "gamma001" ∷
  "gamma010" ∷
  "gamma100" ∷
  "gamma111" ∷
  "gamma122" ∷
  "gamma133" ∷
  "gamma212" ∷
  "gamma221" ∷
  "gamma313" ∷
  "gamma331" ∷ []

schwarzschildSymmetricDiagonalNonzeroSlotSurface :
  SchwarzschildDiagonalNonzeroSlotSurface
schwarzschildSymmetricDiagonalNonzeroSlotSurface =
  schwarzschildDiagonalNonzeroSlotSurface
    schwarzschildSymmetricSlotClassificationSurface
    schwarzschildSymmetricSlotCheckedSlotClassifierSurface
    schwarzschildSymmetricSlotCheckedSlotClassifierReceiptSurface
    coord4SlotCount64
    coord4SymmetricNonzeroSlotCount10
    coord4SymmetricZeroSlotCount54
    schwarzschildSymmetricNonzeroSlotCoordinates
    schwarzschildSymmetricNonzeroSlotNames
    schwarzschildSymmetricNonzeroSlotClassificationRows
    schwarzschildSymmetricNonzeroSlotDecisionRows

canonicalSchwarzschildSymmetricDiagonalNonzeroSlotSurface :
  SchwarzschildDiagonalNonzeroSlotSurface
canonicalSchwarzschildSymmetricDiagonalNonzeroSlotSurface =
  schwarzschildSymmetricDiagonalNonzeroSlotSurface

schwarzschildDiagonalNonzeroSlotProjectionRowsFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildDiagonalNonzeroSlotProjectionRowsFromSurface surface =
  SchwarzschildDiagonalNonzeroSlotSurface.nonzeroClassificationRows surface

record SchwarzschildDiagonalNonzeroSlotProjectionSurface : Set where
  constructor schwarzschildDiagonalNonzeroSlotProjectionSurface
  field
    diagonalNonzeroSlotSurface :
      SchwarzschildDiagonalNonzeroSlotSurface

    projectionRows :
      List SchwarzschildChristoffelSlotClassificationRow

    projectionCount :
      Nat

    projectionBoundary :
      List String

    projectionNotPromoted :
      Bool

schwarzschildDiagonalNonzeroSlotProjectionSurfaceFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  SchwarzschildDiagonalNonzeroSlotProjectionSurface
schwarzschildDiagonalNonzeroSlotProjectionSurfaceFromSurface surface =
  schwarzschildDiagonalNonzeroSlotProjectionSurface
    surface
    (schwarzschildDiagonalNonzeroSlotProjectionRowsFromSurface surface)
    coord4NonzeroSlotCount7
    ( "DiagonalNonzeroSlotProjectionSurface" ∷
      "canonicalSchwarzschildDiagonalNonzeroSlotSurface" ∷
      "7 canonical Schwarzschild nonzero slots" ∷ [] )
    false

canonicalSchwarzschildDiagonalNonzeroSlotProjectionSurface :
  SchwarzschildDiagonalNonzeroSlotProjectionSurface
canonicalSchwarzschildDiagonalNonzeroSlotProjectionSurface =
  schwarzschildDiagonalNonzeroSlotProjectionSurfaceFromSurface
    canonicalSchwarzschildDiagonalNonzeroSlotSurface

schwarzschildSymmetricDiagonalNonzeroSlotProjectionRowsFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  List SchwarzschildChristoffelSlotClassificationRow
schwarzschildSymmetricDiagonalNonzeroSlotProjectionRowsFromSurface surface =
  SchwarzschildDiagonalNonzeroSlotSurface.nonzeroClassificationRows surface

schwarzschildSymmetricDiagonalNonzeroSlotProjectionSurfaceFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  SchwarzschildDiagonalNonzeroSlotProjectionSurface
schwarzschildSymmetricDiagonalNonzeroSlotProjectionSurfaceFromSurface surface =
  schwarzschildDiagonalNonzeroSlotProjectionSurface
    surface
    (schwarzschildSymmetricDiagonalNonzeroSlotProjectionRowsFromSurface surface)
    coord4SymmetricNonzeroSlotCount10
    ( "SymmetricDiagonalNonzeroSlotProjectionSurface" ∷
      "canonicalSchwarzschildSymmetricDiagonalNonzeroSlotSurface" ∷
      "10 symmetric Schwarzschild nonzero slots" ∷ [] )
    false

canonicalSchwarzschildSymmetricDiagonalNonzeroSlotProjectionSurface :
  SchwarzschildDiagonalNonzeroSlotProjectionSurface
canonicalSchwarzschildSymmetricDiagonalNonzeroSlotProjectionSurface =
  schwarzschildSymmetricDiagonalNonzeroSlotProjectionSurfaceFromSurface
    canonicalSchwarzschildSymmetricDiagonalNonzeroSlotSurface

schwarzschildDiagonalNonzeroSlotCoverageRowsFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  List SchwarzschildChristoffelSlotDecisionRow
schwarzschildDiagonalNonzeroSlotCoverageRowsFromSurface surface =
  SchwarzschildDiagonalNonzeroSlotSurface.nonzeroDecisionRows surface

record SchwarzschildDiagonalNonzeroSlotCoverageSurface : Set where
  constructor schwarzschildDiagonalNonzeroSlotCoverageSurface
  field
    projectionSurface :
      SchwarzschildDiagonalNonzeroSlotProjectionSurface

    coverageRows :
      List SchwarzschildChristoffelSlotDecisionRow

    coverageCount :
      Nat

    coverageBoundary :
      List String

    coverageNotPromoted :
      Bool

schwarzschildDiagonalNonzeroSlotCoverageSurfaceFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  SchwarzschildDiagonalNonzeroSlotCoverageSurface
schwarzschildDiagonalNonzeroSlotCoverageSurfaceFromSurface surface =
  schwarzschildDiagonalNonzeroSlotCoverageSurface
    (schwarzschildDiagonalNonzeroSlotProjectionSurfaceFromSurface surface)
    (schwarzschildDiagonalNonzeroSlotCoverageRowsFromSurface surface)
    coord4NonzeroSlotCount7
    ( "DiagonalNonzeroSlotCoverageSurface" ∷
      "checkedDiagonalNonzeroSlotClassifier" ∷
      "7-true checked Schwarzschild nonzero slots" ∷ [] )
    false

canonicalSchwarzschildDiagonalNonzeroSlotCoverageSurface :
  SchwarzschildDiagonalNonzeroSlotCoverageSurface
canonicalSchwarzschildDiagonalNonzeroSlotCoverageSurface =
  schwarzschildDiagonalNonzeroSlotCoverageSurfaceFromSurface
    canonicalSchwarzschildDiagonalNonzeroSlotSurface

schwarzschildSymmetricDiagonalNonzeroSlotCoverageRowsFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  List SchwarzschildChristoffelSlotDecisionRow
schwarzschildSymmetricDiagonalNonzeroSlotCoverageRowsFromSurface surface =
  SchwarzschildDiagonalNonzeroSlotSurface.nonzeroDecisionRows surface

schwarzschildSymmetricDiagonalNonzeroSlotCoverageSurfaceFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  SchwarzschildDiagonalNonzeroSlotCoverageSurface
schwarzschildSymmetricDiagonalNonzeroSlotCoverageSurfaceFromSurface surface =
  schwarzschildDiagonalNonzeroSlotCoverageSurface
    (schwarzschildSymmetricDiagonalNonzeroSlotProjectionSurfaceFromSurface surface)
    (schwarzschildSymmetricDiagonalNonzeroSlotCoverageRowsFromSurface surface)
    coord4SymmetricNonzeroSlotCount10
    ( "SymmetricDiagonalNonzeroSlotCoverageSurface" ∷
      "checkedSymmetricDiagonalNonzeroSlotClassifier" ∷
      "10-true checked Schwarzschild nonzero slots" ∷ [] )
    false

canonicalSchwarzschildSymmetricDiagonalNonzeroSlotCoverageSurface :
  SchwarzschildDiagonalNonzeroSlotCoverageSurface
canonicalSchwarzschildSymmetricDiagonalNonzeroSlotCoverageSurface =
  schwarzschildSymmetricDiagonalNonzeroSlotCoverageSurfaceFromSurface
    canonicalSchwarzschildSymmetricDiagonalNonzeroSlotSurface

schwarzschildDiagonalNonzeroSlotReceiptRowsFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  List SchwarzschildChristoffelSlotDecisionRow
schwarzschildDiagonalNonzeroSlotReceiptRowsFromSurface surface =
  SchwarzschildDiagonalNonzeroSlotSurface.nonzeroDecisionRows surface

record SchwarzschildDiagonalNonzeroSlotReceiptSurface : Set where
  constructor schwarzschildDiagonalNonzeroSlotReceiptSurface
  field
    coverageSurface :
      SchwarzschildDiagonalNonzeroSlotCoverageSurface

    receiptRows :
      List SchwarzschildChristoffelSlotDecisionRow

    receiptCount :
      Nat

    receiptBoundary :
      List String

    receiptNotPromoted :
      Bool

schwarzschildDiagonalNonzeroSlotReceiptSurfaceFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  SchwarzschildDiagonalNonzeroSlotReceiptSurface
schwarzschildDiagonalNonzeroSlotReceiptSurfaceFromSurface surface =
  schwarzschildDiagonalNonzeroSlotReceiptSurface
    (schwarzschildDiagonalNonzeroSlotCoverageSurfaceFromSurface surface)
    (schwarzschildDiagonalNonzeroSlotReceiptRowsFromSurface surface)
    coord4NonzeroSlotCount7
    ( "DiagonalNonzeroSlotReceiptSurface" ∷
      "receiptDiagonalNonzeroSlotClassifier" ∷
      "checkedSurfaceReceiptForSevenSchwarzschildSlots" ∷ [] )
    false

canonicalSchwarzschildDiagonalNonzeroSlotReceiptSurface :
  SchwarzschildDiagonalNonzeroSlotReceiptSurface
canonicalSchwarzschildDiagonalNonzeroSlotReceiptSurface =
  schwarzschildDiagonalNonzeroSlotReceiptSurfaceFromSurface
    canonicalSchwarzschildDiagonalNonzeroSlotSurface

schwarzschildSymmetricDiagonalNonzeroSlotReceiptRowsFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  List SchwarzschildChristoffelSlotDecisionRow
schwarzschildSymmetricDiagonalNonzeroSlotReceiptRowsFromSurface surface =
  SchwarzschildDiagonalNonzeroSlotSurface.nonzeroDecisionRows surface

schwarzschildSymmetricDiagonalNonzeroSlotReceiptSurfaceFromSurface :
  SchwarzschildDiagonalNonzeroSlotSurface →
  SchwarzschildDiagonalNonzeroSlotReceiptSurface
schwarzschildSymmetricDiagonalNonzeroSlotReceiptSurfaceFromSurface surface =
  schwarzschildDiagonalNonzeroSlotReceiptSurface
    (schwarzschildSymmetricDiagonalNonzeroSlotCoverageSurfaceFromSurface surface)
    (schwarzschildSymmetricDiagonalNonzeroSlotReceiptRowsFromSurface surface)
    coord4SymmetricNonzeroSlotCount10
    ( "SymmetricDiagonalNonzeroSlotReceiptSurface" ∷
      "receiptSymmetricDiagonalNonzeroSlotClassifier" ∷
      "checkedSurfaceReceiptForTenSymmetricSchwarzschildSlots" ∷ [] )
    false

canonicalSchwarzschildSymmetricDiagonalNonzeroSlotReceiptSurface :
  SchwarzschildDiagonalNonzeroSlotReceiptSurface
canonicalSchwarzschildSymmetricDiagonalNonzeroSlotReceiptSurface =
  schwarzschildSymmetricDiagonalNonzeroSlotReceiptSurfaceFromSurface
    canonicalSchwarzschildSymmetricDiagonalNonzeroSlotSurface

DiagonalNonzeroSlotPredicateSurface : Set
DiagonalNonzeroSlotPredicateSurface =
  SchwarzschildChristoffelSlotClassificationSurface

DiagonalNonzeroSlotDecisionSurface : Set
DiagonalNonzeroSlotDecisionSurface =
  SchwarzschildChristoffelCheckedSlotClassifierSurface

DiagonalNonzeroSlotReceiptSurface : Set
DiagonalNonzeroSlotReceiptSurface =
  SchwarzschildChristoffelCheckedSlotClassifierReceiptSurface

DiagonalNonzeroSlotProjectionSurface : Set
DiagonalNonzeroSlotProjectionSurface =
  SchwarzschildDiagonalNonzeroSlotProjectionSurface

DiagonalNonzeroSlotCoverageSurface : Set
DiagonalNonzeroSlotCoverageSurface =
  SchwarzschildDiagonalNonzeroSlotCoverageSurface

DiagonalNonzeroSlotCheckedReceiptSurface : Set
DiagonalNonzeroSlotCheckedReceiptSurface =
  SchwarzschildDiagonalNonzeroSlotReceiptSurface

DiagonalNonzeroSlotQuestionName : String
DiagonalNonzeroSlotQuestionName = schwarzschildDiagonalNonzeroSlotQuestionName

DiagonalNonzeroSlotBoundary : List String
DiagonalNonzeroSlotBoundary = schwarzschildDiagonalNonzeroSlotBoundary

DiagonalNonzeroSlotSurface : Set
DiagonalNonzeroSlotSurface = SchwarzschildDiagonalNonzeroSlotSurface

DiagonalSymmetricNonzeroSlotPredicateSurface : Set
DiagonalSymmetricNonzeroSlotPredicateSurface =
  SchwarzschildChristoffelSlotClassificationSurface

DiagonalSymmetricNonzeroSlotDecisionSurface : Set
DiagonalSymmetricNonzeroSlotDecisionSurface =
  SchwarzschildChristoffelCheckedSlotClassifierSurface

DiagonalSymmetricNonzeroSlotReceiptSurface : Set
DiagonalSymmetricNonzeroSlotReceiptSurface =
  SchwarzschildChristoffelCheckedSlotClassifierReceiptSurface

DiagonalSymmetricNonzeroSlotProjectionSurface : Set
DiagonalSymmetricNonzeroSlotProjectionSurface =
  SchwarzschildDiagonalNonzeroSlotProjectionSurface

DiagonalSymmetricNonzeroSlotCoverageSurface : Set
DiagonalSymmetricNonzeroSlotCoverageSurface =
  SchwarzschildDiagonalNonzeroSlotCoverageSurface

DiagonalSymmetricNonzeroSlotCheckedReceiptSurface : Set
DiagonalSymmetricNonzeroSlotCheckedReceiptSurface =
  SchwarzschildDiagonalNonzeroSlotReceiptSurface

DiagonalSymmetricNonzeroSlotQuestionName : String
DiagonalSymmetricNonzeroSlotQuestionName =
  schwarzschildSymmetricDiagonalNonzeroSlotQuestionName

DiagonalSymmetricNonzeroSlotBoundary : List String
DiagonalSymmetricNonzeroSlotBoundary =
  schwarzschildSymmetricDiagonalNonzeroSlotBoundary

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

------------------------------------------------------------------------
-- Boolean ledger and receipt surfaces for the seven canonical nonzero slots.

record SchwarzschildChristoffelSevenSlotLedgerRow : Set where
  constructor schwarzschildChristoffelSevenSlotLedgerRow
  field
    rowName :
      String

    rowSlot :
      SchwarzschildChristoffelSlot

    rowCoordinates :
      Coord4Slot

    rowIsNonzero :
      Bool

    rowBoundary :
      List String

    rowNotPromoted :
      Bool

schwarzschildChristoffelSevenSlotLedgerRowFromSlot :
  SchwarzschildChristoffelSlot →
  SchwarzschildChristoffelSevenSlotLedgerRow
schwarzschildChristoffelSevenSlotLedgerRowFromSlot gammaTtr =
  schwarzschildChristoffelSevenSlotLedgerRow
    "gammaTtrLedgerRow"
    gammaTtr
    schwarzschildGammaTtrCoordinates
    true
    ( "sevenSlotBooleanLedgerRow" ∷ "gammaTtr" ∷ [] )
    false
schwarzschildChristoffelSevenSlotLedgerRowFromSlot gammaRtt =
  schwarzschildChristoffelSevenSlotLedgerRow
    "gammaRttLedgerRow"
    gammaRtt
    schwarzschildGammaRttCoordinates
    true
    ( "sevenSlotBooleanLedgerRow" ∷ "gammaRtt" ∷ [] )
    false
schwarzschildChristoffelSevenSlotLedgerRowFromSlot gammaRrr =
  schwarzschildChristoffelSevenSlotLedgerRow
    "gammaRrrLedgerRow"
    gammaRrr
    schwarzschildGammaRrrCoordinates
    true
    ( "sevenSlotBooleanLedgerRow" ∷ "gammaRrr" ∷ [] )
    false
schwarzschildChristoffelSevenSlotLedgerRowFromSlot gammaRThetaTheta =
  schwarzschildChristoffelSevenSlotLedgerRow
    "gammaRThetaThetaLedgerRow"
    gammaRThetaTheta
    schwarzschildGammaRThetaThetaCoordinates
    true
    ( "sevenSlotBooleanLedgerRow" ∷ "gammaRThetaTheta" ∷ [] )
    false
schwarzschildChristoffelSevenSlotLedgerRowFromSlot gammaRPhiPhi =
  schwarzschildChristoffelSevenSlotLedgerRow
    "gammaRPhiPhiLedgerRow"
    gammaRPhiPhi
    schwarzschildGammaRPhiPhiCoordinates
    true
    ( "sevenSlotBooleanLedgerRow" ∷ "gammaRPhiPhi" ∷ [] )
    false
schwarzschildChristoffelSevenSlotLedgerRowFromSlot gammaThetaRTheta =
  schwarzschildChristoffelSevenSlotLedgerRow
    "gammaThetaRThetaLedgerRow"
    gammaThetaRTheta
    schwarzschildGammaThetaRThetaCoordinates
    true
    ( "sevenSlotBooleanLedgerRow" ∷ "gammaThetaRTheta" ∷ [] )
    false
schwarzschildChristoffelSevenSlotLedgerRowFromSlot gammaPhiRPhi =
  schwarzschildChristoffelSevenSlotLedgerRow
    "gammaPhiRPhiLedgerRow"
    gammaPhiRPhi
    schwarzschildGammaPhiRPhiCoordinates
    true
    ( "sevenSlotBooleanLedgerRow" ∷ "gammaPhiRPhi" ∷ [] )
    false

schwarzschildChristoffelSevenSlotLedgerRows :
  List SchwarzschildChristoffelSevenSlotLedgerRow
schwarzschildChristoffelSevenSlotLedgerRows =
  map schwarzschildChristoffelSevenSlotLedgerRowFromSlot
    schwarzschildSevenNonzeroSlots

record SchwarzschildChristoffelSevenSlotClassifierSurface : Set where
  constructor schwarzschildChristoffelSevenSlotClassifierSurface
  field
    classifierRows :
      List SchwarzschildChristoffelSevenSlotLedgerRow

    classifierRowCount :
      Nat

    classifierBoundary :
      List String

    classifierNotPromoted :
      Bool

canonicalSchwarzschildChristoffelSevenSlotClassifierSurface :
  SchwarzschildChristoffelSevenSlotClassifierSurface
canonicalSchwarzschildChristoffelSevenSlotClassifierSurface =
  schwarzschildChristoffelSevenSlotClassifierSurface
    schwarzschildChristoffelSevenSlotLedgerRows
    coord4NonzeroSlotCount7
    ( "sevenSlotBooleanClassifier" ∷
      "canonicalSchwarzschildChristoffelSevenSlotClassifierSurface" ∷
      [] )
    false

record SchwarzschildChristoffelSevenSlotReceiptSurface : Set where
  constructor schwarzschildChristoffelSevenSlotReceiptSurface
  field
    receiptRows :
      List SchwarzschildChristoffelSevenSlotLedgerRow

    receiptRowCount :
      Nat

    receiptBoundary :
      List String

    receiptNotPromoted :
      Bool

canonicalSchwarzschildChristoffelSevenSlotReceiptSurface :
  SchwarzschildChristoffelSevenSlotReceiptSurface
canonicalSchwarzschildChristoffelSevenSlotReceiptSurface =
  schwarzschildChristoffelSevenSlotReceiptSurface
    schwarzschildChristoffelSevenSlotLedgerRows
    coord4NonzeroSlotCount7
    ( "sevenSlotCanonicalReceipt" ∷
      "sevenSlotBooleanClassifierReceipt" ∷
      [] )
    false

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

record SchwarzschildChristoffelFormulaLawCarrierRow : Set where
  constructor schwarzschildChristoffelFormulaLawCarrierRow
  field
    row :
      ChristoffelFormulaLaw

    rowBoundary :
      List String

    rowNotPromoted :
      Bool

record SchwarzschildInverseMetricLawCarrierRow : Set where
  constructor schwarzschildInverseMetricLawCarrierRow
  field
    row :
      InverseMetricLaw

    rowBoundary :
      List String

    rowNotPromoted :
      Bool

record SchwarzschildMetricCompatibilityLawCarrierRow : Set where
  constructor schwarzschildMetricCompatibilityLawCarrierRow
  field
    row :
      MetricCompatibilityLaw

    rowBoundary :
      List String

    rowNotPromoted :
      Bool

record SchwarzschildDiagonalFormulaLawCarrierSurface : Set where
  constructor schwarzschildDiagonalFormulaLawCarrierSurface
  field
    formulaCarrier :
      SchwarzschildDiagonalFormulaCarrierSurface

    christoffelFormulaRows :
      List SchwarzschildChristoffelFormulaLawCarrierRow

    inverseMetricLawRows :
      List SchwarzschildInverseMetricLawCarrierRow

    metricCompatibilityRows :
      List SchwarzschildMetricCompatibilityLawCarrierRow

    formulaCarrierBoundary :
      List String

    formulaCarrierNotPromoted :
      Bool

schwarzschildDiagonalFormulaLawCarrierSurfaceFromCarrier :
  SchwarzschildDiagonalFormulaCarrierSurface →
  SchwarzschildDiagonalFormulaLawCarrierSurface
schwarzschildDiagonalFormulaLawCarrierSurfaceFromCarrier carrier =
  schwarzschildDiagonalFormulaLawCarrierSurface
    carrier
    ( diagonalOneTermReductionCarrierRow
      ∷ sevenSlotNonzeroReductionCarrierRow
      ∷ zeroSlot57ClosureCarrierRow
      ∷ [] )
    ( diagonalOneTermInverseReductionCarrierRow ∷ [] )
    ( diagonalMetricCompatibilityReductionCarrierRow ∷ [] )
    ( "diagonal Christoffel formula, inverse metric, and metric compatibility rows"
      ∷ [] )
    false
  where
    diagonalOneTermReductionCarrierRow :
      SchwarzschildChristoffelFormulaLawCarrierRow
    diagonalOneTermReductionCarrierRow =
      schwarzschildChristoffelFormulaLawCarrierRow
        diagonalOneTermReduction
        ( "diagonalOneTermReduction" ∷ [] )
        false

    sevenSlotNonzeroReductionCarrierRow :
      SchwarzschildChristoffelFormulaLawCarrierRow
    sevenSlotNonzeroReductionCarrierRow =
      schwarzschildChristoffelFormulaLawCarrierRow
        sevenSlotNonzeroReduction
        ( "sevenSlotNonzeroReduction" ∷ [] )
        false

    zeroSlot57ClosureCarrierRow :
      SchwarzschildChristoffelFormulaLawCarrierRow
    zeroSlot57ClosureCarrierRow =
      schwarzschildChristoffelFormulaLawCarrierRow
        zeroSlot57Closure
        ( "zeroSlot57Closure" ∷ [] )
        false

    diagonalOneTermInverseReductionCarrierRow :
      SchwarzschildInverseMetricLawCarrierRow
    diagonalOneTermInverseReductionCarrierRow =
      schwarzschildInverseMetricLawCarrierRow
        diagonalOneTermInverseReduction
        ( "diagonalOneTermInverseReduction" ∷ [] )
        false

    diagonalMetricCompatibilityReductionCarrierRow :
      SchwarzschildMetricCompatibilityLawCarrierRow
    diagonalMetricCompatibilityReductionCarrierRow =
      schwarzschildMetricCompatibilityLawCarrierRow
        diagonalMetricCompatibilityReduction
        ( "diagonalMetricCompatibilityReduction" ∷ [] )
        false

------------------------------------------------------------------------
-- Canonical checked projection rows for the diagonal Christoffel law.
-- These rows remain fail-closed and concrete so downstream modules can
-- consume diagonal slot projections without repeating slot enumeration.

schwarzschildChristoffelSlotRowName :
  SchwarzschildChristoffelSlot →
  String
schwarzschildChristoffelSlotRowName gammaTtr = "gammaTtr"
schwarzschildChristoffelSlotRowName gammaRtt = "gammaRtt"
schwarzschildChristoffelSlotRowName gammaRrr = "gammaRrr"
schwarzschildChristoffelSlotRowName gammaRThetaTheta = "gammaRThetaTheta"
schwarzschildChristoffelSlotRowName gammaRPhiPhi = "gammaRPhiPhi"
schwarzschildChristoffelSlotRowName gammaThetaRTheta = "gammaThetaRTheta"
schwarzschildChristoffelSlotRowName gammaPhiRPhi = "gammaPhiRPhi"

schwarzschildFormulaLawFromChristoffelSlot :
  SchwarzschildChristoffelSlot →
  ChristoffelFormulaLaw
schwarzschildFormulaLawFromChristoffelSlot gammaTtr = sevenSlotNonzeroReduction
schwarzschildFormulaLawFromChristoffelSlot gammaRtt = sevenSlotNonzeroReduction
schwarzschildFormulaLawFromChristoffelSlot gammaRrr = sevenSlotNonzeroReduction
schwarzschildFormulaLawFromChristoffelSlot gammaRThetaTheta = sevenSlotNonzeroReduction
schwarzschildFormulaLawFromChristoffelSlot gammaRPhiPhi = sevenSlotNonzeroReduction
schwarzschildFormulaLawFromChristoffelSlot gammaThetaRTheta = sevenSlotNonzeroReduction
schwarzschildFormulaLawFromChristoffelSlot gammaPhiRPhi = sevenSlotNonzeroReduction

schwarzschildFormulaSlotValueFromSurface :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelSlot →
  SchwarzschildChristoffelSlotFormula
schwarzschildFormulaSlotValueFromSurface surface gammaTtr =
  SchwarzschildChristoffelFormulaSurface.ttrFormula surface
schwarzschildFormulaSlotValueFromSurface surface gammaRtt =
  SchwarzschildChristoffelFormulaSurface.rttFormula surface
schwarzschildFormulaSlotValueFromSurface surface gammaRrr =
  SchwarzschildChristoffelFormulaSurface.rrrFormula surface
schwarzschildFormulaSlotValueFromSurface surface gammaRThetaTheta =
  SchwarzschildChristoffelFormulaSurface.rThetaThetaFormula surface
schwarzschildFormulaSlotValueFromSurface surface gammaRPhiPhi =
  SchwarzschildChristoffelFormulaSurface.rPhiPhiFormula surface
schwarzschildFormulaSlotValueFromSurface surface gammaThetaRTheta =
  SchwarzschildChristoffelFormulaSurface.thetaRThetaFormula surface
schwarzschildFormulaSlotValueFromSurface surface gammaPhiRPhi =
  SchwarzschildChristoffelFormulaSurface.phiRPhiFormula surface

record SchwarzschildChristoffelFormulaLawProjectionRow : Set where
  constructor schwarzschildChristoffelFormulaLawProjectionRow
  field
    rowName :
      String

    lawRow :
      ChristoffelFormulaLaw

    slot :
      SchwarzschildChristoffelSlot

    slotFormula :
      SchwarzschildChristoffelSlotFormula

    rowBoundary :
      List String

    rowNotPromoted :
      Bool

schwarzschildChristoffelFormulaLawProjectionRowFromSlot :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelSlot →
  SchwarzschildChristoffelFormulaLawProjectionRow
schwarzschildChristoffelFormulaLawProjectionRowFromSlot surface slot =
  schwarzschildChristoffelFormulaLawProjectionRow
    (schwarzschildChristoffelSlotRowName slot)
    (schwarzschildFormulaLawFromChristoffelSlot slot)
    slot
    (schwarzschildFormulaSlotValueFromSurface surface slot)
    ( "christoffelFormulaLawProjectionRow" ∷
      schwarzschildChristoffelSlotRowName slot
      ∷ [] )
    false

schwarzschildChristoffelFormulaLawProjectionRowsFromSurface :
  SchwarzschildChristoffelFormulaSurface →
  List SchwarzschildChristoffelFormulaLawProjectionRow
schwarzschildChristoffelFormulaLawProjectionRowsFromSurface surface =
  map (schwarzschildChristoffelFormulaLawProjectionRowFromSlot surface)
    schwarzschildSevenNonzeroSlots

schwarzschildChristoffelFormulaLawProjectionNonzeroCount :
  Nat
schwarzschildChristoffelFormulaLawProjectionNonzeroCount =
  coord4NonzeroSlotCount7

schwarzschildChristoffelFormulaLawCarrierRowName :
  ChristoffelFormulaLaw →
  String
schwarzschildChristoffelFormulaLawCarrierRowName diagonalOneTermReduction =
  "diagonalOneTermReduction"
schwarzschildChristoffelFormulaLawCarrierRowName sevenSlotNonzeroReduction =
  "sevenSlotNonzeroReduction"
schwarzschildChristoffelFormulaLawCarrierRowName zeroSlot57Closure =
  "zeroSlot57Closure"

record SchwarzschildChristoffelFormulaLawProjectionSurface : Set where
  constructor schwarzschildChristoffelFormulaLawProjectionSurface
  field
    christoffelFormula :
      SchwarzschildChristoffelFormulaSurface

    nonzeroProjectionRows :
      List SchwarzschildChristoffelFormulaLawProjectionRow

    nonzeroProjectionCount :
      Nat

    reductionRows :
      List SchwarzschildChristoffelFormulaLawCarrierRow

    projectionBoundary :
      List String

    projectionNotPromoted :
      Bool

schwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier :
  SchwarzschildDiagonalFormulaCarrierSurface →
  SchwarzschildChristoffelFormulaLawProjectionSurface
schwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier carrier =
  schwarzschildChristoffelFormulaLawProjectionSurface
    (SchwarzschildDiagonalFormulaCarrierSurface.christoffelFormula carrier)
    (schwarzschildChristoffelFormulaLawProjectionRowsFromSurface
      (SchwarzschildDiagonalFormulaCarrierSurface.christoffelFormula carrier))
    schwarzschildChristoffelFormulaLawProjectionNonzeroCount
    ( (schwarzschildChristoffelFormulaLawCarrierRow
        diagonalOneTermReduction
        (schwarzschildChristoffelFormulaLawCarrierRowName diagonalOneTermReduction ∷ [])
        false)
      ∷ (schwarzschildChristoffelFormulaLawCarrierRow
        sevenSlotNonzeroReduction
        (schwarzschildChristoffelFormulaLawCarrierRowName sevenSlotNonzeroReduction ∷ [])
        false)
      ∷ (schwarzschildChristoffelFormulaLawCarrierRow
        zeroSlot57Closure
        (schwarzschildChristoffelFormulaLawCarrierRowName zeroSlot57Closure ∷ [])
        false)
      ∷ [] )
    ( "projection surface over diagonal Christoffel formula rows"
      ∷ "7 nonzero canonical slots + 1 zero-closure + 1 one-term law row"
      ∷ [] )
    false

-- Canonical inverse-metric law projections, using diagonal slot coordinates.
-- We keep projections concrete and total so downstream readers can consume
-- all diagonal inverse-metric diagonal slots without rebuilding rows.

schwarzschildDiagonalCoordName :
  Coord4 →
  String
schwarzschildDiagonalCoordName coord0 = "tt"
schwarzschildDiagonalCoordName coord1 = "rr"
schwarzschildDiagonalCoordName coord2 = "thetaTheta"
schwarzschildDiagonalCoordName coord3 = "phiPhi"

schwarzschildDiagonalSlotFromCoord :
  Coord4 →
  Coord4Slot
schwarzschildDiagonalSlotFromCoord coord0 = schwarzschildSlot coord0 coord0 coord0
schwarzschildDiagonalSlotFromCoord coord1 = schwarzschildSlot coord1 coord1 coord1
schwarzschildDiagonalSlotFromCoord coord2 = schwarzschildSlot coord2 coord2 coord2
schwarzschildDiagonalSlotFromCoord coord3 = schwarzschildSlot coord3 coord3 coord3

schwarzschildInverseMetricLawProjectionRowName :
  Coord4 →
  String
schwarzschildInverseMetricLawProjectionRowName coord0 = "inverseMetricTT"
schwarzschildInverseMetricLawProjectionRowName coord1 = "inverseMetricRR"
schwarzschildInverseMetricLawProjectionRowName coord2 = "inverseMetricThetaTheta"
schwarzschildInverseMetricLawProjectionRowName coord3 = "inverseMetricPhiPhi"

record SchwarzschildInverseMetricLawProjectionRow : Set where
  constructor schwarzschildInverseMetricLawProjectionRow
  field
    rowName :
      String

    lawRow :
      InverseMetricLaw

    diagonalCoordinate :
      Coord4

    metricSlot :
      Coord4Slot

    inverseMetricSlot :
      Coord4Slot

    metricValue :
      ℚ

    inverseMetricValue :
      ℚ

    rowBoundary :
      List String

    rowNotPromoted :
      Bool

schwarzschildInverseMetricLawProjectionRowFromCarrier :
  SchwarzschildDiagonalFormulaCarrierSurface →
  Coord4 →
  SchwarzschildInverseMetricLawProjectionRow
schwarzschildInverseMetricLawProjectionRowFromCarrier carrier coord =
  schwarzschildInverseMetricLawProjectionRow
    (schwarzschildInverseMetricLawProjectionRowName coord)
    diagonalOneTermInverseReduction
    coord
    (schwarzschildDiagonalSlotFromCoord coord)
    (schwarzschildDiagonalSlotFromCoord coord)
    (schwarzschildMetricAt
      (SchwarzschildDiagonalFormulaCarrierSurface.metric carrier)
      coord)
    (schwarzschildInverseMetricAt
      (SchwarzschildDiagonalFormulaCarrierSurface.inverseMetric carrier)
      coord)
    ( "inverseMetricLawProjectionRow" ∷
      schwarzschildDiagonalCoordName coord
      ∷ [] )
    false

schwarzschildInverseMetricLawProjectionRowsFromCarrier :
  SchwarzschildDiagonalFormulaCarrierSurface →
  List SchwarzschildInverseMetricLawProjectionRow
schwarzschildInverseMetricLawProjectionRowsFromCarrier carrier =
  map (schwarzschildInverseMetricLawProjectionRowFromCarrier carrier)
    schwarzschildSlotAxes

schwarzschildInverseMetricLawProjectionRowCount :
  Nat
schwarzschildInverseMetricLawProjectionRowCount = 4

schwarzschildInverseMetricLawCarrierRowName :
  InverseMetricLaw →
  String
schwarzschildInverseMetricLawCarrierRowName diagonalOneTermInverseReduction =
  "diagonalOneTermInverseReduction"

record SchwarzschildInverseMetricLawProjectionSurface : Set where
  constructor schwarzschildInverseMetricLawProjectionSurface
  field
    inverseMetricCarrier :
      SchwarzschildDiagonalFormulaCarrierSurface

    projectionRows :
      List SchwarzschildInverseMetricLawProjectionRow

    projectionCount :
      Nat

    inverseMetricLawRows :
      List SchwarzschildInverseMetricLawCarrierRow

    projectionBoundary :
      List String

    projectionNotPromoted :
      Bool

schwarzschildInverseMetricLawProjectionSurfaceFromCarrier :
  SchwarzschildDiagonalFormulaCarrierSurface →
  SchwarzschildInverseMetricLawProjectionSurface
schwarzschildInverseMetricLawProjectionSurfaceFromCarrier carrier =
  schwarzschildInverseMetricLawProjectionSurface
    carrier
    (schwarzschildInverseMetricLawProjectionRowsFromCarrier carrier)
    schwarzschildInverseMetricLawProjectionRowCount
    ( (schwarzschildInverseMetricLawCarrierRow
        diagonalOneTermInverseReduction
        (schwarzschildInverseMetricLawCarrierRowName diagonalOneTermInverseReduction ∷ [])
        false)
      ∷ [] )
    ( "diagonal inverse metric projection by Coord4 slot coordinates"
      ∷ "4 diagonal components: tt, rr, thetaTheta, phiPhi"
      ∷ [] )
    false

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

schwarzschildChristoffelFormulaLawProjectionSurfaceFromLawSurface :
  SchwarzschildFormulaLawSurface →
  SchwarzschildChristoffelFormulaLawProjectionSurface
schwarzschildChristoffelFormulaLawProjectionSurfaceFromLawSurface lawSurface =
  schwarzschildChristoffelFormulaLawProjectionSurfaceFromCarrier
    (SchwarzschildFormulaLawSurface.metricCarrier lawSurface)

schwarzschildInverseMetricLawProjectionSurfaceFromLawSurface :
  SchwarzschildFormulaLawSurface →
  SchwarzschildInverseMetricLawProjectionSurface
schwarzschildInverseMetricLawProjectionSurfaceFromLawSurface lawSurface =
  schwarzschildInverseMetricLawProjectionSurfaceFromCarrier
    (SchwarzschildFormulaLawSurface.metricCarrier lawSurface)

------------------------------------------------------------------------
-- Named Christoffel law rows and the 57-slot zero closure.
--
-- These definitions stay at the surface level.  They record the seven
-- canonical nonzero Schwarzschild Christoffel slots individually, and they
-- give the complementary 57-slot closure a concrete named list so downstream
-- perturbation work can project the row family without promoting any theorem.

record SchwarzschildChristoffelNamedLawRow : Set where
  constructor schwarzschildChristoffelNamedLawRow
  field
    rowName :
      String

    rowSlot :
      SchwarzschildChristoffelSlot

    rowFormula :
      SchwarzschildChristoffelSlotFormula

    rowBoundary :
      List String

    rowNotPromoted :
      Bool

schwarzschildChristoffelTtrNamedLawRow :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelNamedLawRow
schwarzschildChristoffelTtrNamedLawRow surface =
  schwarzschildChristoffelNamedLawRow
    "ttrLawRow"
    gammaTtr
    (SchwarzschildChristoffelFormulaSurface.ttrFormula surface)
    ("rowTtr" ∷ [])
    false

schwarzschildChristoffelRttNamedLawRow :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelNamedLawRow
schwarzschildChristoffelRttNamedLawRow surface =
  schwarzschildChristoffelNamedLawRow
    "rttLawRow"
    gammaRtt
    (SchwarzschildChristoffelFormulaSurface.rttFormula surface)
    ("rowRtt" ∷ [])
    false

schwarzschildChristoffelRrrNamedLawRow :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelNamedLawRow
schwarzschildChristoffelRrrNamedLawRow surface =
  schwarzschildChristoffelNamedLawRow
    "rrrLawRow"
    gammaRrr
    (SchwarzschildChristoffelFormulaSurface.rrrFormula surface)
    ("rowRrr" ∷ [])
    false

schwarzschildChristoffelRThetaThetaNamedLawRow :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelNamedLawRow
schwarzschildChristoffelRThetaThetaNamedLawRow surface =
  schwarzschildChristoffelNamedLawRow
    "rThetaThetaLawRow"
    gammaRThetaTheta
    (SchwarzschildChristoffelFormulaSurface.rThetaThetaFormula surface)
    ("rowRThetaTheta" ∷ [])
    false

schwarzschildChristoffelRPhiPhiNamedLawRow :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelNamedLawRow
schwarzschildChristoffelRPhiPhiNamedLawRow surface =
  schwarzschildChristoffelNamedLawRow
    "rPhiPhiLawRow"
    gammaRPhiPhi
    (SchwarzschildChristoffelFormulaSurface.rPhiPhiFormula surface)
    ("rowRPhiPhi" ∷ [])
    false

schwarzschildChristoffelThetaRThetaNamedLawRow :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelNamedLawRow
schwarzschildChristoffelThetaRThetaNamedLawRow surface =
  schwarzschildChristoffelNamedLawRow
    "thetaRThetaLawRow"
    gammaThetaRTheta
    (SchwarzschildChristoffelFormulaSurface.thetaRThetaFormula surface)
    ("rowThetaRTheta" ∷ [])
    false

schwarzschildChristoffelPhiRPhiNamedLawRow :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelNamedLawRow
schwarzschildChristoffelPhiRPhiNamedLawRow surface =
  schwarzschildChristoffelNamedLawRow
    "phiRPhiLawRow"
    gammaPhiRPhi
    (SchwarzschildChristoffelFormulaSurface.phiRPhiFormula surface)
    ("rowPhiRPhi" ∷ [])
    false

record SchwarzschildChristoffelSevenNamedLawSurface : Set where
  constructor schwarzschildChristoffelSevenNamedLawSurfaceRecord
  field
    ttrRow :
      SchwarzschildChristoffelNamedLawRow

    rttRow :
      SchwarzschildChristoffelNamedLawRow

    rrrRow :
      SchwarzschildChristoffelNamedLawRow

    rThetaThetaRow :
      SchwarzschildChristoffelNamedLawRow

    rPhiPhiRow :
      SchwarzschildChristoffelNamedLawRow

    thetaRThetaRow :
      SchwarzschildChristoffelNamedLawRow

    phiRPhiRow :
      SchwarzschildChristoffelNamedLawRow

    surfaceBoundary :
      List String

    surfaceNotPromoted :
      Bool

schwarzschildChristoffelSevenNamedLawSurfaceFromFormulaSurface :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelSevenNamedLawSurface
schwarzschildChristoffelSevenNamedLawSurfaceFromFormulaSurface surface =
  schwarzschildChristoffelSevenNamedLawSurfaceRecord
    (schwarzschildChristoffelTtrNamedLawRow surface)
    (schwarzschildChristoffelRttNamedLawRow surface)
    (schwarzschildChristoffelRrrNamedLawRow surface)
    (schwarzschildChristoffelRThetaThetaNamedLawRow surface)
    (schwarzschildChristoffelRPhiPhiNamedLawRow surface)
    (schwarzschildChristoffelThetaRThetaNamedLawRow surface)
    (schwarzschildChristoffelPhiRPhiNamedLawRow surface)
    ( "sevenNonzeroChristoffelRows" ∷
      "schwarzschildDiagonalLawCore" ∷
      [] )
    false

record SchwarzschildChristoffelZeroSlotClosureSurface : Set where
  constructor schwarzschildChristoffelZeroSlotClosureSurfaceRecord
  field
    zeroSlotNames :
      List String

    closureBoundary :
      List String

    closureNotPromoted :
      Bool

schwarzschildChristoffelZeroSlotClosureNames :
  List String
schwarzschildChristoffelZeroSlotClosureNames =
  "zeroGamma000" ∷ "zeroGamma002" ∷ "zeroGamma003" ∷
  "zeroGamma010" ∷ "zeroGamma011" ∷ "zeroGamma012" ∷
  "zeroGamma013" ∷ "zeroGamma020" ∷ "zeroGamma021" ∷
  "zeroGamma022" ∷ "zeroGamma023" ∷ "zeroGamma030" ∷
  "zeroGamma031" ∷ "zeroGamma032" ∷ "zeroGamma033" ∷
  "zeroGamma101" ∷ "zeroGamma102" ∷ "zeroGamma103" ∷
  "zeroGamma110" ∷ "zeroGamma112" ∷ "zeroGamma113" ∷
  "zeroGamma120" ∷ "zeroGamma121" ∷ "zeroGamma123" ∷
  "zeroGamma130" ∷ "zeroGamma131" ∷ "zeroGamma132" ∷
  "zeroGamma200" ∷ "zeroGamma201" ∷ "zeroGamma202" ∷
  "zeroGamma203" ∷ "zeroGamma210" ∷ "zeroGamma211" ∷
  "zeroGamma213" ∷ "zeroGamma220" ∷ "zeroGamma221" ∷
  "zeroGamma222" ∷ "zeroGamma223" ∷ "zeroGamma230" ∷
  "zeroGamma231" ∷ "zeroGamma232" ∷ "zeroGamma233" ∷
  "zeroGamma300" ∷ "zeroGamma301" ∷ "zeroGamma302" ∷
  "zeroGamma303" ∷ "zeroGamma310" ∷ "zeroGamma311" ∷
  "zeroGamma312" ∷ "zeroGamma320" ∷ "zeroGamma321" ∷
  "zeroGamma322" ∷ "zeroGamma323" ∷ "zeroGamma330" ∷
  "zeroGamma331" ∷ "zeroGamma332" ∷ "zeroGamma333" ∷ []

schwarzschildChristoffelZeroSlotClosureSurface :
  SchwarzschildChristoffelZeroSlotClosureSurface
schwarzschildChristoffelZeroSlotClosureSurface =
  schwarzschildChristoffelZeroSlotClosureSurfaceRecord
    schwarzschildChristoffelZeroSlotClosureNames
    ( "zeroSlot57Closure" ∷
      "complementOfSevenNamedNonzeroRows" ∷
      [] )
    false

schwarzschildChristoffelSymmetricZeroSlotClosureNames :
  List String
schwarzschildChristoffelSymmetricZeroSlotClosureNames =
  "zeroGamma000" ∷ "zeroGamma002" ∷ "zeroGamma003" ∷
  "zeroGamma011" ∷ "zeroGamma012" ∷ "zeroGamma013" ∷
  "zeroGamma020" ∷ "zeroGamma021" ∷ "zeroGamma022" ∷
  "zeroGamma023" ∷ "zeroGamma030" ∷ "zeroGamma031" ∷
  "zeroGamma032" ∷ "zeroGamma033" ∷
  "zeroGamma101" ∷ "zeroGamma102" ∷ "zeroGamma103" ∷
  "zeroGamma110" ∷ "zeroGamma112" ∷ "zeroGamma113" ∷
  "zeroGamma120" ∷ "zeroGamma121" ∷ "zeroGamma123" ∷
  "zeroGamma130" ∷ "zeroGamma131" ∷ "zeroGamma132" ∷
  "zeroGamma200" ∷ "zeroGamma201" ∷ "zeroGamma202" ∷
  "zeroGamma203" ∷ "zeroGamma210" ∷ "zeroGamma211" ∷
  "zeroGamma213" ∷ "zeroGamma220" ∷ "zeroGamma222" ∷
  "zeroGamma223" ∷ "zeroGamma230" ∷ "zeroGamma231" ∷
  "zeroGamma232" ∷ "zeroGamma233" ∷
  "zeroGamma300" ∷ "zeroGamma301" ∷ "zeroGamma302" ∷
  "zeroGamma303" ∷ "zeroGamma310" ∷ "zeroGamma311" ∷
  "zeroGamma312" ∷ "zeroGamma320" ∷ "zeroGamma321" ∷
  "zeroGamma322" ∷ "zeroGamma323" ∷ "zeroGamma330" ∷
  "zeroGamma332" ∷ "zeroGamma333" ∷ []

schwarzschildChristoffelSymmetricZeroSlotClosureSurface :
  SchwarzschildChristoffelZeroSlotClosureSurface
schwarzschildChristoffelSymmetricZeroSlotClosureSurface =
  schwarzschildChristoffelZeroSlotClosureSurfaceRecord
    schwarzschildChristoffelSymmetricZeroSlotClosureNames
    ( "zeroSlot54Closure" ∷
      "complementOfTenSymmetricNamedRows" ∷
      [] )
    false

record SchwarzschildChristoffelDiagonalLawCoreSurface : Set where
  constructor schwarzschildChristoffelDiagonalLawCoreSurfaceRecord
  field
    sevenNamedLawSurface :
      SchwarzschildChristoffelSevenNamedLawSurface

    zeroSlotClosureSurface :
      SchwarzschildChristoffelZeroSlotClosureSurface

    lawCoreBoundary :
      List String

    lawCoreNotPromoted :
      Bool

schwarzschildChristoffelDiagonalLawCoreSurfaceFromFormulaSurface :
  SchwarzschildChristoffelFormulaSurface →
  SchwarzschildChristoffelDiagonalLawCoreSurface
schwarzschildChristoffelDiagonalLawCoreSurfaceFromFormulaSurface surface =
  schwarzschildChristoffelDiagonalLawCoreSurfaceRecord
    (schwarzschildChristoffelSevenNamedLawSurfaceFromFormulaSurface surface)
    schwarzschildChristoffelZeroSlotClosureSurface
    ( "diagonalChristoffelLawCore" ∷
      "sevenRowsAndZeroClosure" ∷
      [] )
    false

schwarzschildChristoffelDiagonalLawCoreSurfaceFromCarrier :
  SchwarzschildDiagonalFormulaCarrierSurface →
  SchwarzschildChristoffelDiagonalLawCoreSurface
schwarzschildChristoffelDiagonalLawCoreSurfaceFromCarrier carrier =
  schwarzschildChristoffelDiagonalLawCoreSurfaceFromFormulaSurface
    (SchwarzschildDiagonalFormulaCarrierSurface.christoffelFormula carrier)
