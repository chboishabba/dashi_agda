module DASHI.Reasoning.TrialecticObserverMatrix369Exact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Three participants each have a locally available model of self and of the
-- other two participants.  The resulting first-order observer surface is a
-- literal 3 x 3 matrix:
--
--   A_A A_B A_C
--   B_A B_B B_C
--   C_A C_B C_C
--
-- hence three diagonal self positions plus six directed other-models.  This
-- gives a typed nine-position carrier suitable for a 369/hyperfabric chart.
-- It is NOT a claim that every three-person interaction has ternary semantics,
-- nor that the D4 square action below is psychological ontology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.D4NineCellOrbitCompressionExact as D4

data Participant3 : Set where
  participantA : Participant3
  participantB : Participant3
  participantC : Participant3

data ObserverOrder : Set where
  selfPosition : ObserverOrder
  otherModelPosition : ObserverOrder

record ObserverMatrix3 (View : Set) : Set where
  constructor observerMatrix3
  field
    aA aB aC : View
    bA bB bC : View
    cA cB cC : View

open ObserverMatrix3 public

viewAt :
  ∀ {View : Set} →
  ObserverMatrix3 View →
  Participant3 →
  Participant3 →
  View
viewAt matrix participantA participantA = aA matrix
viewAt matrix participantA participantB = aB matrix
viewAt matrix participantA participantC = aC matrix
viewAt matrix participantB participantA = bA matrix
viewAt matrix participantB participantB = bB matrix
viewAt matrix participantB participantC = bC matrix
viewAt matrix participantC participantA = cA matrix
viewAt matrix participantC participantB = cB matrix
viewAt matrix participantC participantC = cC matrix

observerOrder : Participant3 → Participant3 → ObserverOrder
observerOrder participantA participantA = selfPosition
observerOrder participantB participantB = selfPosition
observerOrder participantC participantC = selfPosition
observerOrder _ _ = otherModelPosition

aDiagonalIsSelf :
  observerOrder participantA participantA ≡ selfPosition
aDiagonalIsSelf = refl

bDiagonalIsSelf :
  observerOrder participantB participantB ≡ selfPosition
bDiagonalIsSelf = refl

cDiagonalIsSelf :
  observerOrder participantC participantC ≡ selfPosition
cDiagonalIsSelf = refl

aModelsBIsOther :
  observerOrder participantA participantB ≡ otherModelPosition
aModelsBIsOther = refl

cModelsAIsOther :
  observerOrder participantC participantA ≡ otherModelPosition
cModelsAIsOther = refl

selfPositionCount : Nat
selfPositionCount = 3

directedOtherModelCount : Nat
directedOtherModelCount = 6

observerPositionCount : Nat
observerPositionCount = selfPositionCount + directedOtherModelCount

observerPositionCountIsNine : observerPositionCount ≡ 9
observerPositionCountIsNine = refl

threeByThreeIsNine : 3 * 3 ≡ observerPositionCount
threeByThreeIsNine = refl

------------------------------------------------------------------------
-- A literal 3x3 positional chart onto the existing nine-cell D4 carrier.
--
-- This is a DASHI rechart.  Same cardinality does not identify the semantics.
------------------------------------------------------------------------

data ObserverCell : Set where
  cellAA cellAB cellAC : ObserverCell
  cellBA cellBB cellBC : ObserverCell
  cellCA cellCB cellCC : ObserverCell

observerCellToNineCell : ObserverCell → D4.NineCell
observerCellToNineCell cellAA = D4.northWest
observerCellToNineCell cellAB = D4.north
observerCellToNineCell cellAC = D4.northEast
observerCellToNineCell cellBA = D4.west
observerCellToNineCell cellBB = D4.centre
observerCellToNineCell cellBC = D4.east
observerCellToNineCell cellCA = D4.southWest
observerCellToNineCell cellCB = D4.south
observerCellToNineCell cellCC = D4.southEast

nineCellToObserverCell : D4.NineCell → ObserverCell
nineCellToObserverCell D4.northWest = cellAA
nineCellToObserverCell D4.north = cellAB
nineCellToObserverCell D4.northEast = cellAC
nineCellToObserverCell D4.west = cellBA
nineCellToObserverCell D4.centre = cellBB
nineCellToObserverCell D4.east = cellBC
nineCellToObserverCell D4.southWest = cellCA
nineCellToObserverCell D4.south = cellCB
nineCellToObserverCell D4.southEast = cellCC

observerCellRoundTrip :
  (cell : ObserverCell) →
  nineCellToObserverCell (observerCellToNineCell cell) ≡ cell
observerCellRoundTrip cellAA = refl
observerCellRoundTrip cellAB = refl
observerCellRoundTrip cellAC = refl
observerCellRoundTrip cellBA = refl
observerCellRoundTrip cellBB = refl
observerCellRoundTrip cellBC = refl
observerCellRoundTrip cellCA = refl
observerCellRoundTrip cellCB = refl
observerCellRoundTrip cellCC = refl

nineCellRoundTrip :
  (cell : D4.NineCell) →
  observerCellToNineCell (nineCellToObserverCell cell) ≡ cell
nineCellRoundTrip D4.centre = refl
nineCellRoundTrip D4.north = refl
nineCellRoundTrip D4.east = refl
nineCellRoundTrip D4.south = refl
nineCellRoundTrip D4.west = refl
nineCellRoundTrip D4.northWest = refl
nineCellRoundTrip D4.northEast = refl
nineCellRoundTrip D4.southEast = refl
nineCellRoundTrip D4.southWest = refl

record TrialecticObserverMatrixBoundary : Set where
  constructor trialectic-observer-matrix-boundary
  field
    matrixHasThreeSelfPositions : Bool
    matrixHasSixDirectedOtherModels : Bool
    matrixHasNineFirstOrderPositions : Bool
    d4ChartIsExactBijection : Bool
    d4ChartCreatesSemanticIdentity : Bool
    squareSymmetryIsPsychologicalOntology : Bool
    ninePositionsDetermineTriadicFace : Bool

canonicalTrialecticObserverMatrixBoundary :
  TrialecticObserverMatrixBoundary
canonicalTrialecticObserverMatrixBoundary =
  trialectic-observer-matrix-boundary
    true true true true false false false
