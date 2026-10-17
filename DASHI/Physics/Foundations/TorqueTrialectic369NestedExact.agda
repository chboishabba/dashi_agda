module DASHI.Physics.Foundations.TorqueTrialectic369NestedExact where

------------------------------------------------------------------------
-- NESTED TORQUE DIALECTICS -> STRUCTURED TRIALECTIC BOUNDARY
--
-- The local torque owner supplies one explicit T^3 / 27-point cell from an
-- (output, lever, force) bracket voxel.  The mature trialectic owner already
-- lifts three such cells into one dialectic (left, right, synthesis), and three
-- cyclic dialectics into the six-independent-cell T^18 boundary
--
--   A, B, C, S_AB, S_BC, S_CA.
--
-- This module makes that specialization explicit.  It does not manufacture the
-- irreducible triadic face: the existing trialectic boundary keeps that as a
-- separate mediation obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.TorqueTrialectic369Exact as Torque
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell

TorqueBasis3Cell : Set
TorqueBasis3Cell = Cell.TrialecticBasis3Cell

torqueBasisCell : Torque.BracketVoxel → TorqueBasis3Cell
torqueBasisCell = Torque.torqueVoxelPoint

makeTorqueCellDialectic :
  Torque.BracketVoxel →
  Torque.BracketVoxel →
  Torque.BracketVoxel →
  Cell.CellDialectic
makeTorqueCellDialectic left right synthesis =
  Cell.cell-dialectic
    (torqueBasisCell left)
    (torqueBasisCell right)
    (torqueBasisCell synthesis)

------------------------------------------------------------------------
-- The user's nested pattern is represented by repeated use of the same
-- (left, right, synthesis) constructor at cell scale.  A cyclic compatible
-- boundary shares A/B/C literally and retains the three synthesis cells.
------------------------------------------------------------------------

makeTorqueCompatibleBoundary :
  (a b c sab sbc sca : Torque.BracketVoxel) →
  Cell.CompatibleThreeCellTrialecticBoundary
makeTorqueCompatibleBoundary a b c sab sbc sca =
  Cell.compatible-three-cell-trialectic-boundary
    (makeTorqueCellDialectic a b sab)
    (makeTorqueCellDialectic b c sbc)
    (makeTorqueCellDialectic c a sca)
    refl
    refl
    refl

torqueBoundaryCoordinateCount : Nat
torqueBoundaryCoordinateCount =
  Cell.structuredBoundaryTernaryCoordinateCount

torqueBoundaryCoordinateCountIsEighteen :
  torqueBoundaryCoordinateCount ≡ 18
torqueBoundaryCoordinateCountIsEighteen =
  Cell.structuredBoundaryTernaryCoordinateCountIsEighteen

torqueDialecticStateCount : Nat
torqueDialecticStateCount = Cell.cellDialecticStateCount

torqueDialecticStateCountIsT9 :
  torqueDialecticStateCount ≡ 19683
torqueDialecticStateCountIsT9 =
  Cell.cellDialecticHasNineteenThousandSixHundredEightyThreeStates

------------------------------------------------------------------------
-- Exact projections show that synthesis retains, rather than replaces, the
-- two compared torque cells.
------------------------------------------------------------------------

leftTorqueCellRetained :
  (left right synthesis : Torque.BracketVoxel) →
  Cell.leftCell (makeTorqueCellDialectic left right synthesis)
  ≡ torqueBasisCell left
leftTorqueCellRetained left right synthesis = refl

rightTorqueCellRetained :
  (left right synthesis : Torque.BracketVoxel) →
  Cell.rightCell (makeTorqueCellDialectic left right synthesis)
  ≡ torqueBasisCell right
rightTorqueCellRetained left right synthesis = refl

synthesisTorqueCellRetained :
  (left right synthesis : Torque.BracketVoxel) →
  Cell.synthesisCell (makeTorqueCellDialectic left right synthesis)
  ≡ torqueBasisCell synthesis
synthesisTorqueCellRetained left right synthesis = refl

------------------------------------------------------------------------
-- Boundary: the irreducible triadic face remains separately mediated.
------------------------------------------------------------------------

record TorqueNestedTrialecticBoundary : Set where
  constructor torque-nested-trialectic-boundary
  field
    localTorqueCellIsExistingT3Basis : Bool
    torqueDialecticUsesLeftRightSynthesis : Bool
    torqueDialecticIsExistingT9Hyperform : Bool
    threeTorqueDialecticsGlueCyclically : Bool
    compatibleTorqueBoundaryHasT18Coordinates : Bool
    synthesisErasesComparedTorqueCells : Bool
    irreducibleTriadicFaceManufacturedAutomatically : Bool

canonicalTorqueNestedTrialecticBoundary :
  TorqueNestedTrialecticBoundary
canonicalTorqueNestedTrialecticBoundary =
  torque-nested-trialectic-boundary
    true
    true
    true
    true
    true
    false
    false
