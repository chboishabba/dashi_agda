module DASHI.Physics.ShiftWaveRefinementHierarchy where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftSpatialLaplacian as SSL
open import Data.Integer using (-[1+_])

------------------------------------------------------------------------
-- First genuinely distinct finite refinement hierarchy for the shift-wave
-- lane.
--
-- The coarse carrier is the existing three-point chain.
-- The refined carrier is a five-point chain with reflected endpoint shadows
-- and a true interior point. Coarse points embed at the interior indices
-- `s1`, `s2`, `s3`, which makes the coarse Laplacian match the refined
-- Laplacian on embedded points for the current projection-based field lift.

data ShiftPressurePoint5 : Set where
  s0 s1 s2 s3 s4 : ShiftPressurePoint5

embed3to5 :
  SPTI.ShiftPressurePoint → ShiftPressurePoint5
embed3to5 SPTI.shiftStartPoint = s1
embed3to5 SPTI.shiftNextPoint = s2
embed3to5 SPTI.shiftHeldExitPoint = s3

project5to3 :
  ShiftPressurePoint5 → SPTI.ShiftPressurePoint
project5to3 s0 = SPTI.shiftStartPoint
project5to3 s1 = SPTI.shiftStartPoint
project5to3 s2 = SPTI.shiftNextPoint
project5to3 s3 = SPTI.shiftHeldExitPoint
project5to3 s4 = SPTI.shiftHeldExitPoint

leftNeighbor5 : ShiftPressurePoint5 → ShiftPressurePoint5
leftNeighbor5 s0 = s0
leftNeighbor5 s1 = s0
leftNeighbor5 s2 = s1
leftNeighbor5 s3 = s2
leftNeighbor5 s4 = s3

rightNeighbor5 : ShiftPressurePoint5 → ShiftPressurePoint5
rightNeighbor5 s0 = s1
rightNeighbor5 s1 = s2
rightNeighbor5 s2 = s3
rightNeighbor5 s3 = s4
rightNeighbor5 s4 = s4

ShiftWaveField3 : Set
ShiftWaveField3 = SSL.ShiftWaveField

ShiftWaveField5 : Set
ShiftWaveField5 = ShiftPressurePoint5 → SDWS.DiscreteWave

shiftSpatialLaplacian5 :
  ShiftWaveField5 →
  ShiftPressurePoint5 →
  SDWS.DiscreteWave
shiftSpatialLaplacian5 wf s =
  SDWS.waveAdd
    (wf (leftNeighbor5 s))
    (SDWS.waveAdd
      (wf (rightNeighbor5 s))
      (SDWS.scaleWave (-[1+ 1 ]) (wf s)))

liftField3to5 :
  ShiftWaveField3 → ShiftWaveField5
liftField3to5 wf s =
  wf (project5to3 s)

LaplacianConsistency3to5 : Set
LaplacianConsistency3to5 =
  (wf : ShiftWaveField3) →
  (s : SPTI.ShiftPressurePoint) →
  shiftSpatialLaplacian5 (liftField3to5 wf) (embed3to5 s)
    ≡
  SSL.shiftSpatialLaplacian wf s

laplacianConsistency3to5 : LaplacianConsistency3to5
laplacianConsistency3to5 wf SPTI.shiftStartPoint = refl
laplacianConsistency3to5 wf SPTI.shiftNextPoint = refl
laplacianConsistency3to5 wf SPTI.shiftHeldExitPoint = refl

bulkCenter5 : ShiftPressurePoint5
bulkCenter5 = s2

BulkInteriorStencil5 : Set
BulkInteriorStencil5 =
  (wf : ShiftWaveField5) →
  shiftSpatialLaplacian5 wf bulkCenter5
    ≡
  SDWS.waveAdd
    (wf s1)
    (SDWS.waveAdd
      (wf s3)
      (SDWS.scaleWave (-[1+ 1 ]) (wf s2)))

bulkInteriorStencil5 : BulkInteriorStencil5
bulkInteriorStencil5 wf = refl

record ShiftWaveRefinementHierarchy : Setω where
  field
    coarseState : Set
    fineState : Set
    embed :
      coarseState → fineState
    project :
      fineState → coarseState
    coarseField : Set
    fineField : Set
    liftField :
      coarseField → fineField
    coarseLaplacian :
      coarseField → coarseState → SDWS.DiscreteWave
    fineLaplacian :
      fineField → fineState → SDWS.DiscreteWave
    laplacianConsistency : Set
    nonClaimBoundary : List String

shiftWaveRefinementHierarchy :
  ShiftWaveRefinementHierarchy
shiftWaveRefinementHierarchy =
  record
    { coarseState = SPTI.ShiftPressurePoint
    ; fineState = ShiftPressurePoint5
    ; embed = embed3to5
    ; project = project5to3
    ; coarseField = ShiftWaveField3
    ; fineField = ShiftWaveField5
    ; liftField = liftField3to5
    ; coarseLaplacian = SSL.shiftSpatialLaplacian
    ; fineLaplacian = shiftSpatialLaplacian5
    ; laplacianConsistency = LaplacianConsistency3to5
    ; nonClaimBoundary =
        "Finite 3-point to 5-point refinement hierarchy only"
        ∷ "coarse points embed at interior refined points s1, s2, s3"
        ∷ "refined endpoints act as reflected boundary shadows"
        ∷ "Laplacian consistency is only stated on embedded coarse points under projection-based field lift"
        ∷ "No limit, topology, derivative, or PDE convergence claim is implied"
        ∷ []
    }
