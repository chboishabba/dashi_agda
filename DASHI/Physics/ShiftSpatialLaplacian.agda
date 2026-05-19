module DASHI.Physics.ShiftSpatialLaplacian where

open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; -[1+_])
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS

------------------------------------------------------------------------
-- Finite spatial second-difference surface over the three-point shift
-- carrier.
--
-- Boundary behavior is reflected / Neumann-style at the endpoints. This is a
-- finite carrier operator only, not yet a spatial PDE or continuum Laplacian.

leftNeighbor :
  SPTI.ShiftPressurePoint →
  SPTI.ShiftPressurePoint
leftNeighbor SPTI.shiftStartPoint = SPTI.shiftStartPoint
leftNeighbor SPTI.shiftNextPoint = SPTI.shiftStartPoint
leftNeighbor SPTI.shiftHeldExitPoint = SPTI.shiftNextPoint

rightNeighbor :
  SPTI.ShiftPressurePoint →
  SPTI.ShiftPressurePoint
rightNeighbor SPTI.shiftStartPoint = SPTI.shiftNextPoint
rightNeighbor SPTI.shiftNextPoint = SPTI.shiftHeldExitPoint
rightNeighbor SPTI.shiftHeldExitPoint = SPTI.shiftHeldExitPoint

ShiftWaveField : Set
ShiftWaveField = SPTI.ShiftPressurePoint → SDWS.DiscreteWave

shiftSpatialLaplacian :
  ShiftWaveField →
  SPTI.ShiftPressurePoint →
  SDWS.DiscreteWave
shiftSpatialLaplacian wf s =
  SDWS.waveAdd
    (wf (leftNeighbor s))
    (SDWS.waveAdd
      (wf (rightNeighbor s))
      (SDWS.scaleWave (-[1+ 1 ]) (wf s)))

record ShiftSpatialLaplacianPackage : Set₁ where
  field
    Field : Set
    sample :
      Field → SPTI.ShiftPressurePoint → SDWS.DiscreteWave
    laplacian :
      Field → SPTI.ShiftPressurePoint → SDWS.DiscreteWave
    nonClaimBoundary : List String

shiftSpatialLaplacianPackage :
  ShiftSpatialLaplacianPackage
shiftSpatialLaplacianPackage =
  record
    { Field = ShiftWaveField
    ; sample = λ wf s → wf s
    ; laplacian = shiftSpatialLaplacian
    ; nonClaimBoundary =
        "Finite three-point spatial Laplacian only"
        ∷ "Boundary behavior uses reflected/Neumann-style endpoints"
        ∷ "No continuum spatial derivative or PDE claim is implied"
        ∷ []
    }
