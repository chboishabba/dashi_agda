module DASHI.Physics.ShiftWaveRefinementLevel where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftSpatialLaplacian as SSL
open import DASHI.Physics.ShiftWaveRefinementHierarchy as SWRH

------------------------------------------------------------------------
-- Theorem-thin refinement-family abstraction over the current concrete
-- 3 -> 5 hierarchy.
--
-- This does not claim a scaling limit or a recursive construction theorem.
-- It only packages the current hierarchy as one named refinement level pair
-- so later finite steps like 5 -> 9 or 9 -> 17 can reuse the same surface.

record ShiftWaveRefinementLevel : Setω where
  field
    levelLabel : String
    State : Set
    Field : Set
    sample :
      Field → State → SDWS.DiscreteWave
    laplacian :
      Field → State → SDWS.DiscreteWave
    nonClaimBoundary : List String

record ShiftWaveRefinementFamily : Setω where
  field
    coarseLevel : ShiftWaveRefinementLevel
    fineLevel : ShiftWaveRefinementLevel

    embed :
      ShiftWaveRefinementLevel.State coarseLevel →
      ShiftWaveRefinementLevel.State fineLevel

    project :
      ShiftWaveRefinementLevel.State fineLevel →
      ShiftWaveRefinementLevel.State coarseLevel

    liftField :
      ShiftWaveRefinementLevel.Field coarseLevel →
      ShiftWaveRefinementLevel.Field fineLevel

    laplacianCompatibility : Set
    refinementBoundary : List String

shiftWaveRefinementLevel3 : ShiftWaveRefinementLevel
shiftWaveRefinementLevel3 =
  record
    { levelLabel = "shift-wave-level-3"
    ; State = SPTI.ShiftPressurePoint
    ; Field = SSL.ShiftWaveField
    ; sample = λ wf s → wf s
    ; laplacian = SSL.shiftSpatialLaplacian
    ; nonClaimBoundary =
        "Finite 3-point wave level only"
        ∷ "sample and Laplacian stay on the current three-point carrier"
        ∷ "No continuum or recursive family theorem is implied"
        ∷ []
    }

shiftWaveRefinementLevel5 : ShiftWaveRefinementLevel
shiftWaveRefinementLevel5 =
  record
    { levelLabel = "shift-wave-level-5"
    ; State = SWRH.ShiftPressurePoint5
    ; Field = SWRH.ShiftWaveField5
    ; sample = λ wf s → wf s
    ; laplacian = SWRH.shiftSpatialLaplacian5
    ; nonClaimBoundary =
        "Finite 5-point wave level only"
        ∷ "endpoints remain reflected boundary shadows on the current carrier"
        ∷ "No continuum or recursive family theorem is implied"
        ∷ []
    }

shiftWaveRefinementFamily3to5 : ShiftWaveRefinementFamily
shiftWaveRefinementFamily3to5 =
  record
    { coarseLevel = shiftWaveRefinementLevel3
    ; fineLevel = shiftWaveRefinementLevel5
    ; embed = SWRH.embed3to5
    ; project = SWRH.project5to3
    ; liftField = SWRH.liftField3to5
    ; laplacianCompatibility = SWRH.LaplacianConsistency3to5
    ; refinementBoundary =
        "Finite refinement-family package only"
        ∷ "current family contains one concrete 3 -> 5 step"
        ∷ "later 5 -> 9 or 9 -> 17 steps may reuse the same surface"
        ∷ "No recursive refinement theorem or scaling-limit claim is implied"
        ∷ []
    }
