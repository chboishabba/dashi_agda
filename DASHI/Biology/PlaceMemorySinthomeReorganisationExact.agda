module DASHI.Biology.PlaceMemorySinthomeReorganisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Reasoning.SinthomeTypedStabilisation as Sinthome

------------------------------------------------------------------------
-- A finite place-memory witness: the remembered site and residual remain,
-- while compulsory action is replaced by a coherent choice among actions.
------------------------------------------------------------------------

data PlaceAccessState : Set where
  compulsoryFlightState : PlaceAccessState
  integratedChoiceState : PlaceAccessState
  erasedPlaceState : PlaceAccessState

Coherent : PlaceAccessState → Set
Coherent compulsoryFlightState = ⊥
Coherent integratedChoiceState = ⊤
Coherent erasedPlaceState = ⊤

ResidualPresent : Residual.ResidualLevel → PlaceAccessState → Set
ResidualPresent Residual.partial integratedChoiceState = ⊤
ResidualPresent residual state = ⊥

MemoryPreserved : PlaceAccessState → PlaceAccessState → Set
MemoryPreserved compulsoryFlightState integratedChoiceState = ⊤
MemoryPreserved state state' = ⊥

Equivalent : PlaceAccessState → PlaceAccessState → Set
Equivalent left right = left ≡ right

placeReorganisationPath : Sinthome.StabilisationPath
placeReorganisationPath = record
  { Sinthome.pathSteps =
      "approach site" ∷ "recognise cue" ∷ "retain residual" ∷ "expand action choice" ∷ []
  ; Sinthome.sourceVersion = "compulsory-flight map"
  ; Sinthome.targetVersion = "choice-bearing map"
  ; Sinthome.pathProvenance =
      "same site" ∷ "same remembered event" ∷ "new route relation" ∷ []
  ; Sinthome.pathReceipt = "psychogeographic non-erasing reorganisation"
  }

placeMemorySinthome :
  Sinthome.AdmissibleSinthome
    PlaceAccessState Coherent ResidualPresent MemoryPreserved Equivalent
placeMemorySinthome = record
  { Sinthome.before = compulsoryFlightState
  ; Sinthome.after = integratedChoiceState
  ; Sinthome.erasureCandidate = erasedPlaceState
  ; Sinthome.residual = Residual.partial
  ; Sinthome.path = placeReorganisationPath
  ; Sinthome.coherenceAfter = tt
  ; Sinthome.residualAfter = tt
  ; Sinthome.memoryFromBefore = tt
  ; Sinthome.notEquivalentToErasure = λ ()
  ; Sinthome.mode = Sinthome.sinthomaticIntegrationMode
  ; Sinthome.modeIsSinthomatic = refl
  ; Sinthome.stabilisationReceipt =
      "same site and residual; altered access/action topology"
  }

placeReorganisationRestoresCoherence : Coherent integratedChoiceState
placeReorganisationRestoresCoherence =
  Sinthome.sinthomeRestoresCoherence placeMemorySinthome

placeReorganisationRetainsResidual :
  ResidualPresent Residual.partial integratedChoiceState
placeReorganisationRetainsResidual =
  Sinthome.sinthomeRetainsResidual placeMemorySinthome

placeReorganisationPreservesMemory :
  MemoryPreserved compulsoryFlightState integratedChoiceState
placeReorganisationPreservesMemory =
  Sinthome.sinthomePreservesMemory placeMemorySinthome

placeReorganisationIsNotErasure :
  ¬ Equivalent integratedChoiceState erasedPlaceState
placeReorganisationIsNotErasure =
  Sinthome.sinthomeIsNotErasure placeMemorySinthome

record PlaceMemorySinthomeBoundary : Set where
  constructor placeMemorySinthomeBoundary
  field
    integrationEqualsForgettingPlace : Bool
    integrationEqualsForgettingPlaceIsFalse :
      integrationEqualsForgettingPlace ≡ false
    residualRetentionMeansCompulsoryActionRetained : Bool
    residualRetentionMeansCompulsoryActionRetainedIsFalse :
      residualRetentionMeansCompulsoryActionRetained ≡ false
    finiteWitnessIsClinicalCureTheorem : Bool
    finiteWitnessIsClinicalCureTheoremIsFalse :
      finiteWitnessIsClinicalCureTheorem ≡ false

canonicalPlaceMemorySinthomeBoundary : PlaceMemorySinthomeBoundary
canonicalPlaceMemorySinthomeBoundary =
  placeMemorySinthomeBoundary false refl false refl false refl
