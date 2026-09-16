module DASHI.Cognition.PNF.FibreNaturalDeltaInverseLimitExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.FibreNaturalDeltaTransportExact as Natural
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Topology.TetrationalGateField as Gate

------------------------------------------------------------------------
-- NATURAL DELTAS ACT ON INVERSE-LIMIT POINTS
--
-- A FibreTowerNaturalDelta already owns the levelwise update and projection-
-- naturality law.  An InverseLimitPoint already owns coherence of the state
-- family.  The only additional datum needed to update the entire inverse-limit
-- point is a coherent family of level deltas.
------------------------------------------------------------------------

record CoherentDeltaFamily
    (tower : Tower.FibreTower)
    (deltaSystem : Natural.FibreTowerNaturalDelta tower) : Set₁ where
  constructor coherent-delta-family
  field
    deltaAt : (level : Nat) → Natural.LevelDelta deltaSystem level
    deltaCoherent :
      (level : Nat) →
      Natural.projectDelta deltaSystem level (deltaAt (suc level))
      ≡ deltaAt level

open CoherentDeltaFamily public

applyCoherentDeltaToInverseLimit :
  ∀ {tower : Tower.FibreTower}
    (deltaSystem : Natural.FibreTowerNaturalDelta tower) →
  Tower.InverseLimitPoint tower →
  CoherentDeltaFamily tower deltaSystem →
  Tower.InverseLimitPoint tower
applyCoherentDeltaToInverseLimit deltaSystem point family = record
  { Tower.stateAt = λ level →
      Natural.applyLevel deltaSystem level
        (Tower.stateAt point level)
        (deltaAt family level)
  ; Tower.coherent = λ level →
      trans
        (Natural.projectionNaturality deltaSystem level
          (Tower.stateAt point (suc level))
          (deltaAt family (suc level)))
        (trans
          (cong
            (λ state →
              Natural.applyLevel deltaSystem level state
                (Natural.projectDelta deltaSystem level
                  (deltaAt family (suc level))))
            (Tower.coherent point level))
          (cong
            (Natural.applyLevel deltaSystem level (Tower.stateAt point level))
            (deltaCoherent family level)))
  }

------------------------------------------------------------------------
-- Exact identity-delta specimen on the repository's recursive phase tower.
------------------------------------------------------------------------

identityTowerDelta :
  Natural.FibreTowerNaturalDelta Tower.recursivePhaseTower
identityTowerDelta = record
  { Natural.LevelDelta = λ _ → ⊤
  ; Natural.applyLevel = λ _ state _ → state
  ; Natural.projectDelta = λ _ _ → tt
  ; Natural.projectionNaturality = λ _ _ _ → refl
  }

identityDeltaFamily :
  CoherentDeltaFamily Tower.recursivePhaseTower identityTowerDelta
identityDeltaFamily = coherent-delta-family
  (λ _ → tt)
  (λ _ → refl)

canonicalZeroUpdated : Tower.InverseLimitPoint Tower.recursivePhaseTower
canonicalZeroUpdated =
  applyCoherentDeltaToInverseLimit
    identityTowerDelta
    Tower.canonicalZeroInverseLimit
    identityDeltaFamily

canonicalZeroUpdatedRemainsCoherent :
  (level : Nat) →
  Tower.project Tower.recursivePhaseTower level
    (Tower.stateAt canonicalZeroUpdated (suc level))
  ≡ Tower.stateAt canonicalZeroUpdated level
canonicalZeroUpdatedRemainsCoherent = Tower.coherent canonicalZeroUpdated

canonicalZeroUpdateIsPointwiseIdentity :
  (level : Nat) →
  Tower.stateAt canonicalZeroUpdated level
  ≡ Tower.stateAt Tower.canonicalZeroInverseLimit level
canonicalZeroUpdateIsPointwiseIdentity level = refl

------------------------------------------------------------------------
-- Refinement/update does not itself open a tower level.
------------------------------------------------------------------------

deltaUpdateDoesNotOpenTowerLevel :
  Gate.refineWithinChart ≡ Gate.openTowerLevel → ⊥
deltaUpdateDoesNotOpenTowerLevel ()

deltaUpdateDoesNotIncreaseFibreDimension :
  Gate.refineWithinChart ≡ Gate.increaseFibreDimension → ⊥
deltaUpdateDoesNotIncreaseFibreDimension ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FibreNaturalDeltaInverseLimitBoundary : Set where
  constructor fibre-natural-delta-inverse-limit-boundary
  field
    coherentStateFamilyOwnedByInverseLimit : Bool
    coherentDeltaFamilyIsIndependentObligation : Bool
    projectionNaturalityReused : Bool
    levelwiseDeltaPreservesInverseLimitCoherence : Bool
    updateRequiresWholeTowerReconstruction : Bool
    updateRequiresWholeTowerReconstructionIsFalse :
      updateRequiresWholeTowerReconstruction ≡ false
    deltaUpdateAutomaticallyOpensTowerLevel : Bool
    deltaUpdateAutomaticallyOpensTowerLevelIsFalse :
      deltaUpdateAutomaticallyOpensTowerLevel ≡ false
    deltaUpdateAutomaticallyIncreasesFibreDimension : Bool
    deltaUpdateAutomaticallyIncreasesFibreDimensionIsFalse :
      deltaUpdateAutomaticallyIncreasesFibreDimension ≡ false
    recursivePhaseRefinementEqualsLiteralTetration : Bool
    recursivePhaseRefinementEqualsLiteralTetrationIsFalse :
      recursivePhaseRefinementEqualsLiteralTetration ≡ false
    boundaryNote : String

open FibreNaturalDeltaInverseLimitBoundary public

canonicalFibreNaturalDeltaInverseLimitBoundary :
  FibreNaturalDeltaInverseLimitBoundary
canonicalFibreNaturalDeltaInverseLimitBoundary =
  fibre-natural-delta-inverse-limit-boundary
    true
    true
    true
    true
    false refl
    false refl
    false refl
    false refl
    "A coherent family of natural deltas acts levelwise on an existing inverse-limit point and remains coherent by projection naturality. This updates the tower state without reconstructing the whole carrier and without identifying local refinement, fibre-dimension lift, tower opening, or literal ternary tetration."
