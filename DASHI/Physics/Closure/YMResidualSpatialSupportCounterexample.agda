module DASHI.Physics.Closure.YMResidualSpatialSupportCounterexample where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (_∷_; [])

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMEffectiveActionSpatialOnlyBridge as Bridge

------------------------------------------------------------------------
-- Sprint 82 follow-up: why the four residual-support evidence objects cannot
-- be implemented unconditionally over the current PolymerIn relation.
--
-- PolymerIn currently carries only an identifier.  It does not require the
-- polymer to be the polymer of an actual residual effective-action term, and
-- it does not relate support links to term link-use.  Therefore a temporal-link
-- polymer can be given a PolymerIn witness.  Any unconditional residual spatial
-- support evidence would then force temporal == spatial.

temporalNotSpatial :
  Support.temporal ≡ Support.spatial →
  ⊥
temporalNotSpatial ()

temporalLinkCounterexample : Support.Link
temporalLinkCounterexample =
  Support.link "temporal-counterexample-link" Support.temporal

temporalPolymerCounterexample : Support.Polymer
temporalPolymerCounterexample =
  Support.polymer
    "temporal-counterexample-polymer"
    (temporalLinkCounterexample ∷ [])

emptyEffectiveActionCounterexample : Support.BalabanEffectiveAction
emptyEffectiveActionCounterexample =
  Support.balabanEffectiveAction "counterexample-scale" []

arbitraryPolymerInCounterexample :
  Support.PolymerIn
    emptyEffectiveActionCounterexample
    temporalPolymerCounterexample
arbitraryPolymerInCounterexample =
  Support.polymerIn "current-polymer-in-has-no-term-resolver"

temporalPolymerSpatialSupportContradiction :
  Support.SpatialSupport temporalPolymerCounterexample →
  ⊥
temporalPolymerSpatialSupportContradiction
  (Support.allSpatialCons temporalIsSpatial Support.allSpatialNil) =
  temporalNotSpatial temporalIsSpatial

unconditionalResidualSpatialSupportEvidenceImpossible :
  Bridge.ResidualEffectiveActionSpatialSupportEvidence →
  ⊥
unconditionalResidualSpatialSupportEvidenceImpossible evidence =
  temporalPolymerSpatialSupportContradiction
    (Bridge.ResidualEffectiveActionSpatialSupportEvidence.residualSpatialSupport
      evidence
      emptyEffectiveActionCounterexample
      temporalPolymerCounterexample
      arbitraryPolymerInCounterexample)

record CurrentPolymerInCounterexampleBoundary : Set₁ where
  field
    currentPolymerInAllowsTemporalSupportCounterexample :
      Bool
    currentPolymerInAllowsTemporalSupportCounterexampleIsTrue :
      currentPolymerInAllowsTemporalSupportCounterexample ≡ true
    unconditionalResidualSpatialSupportRefutedHere :
      Bridge.ResidualEffectiveActionSpatialSupportEvidence → ⊥
    clayYangMillsPromoted :
      Bool
    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

currentPolymerInCounterexampleBoundary :
  CurrentPolymerInCounterexampleBoundary
currentPolymerInCounterexampleBoundary =
  record
    { currentPolymerInAllowsTemporalSupportCounterexample = true
    ; currentPolymerInAllowsTemporalSupportCounterexampleIsTrue = refl
    ; unconditionalResidualSpatialSupportRefutedHere =
        unconditionalResidualSpatialSupportEvidenceImpossible
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedIsFalse = refl
    }
