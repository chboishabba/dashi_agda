module DASHI.Physics.Plasma.ToroidalZeroBounceAdmissibleConeSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Physics.Plasma.ToroidalConstantMagnitudeHybridABCExact as ABC
import DASHI.Physics.Plasma.TriadicPhaseFourierProjectorExact as Projector
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- ADMISSIBLE-CONE SEARCH FOR THE ZERO-BOUNCE TOROIDAL DESIGN PROGRAMME
--
-- Ambient optimisation is not the search object.  A move must first lie in the
-- proof-bearing admissible transition cone: preserve the declared hard physics
-- invariants, lie in the tangent/nullspace of active equalities, respect active
-- one-sided inequalities, and remain inside the selected C_(3^n) spectral chart.
------------------------------------------------------------------------

record ToroidalDesignSearchState
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor toroidal-design-search-state
  field
    abcBalance : Set
    zeroBounce : ZeroBounce.ZeroBounceReceipt population
    divergenceFreeReceipt : Set
    nestedFluxSurfaceReceipt : Set
    triadicSpectralReceipt : Set
    finiteOrbitWidthReceipt : Set
    energeticParticleReceipt : Set
    stateReference : String

open ToroidalDesignSearchState public

record LinearizedAdmissibleConeReceipt : Set₁ where
  constructor linearized-admissible-cone-receipt
  field
    AmbientDirection : Set
    equalityJacobianReceipt : Set
    tangentNullspace : AmbientDirection → Set
    activeInequalityCone : AmbientDirection → Set
    triadicSpectralSubspace : AmbientDirection → Set
    preservesHardPhysicsToDeclaredOrder : AmbientDirection → Set
    coneReference : String

open LinearizedAdmissibleConeReceipt public

AdmissibleDirection :
  LinearizedAdmissibleConeReceipt →
  AmbientDirection → Set
AdmissibleDirection cone direction =
  tangentNullspace cone direction
  × activeInequalityCone cone direction
  × triadicSpectralSubspace cone direction
  × preservesHardPhysicsToDeclaredOrder cone direction

record ToroidalAdmissibleConeSearch
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor toroidal-admissible-cone-search
  field
    State : Set
    decodeState : State → ToroidalDesignSearchState population
    Move Parameter : Set
    system : Transition.AdmissibleTransitionSystem
    sameStateCarrierReceipt : Transition.State system ≡ State
    coneAtState : State → LinearizedAdmissibleConeReceipt
    everyEnabledMoveHasAdmissibleDirectionReceipt : Set
    abcConstraintNullspaceReceipt : Set
    c3nQuotientBeforeParetoReceipt : Set
    searchReference : String

open ToroidalAdmissibleConeSearch public

record AdmissibleConeSearchBoundary : Set where
  constructor admissible-cone-search-boundary
  field
    hardConstraintsMayBeReplacedByPenaltyTerms : Bool
    hardConstraintsMayBeReplacedByPenaltyTermsIsFalse :
      hardConstraintsMayBeReplacedByPenaltyTerms ≡ false

    tangentNullspaceSearchCompressesAmbientSearch : Bool
    tangentNullspaceSearchCompressesAmbientSearchIsTrue :
      tangentNullspaceSearchCompressesAmbientSearch ≡ true

    c3nProjectionMayBeAppliedBeforeParetoSearch : Bool
    c3nProjectionMayBeAppliedBeforeParetoSearchIsTrue :
      c3nProjectionMayBeAppliedBeforeParetoSearch ≡ true

    numericalNullspaceReceiptIsKernelProof : Bool
    numericalNullspaceReceiptIsKernelProofIsFalse :
      numericalNullspaceReceiptIsKernelProof ≡ false

canonicalAdmissibleConeSearchBoundary : AdmissibleConeSearchBoundary
canonicalAdmissibleConeSearchBoundary =
  admissible-cone-search-boundary
    false refl
    true refl
    true refl
    false refl

pythonReplayReference : String
pythonReplayReference =
  "scripts/admissible_cone_routeC_search.py / scripts/test_admissible_cone_routeC_search.py"
