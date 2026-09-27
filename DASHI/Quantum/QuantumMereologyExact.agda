{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set₁; Set₂)

import DASHI.Core.MereologyCoreExact as Classical
import DASHI.Core.ConsumerRelativeMereologyExact as Consumer
import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- BARE QUANTUM WORLD: carrier/state/Hamiltonian without subsystem structure.
------------------------------------------------------------------------

record BareQuantumWorld : Set₁ where
  field
    HilbertCarrier : Set
    State : Set
    Hamiltonian : Set
    carrierState : State → HilbertCarrier
    evolve : Hamiltonian → State → State

open BareQuantumWorld public

------------------------------------------------------------------------
-- A TPS is extra structure on the same bare world.
-- "Part" is therefore factorisation-relative rather than baked into Carrier.
------------------------------------------------------------------------

record TensorProductStructure (W : BareQuantumWorld) : Set₁ where
  field
    Subsystem : Set
    FactorIndex : Set

    subsystemAt : FactorIndex → Subsystem
    subsystemPartOfCarrier : Subsystem → Set

    ReconstructsCarrier : Set
    reconstruction : ReconstructsCarrier

    -- Entanglement/locality semantics are TPS-indexed.
    Entangled : State W → Subsystem → Subsystem → Set
    Interacts : Hamiltonian W → Subsystem → Subsystem → Set

open TensorProductStructure public

record EntanglementObservation
    (W : BareQuantumWorld)
    (T : TensorProductStructure W) : Set₁ where
  field
    state : State W
    left right : Subsystem T
    entangled : Entangled T state left right

open EntanglementObservation public

------------------------------------------------------------------------
-- Carroll/Singh-style preferred-factorisation criterion.
-- The criterion is separated from existence and uniqueness.
------------------------------------------------------------------------

record QuasiclassicalCriterion
    (W : BareQuantumWorld)
    (T : TensorProductStructure W) : Set₁ where
  field
    PointerState : Set
    pointerStateLivesIn : PointerState → State W → Set

    RobustAgainstEnvironment : PointerState → Set
    EntanglementGrowthControlled : PointerState → Set
    LocalizedAroundClassicalTrajectory : PointerState → Set

    selectedPointer :
      PointerState

    robust :
      RobustAgainstEnvironment selectedPointer

    controlledGrowth :
      EntanglementGrowthControlled selectedPointer

    localized :
      LocalizedAroundClassicalTrajectory selectedPointer

open QuasiclassicalCriterion public

record PreferredTPSCandidate (W : BareQuantumWorld) : Set₁ where
  field
    tps : TensorProductStructure W
    criterion : QuasiclassicalCriterion W tps

open PreferredTPSCandidate public

------------------------------------------------------------------------
-- TPS refinement is not identified with the classical partition lattice.
-- Any common refinement is explicit data; no canonical global meet is supplied.
------------------------------------------------------------------------

record TPSRefinementSpace (W : BareQuantumWorld) : Set₁ where
  field
    TPS : Set
    realizes : TPS → TensorProductStructure W
    Refines : TPS → TPS → Set

open TPSRefinementSpace public

record CommonTPSRefinement
    {W : BareQuantumWorld}
    (R : TPSRefinementSpace W)
    (left right : TPS R) : Set₁ where
  field
    common : TPS R
    refinesLeft : Refines R common left
    refinesRight : Refines R common right

open CommonTPSRefinement public

record CanonicalMeetAuthority
    {W : BareQuantumWorld}
    (R : TPSRefinementSpace W) : Set₁ where
  field
    meet : TPS R → TPS R → TPS R
    meetRefinesLeft :
      ∀ left right → Refines R (meet left right) left
    meetRefinesRight :
      ∀ left right → Refines R (meet left right) right

open CanonicalMeetAuthority public

------------------------------------------------------------------------
-- NON-COLLAPSE FIREWALLS
------------------------------------------------------------------------

record QuantumMereologyBoundary : Set where
  field
    bareCarrierSelectsUniqueTPS : Bool
    bareCarrierSelectsUniqueTPSIsFalse :
      bareCarrierSelectsUniqueTPS ≡ false

    HamiltonianAloneLocallyProvesUniqueTPS : Bool
    HamiltonianAloneLocallyProvesUniqueTPSIsFalse :
      HamiltonianAloneLocallyProvesUniqueTPS ≡ false

    entanglementIsFactorisationIndependent : Bool
    entanglementIsFactorisationIndependentIsFalse :
      entanglementIsFactorisationIndependent ≡ false

    TPSRefinementHasBuiltInGlobalMeet : Bool
    TPSRefinementHasBuiltInGlobalMeetIsFalse :
      TPSRefinementHasBuiltInGlobalMeet ≡ false

    selectedTPSAlreadyIsEmergentGeometry : Bool
    selectedTPSAlreadyIsEmergentGeometryIsFalse :
      selectedTPSAlreadyIsEmergentGeometry ≡ false

canonicalQuantumMereologyBoundary : QuantumMereologyBoundary
canonicalQuantumMereologyBoundary = record
  { bareCarrierSelectsUniqueTPS = false
  ; bareCarrierSelectsUniqueTPSIsFalse = refl
  ; HamiltonianAloneLocallyProvesUniqueTPS = false
  ; HamiltonianAloneLocallyProvesUniqueTPSIsFalse = refl
  ; entanglementIsFactorisationIndependent = false
  ; entanglementIsFactorisationIndependentIsFalse = refl
  ; TPSRefinementHasBuiltInGlobalMeet = false
  ; TPSRefinementHasBuiltInGlobalMeetIsFalse = refl
  ; selectedTPSAlreadyIsEmergentGeometry = false
  ; selectedTPSAlreadyIsEmergentGeometryIsFalse = refl
  }
