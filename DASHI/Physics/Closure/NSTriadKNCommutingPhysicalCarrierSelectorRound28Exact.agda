module DASHI.Physics.Closure.NSTriadKNCommutingPhysicalCarrierSelectorRound28Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Package incompressibility, Fourier reality and centering as three commuting
-- idempotent selectors.  Their composite
--
--   Phys = Center o Reality o Leray
--
-- is proved idempotent, its image is fixed by every constituent selector, and
-- it fixes every state already satisfying all three physical invariants.
-- This is the exact dependent-carrier theorem needed before instantiating the
-- literal finite Galerkin vector field.  The concrete Leray/reality/centering
-- operators and nonlinear commutation theorem remain separate physical data.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record CommutingPhysicalSelectors
    {level : Level}
    (State : Set level) : Set (lsuc level) where
  field
    leray reality center : State → State

    lerayIdempotent : ∀ state →
      leray (leray state) ≡ leray state

    realityIdempotent : ∀ state →
      reality (reality state) ≡ reality state

    centerIdempotent : ∀ state →
      center (center state) ≡ center state

    lerayRealityCommute : ∀ state →
      leray (reality state) ≡ reality (leray state)

    lerayCenterCommute : ∀ state →
      leray (center state) ≡ center (leray state)

    realityCenterCommute : ∀ state →
      reality (center state) ≡ center (reality state)

open CommutingPhysicalSelectors public

physicalSelector :
  ∀ {level} {State : Set level} →
  CommutingPhysicalSelectors State → State → State
physicalSelector selectors state =
  center selectors (reality selectors (leray selectors state))

selectedStateLerayFixed :
  ∀ {level} {State : Set level}
    (selectors : CommutingPhysicalSelectors State)
    (state : State) →
  leray selectors (physicalSelector selectors state)
  ≡ physicalSelector selectors state
selectedStateLerayFixed selectors state =
  trans
    (lerayCenterCommute selectors
      (reality selectors (leray selectors state)))
    (trans
      (cong (center selectors)
        (lerayRealityCommute selectors (leray selectors state)))
      (cong
        (λ selected → center selectors (reality selectors selected))
        (lerayIdempotent selectors state)))

selectedStateRealityFixed :
  ∀ {level} {State : Set level}
    (selectors : CommutingPhysicalSelectors State)
    (state : State) →
  reality selectors (physicalSelector selectors state)
  ≡ physicalSelector selectors state
selectedStateRealityFixed selectors state =
  trans
    (realityCenterCommute selectors
      (reality selectors (leray selectors state)))
    (cong (center selectors)
      (realityIdempotent selectors (leray selectors state)))

selectedStateCentered :
  ∀ {level} {State : Set level}
    (selectors : CommutingPhysicalSelectors State)
    (state : State) →
  center selectors (physicalSelector selectors state)
  ≡ physicalSelector selectors state
selectedStateCentered selectors state =
  centerIdempotent selectors
    (reality selectors (leray selectors state))

record PhysicalCarrier
    {level : Level}
    {State : Set level}
    (selectors : CommutingPhysicalSelectors State) : Set level where
  constructor physical-carrier
  field
    selectedState : State
    lerayFixed :
      leray selectors selectedState ≡ selectedState
    realityFixed :
      reality selectors selectedState ≡ selectedState
    centered :
      center selectors selectedState ≡ selectedState

open PhysicalCarrier public

selectPhysicalCarrier :
  ∀ {level} {State : Set level}
    (selectors : CommutingPhysicalSelectors State) →
  State → PhysicalCarrier selectors
selectPhysicalCarrier selectors state =
  physical-carrier
    (physicalSelector selectors state)
    (selectedStateLerayFixed selectors state)
    (selectedStateRealityFixed selectors state)
    (selectedStateCentered selectors state)

physicalSelectorFixesCarrier :
  ∀ {level} {State : Set level}
    {selectors : CommutingPhysicalSelectors State}
    (carrier : PhysicalCarrier selectors) →
  physicalSelector selectors (selectedState carrier)
  ≡ selectedState carrier
physicalSelectorFixesCarrier {selectors = selectors} carrier =
  trans
    (cong
      (λ state → center selectors (reality selectors state))
      (lerayFixed carrier))
    (trans
      (cong (center selectors) (realityFixed carrier))
      (centered carrier))

physicalSelectorIdempotent :
  ∀ {level} {State : Set level}
    (selectors : CommutingPhysicalSelectors State)
    (state : State) →
  physicalSelector selectors (physicalSelector selectors state)
  ≡ physicalSelector selectors state
physicalSelectorIdempotent selectors state =
  physicalSelectorFixesCarrier (selectPhysicalCarrier selectors state)

physicalCarrierSelectorTheoremClosed : Bool
physicalCarrierSelectorTheoremClosed = true

concreteNavierStokesSelectorsInstantiated : Bool
concreteNavierStokesSelectorsInstantiated = false

fullPhysicalVectorFieldCommutesWithSelector : Bool
fullPhysicalVectorFieldCommutesWithSelector = false

physicalCarrierSelectorTheoremClosedIsTrue :
  physicalCarrierSelectorTheoremClosed ≡ true
physicalCarrierSelectorTheoremClosedIsTrue = refl

concreteNavierStokesSelectorsInstantiatedIsFalse :
  concreteNavierStokesSelectorsInstantiated ≡ false
concreteNavierStokesSelectorsInstantiatedIsFalse = refl

fullPhysicalVectorFieldCommutesWithSelectorIsFalse :
  fullPhysicalVectorFieldCommutesWithSelector ≡ false
fullPhysicalVectorFieldCommutesWithSelectorIsFalse = refl
