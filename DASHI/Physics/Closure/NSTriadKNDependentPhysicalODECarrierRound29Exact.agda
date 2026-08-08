module DASHI.Physics.Closure.NSTriadKNDependentPhysicalODECarrierRound29Exact where

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
-- The ODE is defined on the dependent physical carrier itself. Once a raw
-- finite vector field commutes with the physical selector, its output carries
-- Leray, Fourier-reality and centering proofs by construction. Downstream
-- trajectories therefore cannot contain inadmissible states accidentally.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNCommutingPhysicalCarrierSelectorRound28Exact as Selector

record SelectorEquivariantVectorField
    {level : Level}
    {State : Set level}
    (selectors : Selector.CommutingPhysicalSelectors State) :
    Set (lsuc level) where
  field
    rawVectorField : State → State
    commutesWithPhysicalSelector : ∀ state →
      rawVectorField (Selector.physicalSelector selectors state)
      ≡ Selector.physicalSelector selectors (rawVectorField state)

open SelectorEquivariantVectorField public

outputIsPhysicalSelectorFixed :
  ∀ {level} {State : Set level}
    {selectors : Selector.CommutingPhysicalSelectors State}
    (field : SelectorEquivariantVectorField selectors)
    (carrier : Selector.PhysicalCarrier selectors) →
  Selector.physicalSelector selectors
    (rawVectorField field (Selector.selectedState carrier))
  ≡ rawVectorField field (Selector.selectedState carrier)
outputIsPhysicalSelectorFixed {selectors = selectors} field carrier =
  trans
    (sym
      (commutesWithPhysicalSelector field
        (Selector.selectedState carrier)))
    (cong
      (rawVectorField field)
      (Selector.physicalSelectorFixesCarrier carrier))

physicalVectorField :
  ∀ {level} {State : Set level}
    {selectors : Selector.CommutingPhysicalSelectors State} →
  SelectorEquivariantVectorField selectors →
  Selector.PhysicalCarrier selectors →
  Selector.PhysicalCarrier selectors
physicalVectorField {selectors = selectors} field carrier =
  Selector.physical-carrier output lerayProof realityProof centerProof
  where
  output = rawVectorField field (Selector.selectedState carrier)

  outputFixed :
    Selector.physicalSelector selectors output ≡ output
  outputFixed = outputIsPhysicalSelectorFixed field carrier

  lerayProof :
    Selector.leray selectors output ≡ output
  lerayProof =
    trans
      (cong (Selector.leray selectors) (sym outputFixed))
      (trans
        (Selector.selectedStateLerayFixed selectors output)
        outputFixed)

  realityProof :
    Selector.reality selectors output ≡ output
  realityProof =
    trans
      (cong (Selector.reality selectors) (sym outputFixed))
      (trans
        (Selector.selectedStateRealityFixed selectors output)
        outputFixed)

  centerProof :
    Selector.center selectors output ≡ output
  centerProof =
    trans
      (cong (Selector.center selectors) (sym outputFixed))
      (trans
        (Selector.selectedStateCentered selectors output)
        outputFixed)

physicalVectorFieldErasesToRaw :
  ∀ {level} {State : Set level}
    {selectors : Selector.CommutingPhysicalSelectors State}
    (field : SelectorEquivariantVectorField selectors)
    (carrier : Selector.PhysicalCarrier selectors) →
  Selector.selectedState (physicalVectorField field carrier)
  ≡ rawVectorField field (Selector.selectedState carrier)
physicalVectorFieldErasesToRaw field carrier = refl

record DependentPhysicalTrajectory
    {timeLevel stateLevel : Level}
    (Time : Set timeLevel)
    {State : Set stateLevel}
    (selectors : Selector.CommutingPhysicalSelectors State)
    (field : SelectorEquivariantVectorField selectors) :
    Set (lsuc (timeLevel ⊔ stateLevel)) where
  field
    stateAt : Time → Selector.PhysicalCarrier selectors
    derivativeAt : Time → Selector.PhysicalCarrier selectors
    derivativeEqualsVectorField : ∀ time →
      derivativeAt time ≡ physicalVectorField field (stateAt time)

open DependentPhysicalTrajectory public

rawStateAt :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    {selectors : Selector.CommutingPhysicalSelectors State}
    {field : SelectorEquivariantVectorField selectors} →
  DependentPhysicalTrajectory Time selectors field →
  Time → State
rawStateAt trajectory time =
  Selector.selectedState (stateAt trajectory time)

rawDerivativeAt :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel}
    {selectors : Selector.CommutingPhysicalSelectors State}
    {field : SelectorEquivariantVectorField selectors} →
  DependentPhysicalTrajectory Time selectors field →
  Time → State
rawDerivativeAt trajectory time =
  Selector.selectedState (derivativeAt trajectory time)

dependentPhysicalODECarrierClosed : Bool
dependentPhysicalODECarrierClosed = true

literalNavierStokesVectorFieldEquivarianceClosed : Bool
literalNavierStokesVectorFieldEquivarianceClosed = false

repositoryRealPicardLindelofClosed : Bool
repositoryRealPicardLindelofClosed = false

dependentPhysicalODECarrierClosedIsTrue :
  dependentPhysicalODECarrierClosed ≡ true
dependentPhysicalODECarrierClosedIsTrue = refl

literalNavierStokesVectorFieldEquivarianceClosedIsFalse :
  literalNavierStokesVectorFieldEquivarianceClosed ≡ false
literalNavierStokesVectorFieldEquivarianceClosedIsFalse = refl
