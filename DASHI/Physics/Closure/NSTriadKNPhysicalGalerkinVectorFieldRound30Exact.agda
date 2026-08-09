module DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinVectorFieldRound30Exact where

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
-- Close the type-theoretic part of the Round-29 finite-flow obstruction.  A
-- literal Galerkin producer is required to return, for every positive reality
-- orbit, a transverse coefficient at a nonzero mode.  The negative orbit is
-- then reconstructed canonically by conjugation by the existing dependent
-- state.  Consequently the complete viscous-plus-quadratic field has type
--
--   ReconstructedPhysicalState F E -> ReconstructedPhysicalState F E,
--
-- and lifts to the dependent physical ODE carrier.  No later theorem can
-- insert a non-transverse, non-real or zero-mode derivative.  Construction of
-- the literal finite-triad producer remains a named physical obligation.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNCommutingPhysicalCarrierSelectorRound28Exact as Selector
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNDependentPhysicalODECarrierRound29Exact as ODE

record LiteralPhysicalGalerkinProducer
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set (lsuc r) where
  field
    outputCoefficients :
      State.ReconstructedPhysicalState F E →
      List (Phase.TransverseModeCoefficient F E)

    outputModesNonzero :
      (state : State.ReconstructedPhysicalState F E) →
      (coefficient : Phase.TransverseModeCoefficient F E) →
      State._∈_ coefficient (outputCoefficients state) →
      Z3.NonZeroMode (Phase.coefficientMode coefficient)

    LiteralRawCoefficient :
      State.ReconstructedPhysicalState F E →
      Phase.TransverseModeCoefficient F E → Set r

    outputIsLiteralViscousPlusQuadratic :
      (state : State.ReconstructedPhysicalState F E) →
      (coefficient : Phase.TransverseModeCoefficient F E) →
      State._∈_ coefficient (outputCoefficients state) →
      LiteralRawCoefficient state coefficient

open LiteralPhysicalGalerkinProducer public

physicalGalerkinVectorField :
  ∀ {r}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  LiteralPhysicalGalerkinProducer F E →
  State.ReconstructedPhysicalState F E →
  State.ReconstructedPhysicalState F E
physicalGalerkinVectorField producer state =
  State.reconstructed-physical-state
    (outputCoefficients producer state)
    (outputModesNonzero producer state)

physicalGalerkinOutputCoefficientTransverse :
  ∀ {r}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (producer : LiteralPhysicalGalerkinProducer F E)
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  State._∈_ coefficient
    (State.positiveOrbitCoefficients
      (physicalGalerkinVectorField producer state)) →
  C3.bilinearDot3
    (C3.modeVector E (Phase.coefficientMode coefficient))
    (Phase.coefficientValue coefficient)
  ≡ C3.complexZero F
physicalGalerkinOutputCoefficientTransverse producer state coefficient member =
  Phase.coefficientTransverse coefficient

physicalGalerkinOutputNegativeCoefficientTransverse :
  ∀ {r}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (producer : LiteralPhysicalGalerkinProducer F E)
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  State._∈_ coefficient
    (State.positiveOrbitCoefficients
      (physicalGalerkinVectorField producer state)) →
  C3.bilinearDot3
    (C3.modeVector E (Phase.reconstructedNegativeMode coefficient))
    (Phase.reconstructedNegativeValue coefficient)
  ≡ C3.complexZero F
physicalGalerkinOutputNegativeCoefficientTransverse
    producer state coefficient member =
  State.reconstructedNegativeCoefficientTransverse coefficient

physicalGalerkinOutputPositiveModeNonzero :
  ∀ {r}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (producer : LiteralPhysicalGalerkinProducer F E)
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  State._∈_ coefficient
    (State.positiveOrbitCoefficients
      (physicalGalerkinVectorField producer state)) →
  Z3.NonZeroMode (Phase.coefficientMode coefficient)
physicalGalerkinOutputPositiveModeNonzero producer state =
  outputModesNonzero producer state

physicalGalerkinOutputNegativeModeNonzero :
  ∀ {r}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (producer : LiteralPhysicalGalerkinProducer F E)
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  State._∈_ coefficient
    (State.positiveOrbitCoefficients
      (physicalGalerkinVectorField producer state)) →
  Z3.NonZeroMode (Phase.reconstructedNegativeMode coefficient)
physicalGalerkinOutputNegativeModeNonzero producer state coefficient member =
  State.reconstructedNegativeModeNonzero
    (physicalGalerkinVectorField producer state) coefficient member

physicalGalerkinSelectorEquivariant :
  ∀ {r}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  LiteralPhysicalGalerkinProducer F E →
  ODE.SelectorEquivariantVectorField
    (State.reconstructedPhysicalSelectors F E)
physicalGalerkinSelectorEquivariant producer = record
  { ODE.SelectorEquivariantVectorField.rawVectorField =
      physicalGalerkinVectorField producer
  ; ODE.SelectorEquivariantVectorField.commutesWithPhysicalSelector =
      λ state → refl
  }

physicalGalerkinDependentVectorField :
  ∀ {r}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  LiteralPhysicalGalerkinProducer F E →
  Selector.PhysicalCarrier
    (State.reconstructedPhysicalSelectors F E) →
  Selector.PhysicalCarrier
    (State.reconstructedPhysicalSelectors F E)
physicalGalerkinDependentVectorField producer =
  ODE.physicalVectorField (physicalGalerkinSelectorEquivariant producer)

fullGalerkinVectorFieldMapsReconstructedState : Bool
fullGalerkinVectorFieldMapsReconstructedState = true

fullGalerkinVectorFieldMapsReconstructedStateIsTrue :
  fullGalerkinVectorFieldMapsReconstructedState ≡ true
fullGalerkinVectorFieldMapsReconstructedStateIsTrue = refl

literalFiniteTriadProducerConstructed : Bool
literalFiniteTriadProducerConstructed = false

literalFiniteTriadProducerConstructedIsFalse :
  literalFiniteTriadProducerConstructed ≡ false
literalFiniteTriadProducerConstructedIsFalse = refl
