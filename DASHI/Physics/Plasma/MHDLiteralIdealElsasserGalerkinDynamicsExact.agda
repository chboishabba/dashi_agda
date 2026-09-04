module DASHI.Physics.Plasma.MHDLiteralIdealElsasserGalerkinDynamicsExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Plasma.MHDElsasserProjectedNonlinearCoefficientExact as Projected
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State

------------------------------------------------------------------------
-- LITERAL IDEAL ELSASSER GALERKIN DYNAMICS
--
-- The historical owner is named VelocityGalerkinLaws, but the primitive
-- ordered interaction is application-neutral in its two vector arguments.
-- Ideal incompressible MHD is therefore instantiated by opposite Elsasser
-- transport and same-species target fields on the exact C3 Fourier carrier.
------------------------------------------------------------------------

plusOrderedInteraction :
  forall {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} ->
  C3.ModeInverseSquare F E ->
  State.IdealElsasserFourierState F E ->
  Z3.FourierMode -> Z3.FourierMode -> Z3.FourierMode -> C3.Complex3 F
plusOrderedInteraction {F = F} {E = E} I state k p q =
  Signed.orderedVelocityInteraction
    (C3.complex3VelocityGalerkinLaws F E I)
    k p q
    (State.zMinus state p)
    (State.zPlus state q)

minusOrderedInteraction :
  forall {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} ->
  C3.ModeInverseSquare F E ->
  State.IdealElsasserFourierState F E ->
  Z3.FourierMode -> Z3.FourierMode -> Z3.FourierMode -> C3.Complex3 F
minusOrderedInteraction {F = F} {E = E} I state k p q =
  Signed.orderedVelocityInteraction
    (C3.complex3VelocityGalerkinLaws F E I)
    k p q
    (State.zPlus state p)
    (State.zMinus state q)

plusInteractionIsProjectedElsasser :
  forall {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (k p q : Z3.FourierMode) ->
  plusOrderedInteraction I state k p q
  ==
  Projected.elsasserOrderedInteraction
    E I k q (State.zMinus state p) (State.zPlus state q)
plusInteractionIsProjectedElsasser I state k p q = refl

minusInteractionIsProjectedElsasser :
  forall {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (k p q : Z3.FourierMode) ->
  minusOrderedInteraction I state k p q
  ==
  Projected.elsasserOrderedInteraction
    E I k q (State.zPlus state p) (State.zMinus state q)
minusInteractionIsProjectedElsasser I state k p q = refl

record LiteralIdealElsasserGalerkinBoundary : Set where
  constructor literal-ideal-elsasser-galerkin-boundary
  field
    genericGalerkinPrimitiveReused : Bool
    genericGalerkinPrimitiveReusedIsTrue : genericGalerkinPrimitiveReused == true

    plusIsMinusTransportingPlus : Bool
    plusIsMinusTransportingPlusIsTrue : plusIsMinusTransportingPlus == true

    minusIsPlusTransportingMinus : Bool
    minusIsPlusTransportingMinusIsTrue : minusIsPlusTransportingMinus == true

    repoGalerkinToProjectedInteractionWeldOwned : Bool
    repoGalerkinToProjectedInteractionWeldOwnedIsTrue :
      repoGalerkinToProjectedInteractionWeldOwned == true

canonicalLiteralIdealElsasserGalerkinBoundary : LiteralIdealElsasserGalerkinBoundary
canonicalLiteralIdealElsasserGalerkinBoundary =
  literal-ideal-elsasser-galerkin-boundary true refl true refl true refl true refl
