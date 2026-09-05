module DASHI.Physics.Plasma.MHDLiteralIdealEnergyCrossHelicityTriadConservationExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNEnergyCancellationAssembly as Assembly
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State

------------------------------------------------------------------------
-- LITERAL IDEAL-MHD TRIAD INVARIANTS ON THE PROJECTED FOURIER C3 MODEL
------------------------------------------------------------------------

plusTriadVariation :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  Physical.PhysicalTriadIncidence →
  State.IdealElsasserFourierState F E →
  C3.Complex F
plusTriadVariation I tau state =
  let laws = State.plusTransferLaws I state in
  Assembly.add laws
    (Assembly.add laws
      (Assembly.orderedPairTransfer laws tau)
      (Assembly.orderedPairTransfer laws (Orbit.pEnergyLeg tau)))
    (Assembly.orderedPairTransfer laws (Orbit.qEnergyLeg tau))

minusTriadVariation :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  Physical.PhysicalTriadIncidence →
  State.IdealElsasserFourierState F E →
  C3.Complex F
minusTriadVariation I tau state =
  let laws = State.minusTransferLaws I state in
  Assembly.add laws
    (Assembly.add laws
      (Assembly.orderedPairTransfer laws tau)
      (Assembly.orderedPairTransfer laws (Orbit.pEnergyLeg tau)))
    (Assembly.orderedPairTransfer laws (Orbit.qEnergyLeg tau))

plusTriadVariationZero :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (state : State.IdealElsasserFourierState F E) →
  plusTriadVariation I tau state ≡ C3.complexZero F
plusTriadVariationZero = State.plusThreeLegPseudoEnergyCancellation

minusTriadVariationZero :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (state : State.IdealElsasserFourierState F E) →
  minusTriadVariation I tau state ≡ C3.complexZero F
minusTriadVariationZero = State.minusThreeLegPseudoEnergyCancellation

energyTriadVariation :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  Physical.PhysicalTriadIncidence →
  State.IdealElsasserFourierState F E →
  C3.Complex F
energyTriadVariation I tau state =
  C3.complexAdd
    (plusTriadVariation I tau state)
    (minusTriadVariation I tau state)

crossHelicityTriadVariation :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  Physical.PhysicalTriadIncidence →
  State.IdealElsasserFourierState F E →
  C3.Complex F
crossHelicityTriadVariation I tau state =
  C3.complexAdd
    (plusTriadVariation I tau state)
    (C3.complexNegate (minusTriadVariation I tau state))

literalIdealEnergyTriadConservation :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (state : State.IdealElsasserFourierState F E) →
  energyTriadVariation I tau state ≡ C3.complexZero F
literalIdealEnergyTriadConservation {F = F} I tau state
  rewrite plusTriadVariationZero I tau state
        | minusTriadVariationZero I tau state =
  Algebra.complexAddZeroLeft (C3.complexZero F)

literalIdealCrossHelicityTriadConservation :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (state : State.IdealElsasserFourierState F E) →
  crossHelicityTriadVariation I tau state ≡ C3.complexZero F
literalIdealCrossHelicityTriadConservation {F = F} I tau state
  rewrite plusTriadVariationZero I tau state
        | minusTriadVariationZero I tau state
        | Hermitian.complexNegateZero F =
  Algebra.complexAddZeroLeft (C3.complexZero F)

record LiteralIdealInvariantBoundary : Set where
  constructor literal-ideal-invariant-boundary
  field
    plusPseudoEnergyTriadZeroOwned : Bool
    plusPseudoEnergyTriadZeroOwnedIsTrue : plusPseudoEnergyTriadZeroOwned ≡ true

    minusPseudoEnergyTriadZeroOwned : Bool
    minusPseudoEnergyTriadZeroOwnedIsTrue : minusPseudoEnergyTriadZeroOwned ≡ true

    totalEnergyTriadConservationOwned : Bool
    totalEnergyTriadConservationOwnedIsTrue : totalEnergyTriadConservationOwned ≡ true

    crossHelicityTriadConservationOwned : Bool
    crossHelicityTriadConservationOwnedIsTrue :
      crossHelicityTriadConservationOwned ≡ true

    magneticHelicityFollowsFromSameCompiler : Bool
    magneticHelicityFollowsFromSameCompilerIsFalse :
      magneticHelicityFollowsFromSameCompiler ≡ false

canonicalLiteralIdealInvariantBoundary : LiteralIdealInvariantBoundary
canonicalLiteralIdealInvariantBoundary =
  literal-ideal-invariant-boundary true refl true refl true refl true refl false refl
