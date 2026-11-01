module DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNEnergyCancellationAssembly as Assembly
import DASHI.Physics.Plasma.MHDElsasserProjectedThreeLegCancellationExact as Projected

------------------------------------------------------------------------
-- ONE CONCRETE IDEAL MHD ELSASSER STATE ON THE EXACT FOURIER C3 CARRIER
------------------------------------------------------------------------

record IdealElsasserFourierState
    {r : _}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set r where
  constructor ideal-elsasser-fourier-state
  field
    zPlus zMinus : Z3.FourierMode → C3.Complex3 F
    plusReality : Audit.RealityCondition zPlus
    minusReality : Audit.RealityCondition zMinus
    plusDivergenceFree : Audit.DivergenceFreeCondition E zPlus
    minusDivergenceFree : Audit.DivergenceFreeCondition E zMinus
    stateReference : String

open IdealElsasserFourierState public

plusTransferLaws :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E) →
  IdealElsasserFourierState F E →
  Assembly.OrderedTransferCancellationLaws (C3.Complex F)
plusTransferLaws I state =
  Projected.projectedElsasserTransferLaws
    _ I (zMinus state) (zPlus state)
    (minusReality state) (plusReality state)
    (minusDivergenceFree state) (plusDivergenceFree state)

minusTransferLaws :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E) →
  IdealElsasserFourierState F E →
  Assembly.OrderedTransferCancellationLaws (C3.Complex F)
minusTransferLaws I state =
  Projected.projectedElsasserTransferLaws
    _ I (zPlus state) (zMinus state)
    (plusReality state) (minusReality state)
    (plusDivergenceFree state) (minusDivergenceFree state)

plusThreeLegPseudoEnergyCancellation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (state : IdealElsasserFourierState F E) →
  let laws = plusTransferLaws I state in
  Assembly.add laws
    (Assembly.add laws
      (Assembly.orderedPairTransfer laws tau)
      (Assembly.orderedPairTransfer laws (Orbit.pEnergyLeg tau)))
    (Assembly.orderedPairTransfer laws (Orbit.qEnergyLeg tau))
  ≡ Assembly.zero laws
plusThreeLegPseudoEnergyCancellation {E = E} I tau state =
  Projected.projectedElsasserThreeLegCancellation
    E I tau (zMinus state) (zPlus state)
    (minusReality state) (plusReality state)
    (minusDivergenceFree state) (plusDivergenceFree state)

minusThreeLegPseudoEnergyCancellation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (state : IdealElsasserFourierState F E) →
  let laws = minusTransferLaws I state in
  Assembly.add laws
    (Assembly.add laws
      (Assembly.orderedPairTransfer laws tau)
      (Assembly.orderedPairTransfer laws (Orbit.pEnergyLeg tau)))
    (Assembly.orderedPairTransfer laws (Orbit.qEnergyLeg tau))
  ≡ Assembly.zero laws
minusThreeLegPseudoEnergyCancellation {E = E} I tau state =
  Projected.projectedElsasserThreeLegCancellation
    E I tau (zPlus state) (zMinus state)
    (plusReality state) (minusReality state)
    (plusDivergenceFree state) (minusDivergenceFree state)

record PlusMinusProjectedBoundary : Set where
  constructor plus-minus-projected-boundary
  field
    plusPseudoEnergyProjectedCancellationOwned : Bool
    plusPseudoEnergyProjectedCancellationOwnedIsTrue :
      plusPseudoEnergyProjectedCancellationOwned ≡ true

    minusPseudoEnergyProjectedCancellationOwned : Bool
    minusPseudoEnergyProjectedCancellationOwnedIsTrue :
      minusPseudoEnergyProjectedCancellationOwned ≡ true

    plusReceiptDefinitionallyEqualsMinusReceipt : Bool
    plusReceiptDefinitionallyEqualsMinusReceiptIsFalse :
      plusReceiptDefinitionallyEqualsMinusReceipt ≡ false

    pdeSameObjectWeldStillRequired : Bool
    pdeSameObjectWeldStillRequiredIsTrue : pdeSameObjectWeldStillRequired ≡ true

canonicalPlusMinusProjectedBoundary : PlusMinusProjectedBoundary
canonicalPlusMinusProjectedBoundary =
  plus-minus-projected-boundary true refl true refl false refl true refl
