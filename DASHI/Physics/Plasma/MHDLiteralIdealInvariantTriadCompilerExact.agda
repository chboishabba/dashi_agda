module DASHI.Physics.Plasma.MHDLiteralIdealInvariantTriadCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State
import DASHI.Physics.Plasma.MHDLiteralIdealEnergyCrossHelicityTriadConservationExact as EH
import DASHI.Physics.Plasma.MHDMagneticHelicityThreeLegBidiExact as HMVariation
import DASHI.Physics.Plasma.MHDLiteralMagneticHelicityTriadConservationExact as HM

------------------------------------------------------------------------
-- COMPACT LITERAL IDEAL-MHD INVARIANT COMPILER
--
-- One nonzero physical triad carries three distinct invariant receipts:
--
--   Delta E   = 0
--   Delta H_c = 0
--   Delta H_m = 0.
--
-- Energy and cross helicity compile from the two Elsasser pseudo-energies.
-- Magnetic helicity does NOT come from that compiler: it uses the separate
-- inverse-curl / ordered-induction / reality-paired triple-product proof.
------------------------------------------------------------------------

record IdealInvariantTriadReceipt
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence)
    (nonzero : Physical.NonZeroPhysicalTriad tau) : Set r where
  constructor ideal-invariant-triad-receipt
  field
    energyVariationZero :
      EH.energyTriadVariation I tau state ≡ C3.complexZero F

    crossHelicityVariationZero :
      EH.crossHelicityTriadVariation I tau state ≡ C3.complexZero F

    magneticHelicityVariationZero :
      HMVariation.magneticHelicityThreeLegVariation E I state tau
      ≡ C3.complexZero F

open IdealInvariantTriadReceipt public

compileIdealInvariantTriadReceipt :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence)
    (nonzero : Physical.NonZeroPhysicalTriad tau) →
  IdealInvariantTriadReceipt F E I S L state tau nonzero
compileIdealInvariantTriadReceipt E I S L state tau nonzero =
  ideal-invariant-triad-receipt
    (EH.literalIdealEnergyTriadConservation I tau state)
    (EH.literalIdealCrossHelicityTriadConservation I tau state)
    (HM.literalMagneticHelicityTriadConservation
      E I S L state tau nonzero)

------------------------------------------------------------------------
-- BIDI proof-search routes remain distinct.
------------------------------------------------------------------------

data IdealInvariantProofRoute : Set where
  elsasserPseudoEnergyRoute : IdealInvariantProofRoute
  inverseCurlInductionRoute : IdealInvariantProofRoute

energyProofRoute : IdealInvariantProofRoute
energyProofRoute = elsasserPseudoEnergyRoute

crossHelicityProofRoute : IdealInvariantProofRoute
crossHelicityProofRoute = elsasserPseudoEnergyRoute

magneticHelicityProofRoute : IdealInvariantProofRoute
magneticHelicityProofRoute = inverseCurlInductionRoute

record IdealInvariantCompilerBoundary : Set where
  constructor ideal-invariant-compiler-boundary
  field
    energyTriadReceiptOwned : Bool
    energyTriadReceiptOwnedIsTrue : energyTriadReceiptOwned ≡ true

    crossHelicityTriadReceiptOwned : Bool
    crossHelicityTriadReceiptOwnedIsTrue : crossHelicityTriadReceiptOwned ≡ true

    magneticHelicityNonzeroTriadReceiptOwned : Bool
    magneticHelicityNonzeroTriadReceiptOwnedIsTrue :
      magneticHelicityNonzeroTriadReceiptOwned ≡ true

    energyAndCrossHelicityShareElsasserCompiler : Bool
    energyAndCrossHelicityShareElsasserCompilerIsTrue :
      energyAndCrossHelicityShareElsasserCompiler ≡ true

    magneticHelicityUsesDistinctProducerRoute : Bool
    magneticHelicityUsesDistinctProducerRouteIsTrue :
      magneticHelicityUsesDistinctProducerRoute ≡ true

    triadReceiptImpliesGlobalContinuumInvariant : Bool
    triadReceiptImpliesGlobalContinuumInvariantIsFalse :
      triadReceiptImpliesGlobalContinuumInvariant ≡ false

canonicalIdealInvariantCompilerBoundary : IdealInvariantCompilerBoundary
canonicalIdealInvariantCompilerBoundary =
  ideal-invariant-compiler-boundary
    true refl true refl true refl true refl true refl false refl
