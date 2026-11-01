module DASHI.Physics.Plasma.MHDMagneticHelicityThreeLegBidiExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State
import DASHI.Physics.Plasma.MHDDoubledMagneticElsasserFibreExact as Doubled
import DASHI.Physics.Plasma.MHDPhysicalInverseCurlMagneticHelicityExact as InverseCurl

------------------------------------------------------------------------
-- LITERAL THREE-LEG MAGNETIC-HELICITY CONSUMER
--
-- No cyclic permutation of a Hermitian triple product is assumed.  Each leg
-- is built from the actual doubled magnetic output fibre and the complete
-- ordered p,q + q,p induction tangent at that output.  The final live theorem
-- is therefore one concrete equality on the exact Fourier carrier.
------------------------------------------------------------------------

orderedDoubledInductionAt :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  State.IdealElsasserFourierState F E →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
orderedDoubledInductionAt I state tau =
  Doubled.doubledInductionOrderedInteraction I state
    (Physical.k tau) (Physical.p tau) (Physical.q tau)

orderedPairDoubledInductionAt :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  State.IdealElsasserFourierState F E →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
orderedPairDoubledInductionAt I state tau =
  C3.complex3Add
    (orderedDoubledInductionAt I state tau)
    (orderedDoubledInductionAt I state (Symmetry.swapTriad tau))

physicalMagneticHelicityDirectionalVariation :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex3 F → C3.Complex F
physicalMagneticHelicityDirectionalVariation E I k magnetic tangent =
  C3.complexAdd
    (C3.complexRealPart
      (C3.hermitianPairing3 tangent
        (InverseCurl.physicalVectorPotential E I k magnetic)))
    (C3.complexRealPart
      (C3.hermitianPairing3 magnetic
        (InverseCurl.physicalVectorPotential E I k tangent)))

magneticHelicityLegVariation :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E) →
  Physical.PhysicalTriadIncidence → C3.Complex F
magneticHelicityLegVariation E I state tau =
  physicalMagneticHelicityDirectionalVariation E I
    (Physical.k tau)
    (Doubled.doubledMagnetic state (Physical.k tau))
    (orderedPairDoubledInductionAt I state tau)

magneticHelicityThreeLegVariation :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E) →
  Physical.PhysicalTriadIncidence → C3.Complex F
magneticHelicityThreeLegVariation E I state tau =
  C3.complexAdd
    (C3.complexAdd
      (magneticHelicityLegVariation E I state tau)
      (magneticHelicityLegVariation E I state (Orbit.pEnergyLeg tau)))
    (magneticHelicityLegVariation E I state (Orbit.qEnergyLeg tau))

record MagneticHelicityThreeLegCancellationReceipt
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) : Set r where
  constructor magnetic-helicity-three-leg-cancellation-receipt
  field
    literalThreeLegVariationZero :
      magneticHelicityThreeLegVariation E I state tau
      ≡ C3.complexZero F
    receiptReference : String

open MagneticHelicityThreeLegCancellationReceipt public

data MagneticHelicityReverseObligation : Set where
  establishRealityPairedThreeLegInductionCancellation :
    MagneticHelicityReverseObligation

reverseMagneticHelicityProofSearch : MagneticHelicityReverseObligation
reverseMagneticHelicityProofSearch =
  establishRealityPairedThreeLegInductionCancellation

record MagneticHelicityThreeLegBidiBoundary : Set where
  constructor magnetic-helicity-three-leg-bidi-boundary
  field
    literalThreeLegConsumerOwned : Bool
    literalThreeLegConsumerOwnedIsTrue : literalThreeLegConsumerOwned ≡ true

    orderedPairInductionTangentOwned : Bool
    orderedPairInductionTangentOwnedIsTrue : orderedPairInductionTangentOwned ≡ true

    inverseCurlObserverOwned : Bool
    inverseCurlObserverOwnedIsTrue : inverseCurlObserverOwned ≡ true

    cyclicHermitianPermutationAssumed : Bool
    cyclicHermitianPermutationAssumedIsFalse :
      cyclicHermitianPermutationAssumed ≡ false

    realityPairedThreeLegCancellationOwnedHere : Bool
    realityPairedThreeLegCancellationOwnedHereIsFalse :
      realityPairedThreeLegCancellationOwnedHere ≡ false

canonicalMagneticHelicityThreeLegBidiBoundary : MagneticHelicityThreeLegBidiBoundary
canonicalMagneticHelicityThreeLegBidiBoundary =
  magnetic-helicity-three-leg-bidi-boundary
    true refl true refl true refl false refl false refl
