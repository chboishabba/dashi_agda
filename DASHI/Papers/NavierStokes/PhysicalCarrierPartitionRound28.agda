module DASHI.Papers.NavierStokes.PhysicalCarrierPartitionRound28 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaRound28Exact as Round28

record PhysicalCarrierPartitionRound28Status : Set where
  constructor physical-carrier-partition-round28-status
  field
    commutingCarrierSelectorProved : Bool
    conjugateOutputFibresProved : Bool
    dependentOwnerPartitionProved : Bool
    signedConstituentGroupingProved : Bool
    signedInteractionFibreProved : Bool
    triadOrbitParityProved : Bool
    divisionFreePluckerScalingProved : Bool
    admissibleTaxAggregationProved : Bool
    nineOwnerAbsorptionAlgebraProved : Bool
    physicalOwnerEstimatesProduced : Bool
    strictViscosityMarginProduced : Bool
    unconditionalClayPromotion : Bool

open PhysicalCarrierPartitionRound28Status public

canonicalPhysicalCarrierPartitionRound28Status :
  PhysicalCarrierPartitionRound28Status
canonicalPhysicalCarrierPartitionRound28Status =
  physical-carrier-partition-round28-status
    true true true true true true true true true false false false

carrierPartitionAdvanced :
  commutingCarrierSelectorProved
    canonicalPhysicalCarrierPartitionRound28Status ≡ true
carrierPartitionAdvanced = refl

signedCancellationArchitectureAdvanced :
  signedConstituentGroupingProved
    canonicalPhysicalCarrierPartitionRound28Status ≡ true
signedCancellationArchitectureAdvanced = refl

physicalTaxesStillOpen :
  physicalOwnerEstimatesProduced
    canonicalPhysicalCarrierPartitionRound28Status ≡ false
physicalTaxesStillOpen = refl

strictMarginStillOpen :
  strictViscosityMarginProduced
    canonicalPhysicalCarrierPartitionRound28Status ≡ false
strictMarginStillOpen = refl

clayPromotionStillFalse :
  unconditionalClayPromotion
    canonicalPhysicalCarrierPartitionRound28Status ≡ false
clayPromotionStillFalse = refl
