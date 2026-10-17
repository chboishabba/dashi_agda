module DASHI.Reasoning.TrialecticT27PolicyResidualReductionValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticT27PolicyResidualReductionExact as Reduction27

boundary : Reduction27.TrialecticT27PolicyResidualReductionBoundary
boundary = Reduction27.canonicalTrialecticT27PolicyResidualReductionBoundary

reductionPaid : Reduction27.t18ConsumerReductionConstructed boundary ≡ true
reductionPaid = refl

reopeningPaid : Reduction27.hiddenPolicyExactResidualReopeningPaid boundary ≡ true
reopeningPaid = refl

discriminatorPaid : Reduction27.thirdFaceMeasurementDiscriminatorPaid boundary ≡ true
discriminatorPaid = refl

equifinalityPaid : Reduction27.policyMechanisticEquifinalityPaid boundary ≡ true
equifinalityPaid = refl

futurePaid : Reduction27.declaredT18FutureConsumerPreserved boundary ≡ true
futurePaid = refl

thirdFaceNotPreserved : Reduction27.thirdFaceConsumerPreservedByT18Reduction boundary ≡ false
thirdFaceNotPreserved = refl

physicalNotPromoted : Reduction27.policyResidualPromotedToPhysicalMechanism boundary ≡ false
physicalNotPromoted = refl

reopenedFirst :
  Reduction27.reopenPolicyExact Reduction27.firstPolicyState
  ≡ Reduction27.firstPolicyState
reopenedFirst = refl
