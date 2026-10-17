module DASHI.Reasoning.TrialecticT27PolicyHiddenNonDescentValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticT27PolicyHiddenNonDescentExact as Hidden

boundary : Hidden.TrialecticT27PolicyHiddenNonDescentBoundary
boundary = Hidden.canonicalTrialecticT27PolicyHiddenNonDescentBoundary

sameT18CollisionPaid : Hidden.sameT18DifferentThirdFaceWitnessPaid boundary ≡ true
sameT18CollisionPaid = refl

thirdFaceNonDescentPaid : Hidden.thirdFaceDoesNotFactorThroughT18 boundary ≡ true
thirdFaceNonDescentPaid = refl

policyNonDescentPaid : Hidden.policyChoiceDoesNotFactorThroughT18 boundary ≡ true
policyNonDescentPaid = refl

fixedPolicyRecoveryPaid : Hidden.fixedPolicyThirdFaceRecoveredFromT18 boundary ≡ true
fixedPolicyRecoveryPaid = refl

hiddenPolicyNotPhysicalDynamics : Hidden.hiddenPolicyChoicePromotedToPhysicalDynamics boundary ≡ false
hiddenPolicyNotPhysicalDynamics = refl

witnessCollision :
  Hidden.observedT18 Hidden.firstPolicyState
  ≡ Hidden.observedT18 Hidden.secondPolicyState
witnessCollision = Hidden.sameObservedT18

witnessThirdFaceDiffers :
  Hidden.thirdFaceConsumer Hidden.firstPolicyState
  ≡ Hidden.thirdFaceConsumer Hidden.secondPolicyState
  →
  Hidden.⊥
witnessThirdFaceDiffers = Hidden.differentThirdFace
