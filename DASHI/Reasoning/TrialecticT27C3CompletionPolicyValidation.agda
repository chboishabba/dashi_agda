module DASHI.Reasoning.TrialecticT27C3CompletionPolicyValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27C3CompletionPolicyExact as C3Policy

boundary : C3Policy.TrialecticT27C3CompletionPolicyBoundary
boundary = C3Policy.canonicalTrialecticT27C3CompletionPolicyBoundary

t9ObserverRechartPaid : C3Policy.t9ObserverRechartExact boundary ≡ true
t9ObserverRechartPaid = refl

orderThreePaid : C3Policy.t9C3ActionOrderThree boundary ≡ true
orderThreePaid = refl

completionConstructed : C3Policy.nativeC3CompletionPolicyConstructed boundary ≡ true
completionConstructed = refl

graphLawPaid : C3Policy.nativeC3CompletionSatisfiesGraphLaw boundary ≡ true
graphLawPaid = refl

notIITPolicy : C3Policy.iitBOperatorPolicyIdentifiedWithNativeC3 boundary ≡ false
notIITPolicy = refl

notPhysicalDynamics : C3Policy.nativeC3PolicyPromotedToPhysicalDynamics boundary ≡ false
notPhysicalDynamics = refl

threeRotationsReturn :
  (coordinates : Tower.T9Coordinates) →
  C3Policy.rotateT9
    (C3Policy.rotateT9
      (C3Policy.rotateT9 coordinates))
  ≡ coordinates
threeRotationsReturn = C3Policy.rotateT9ThreeTimes
