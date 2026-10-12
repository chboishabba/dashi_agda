module DASHI.Biology.SignedSSPWeaveAddressNeutralDynamicsValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Biology.SignedSSPWeaveAddressNeutralDynamicsExact as Cut

counterPreservationIsPaid :
  Cut.nonRefinementCounterPreservationPaid Cut.canonicalAddressDynamicsMaxCut ≡ true
counterPreservationIsPaid = refl

conservativeIdentityPolicyIsTyped :
  Cut.conservativeIdentityPolicyTyped Cut.canonicalAddressDynamicsMaxCut ≡ true
conservativeIdentityPolicyIsTyped = refl

conservativePolicyIsNotPromotedToSourceSemantics :
  Cut.conservativeIdentityPolicyIsSourceSemantics Cut.canonicalAddressDynamicsMaxCut ≡ false
conservativePolicyIsNotPromotedToSourceSemantics = refl

refineAt369SourceLawRemainsOpen :
  Cut.refineAt369AddressSourceLawPaid Cut.canonicalAddressDynamicsMaxCut ≡ false
refineAt369SourceLawRemainsOpen = refl
