module DASHI.Biology.SignedSSPWeaveAddressNeutralDynamicsExact where

------------------------------------------------------------------------
-- CONSERVATIVE ADDRESS POLICY FOR THE NON-REFINEMENT WEAVE SUBLANGUAGE
--
-- The executable WeaveEffect semantics has exactly one instruction which
-- changes its explicit refinement counter: refineAt369.  The remaining five
-- instruction forms leave that counter unchanged.
--
-- IMPORTANT BOUNDARY:
-- address369 is richer metadata carried outside WeaveEffect.  Counter
-- preservation alone does NOT prove that a source-owned address369 semantics
-- must be identity for those five instructions.  What we can construct
-- generically is the conservative identity extension below.  It is a typed
-- compiler policy consistent with the executable effect, not recovered source
-- semantics.
--
-- Thus this owner pays:
--   * exact non-refinement counter preservation;
--   * existence of a conservative identity address policy.
-- It leaves source-owned address laws for ALL instruction forms external,
-- including refineAt369.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Geometry.SSP369Ultrametric as SSP

data AddressCounterNeutralInstruction : Set where
  buildCounterNeutral : AddressCounterNeutralInstruction
  removeInvariantCounterNeutral : AddressCounterNeutralInstruction
  introducePrimeCounterNeutral : Signed.SSPPrime -> AddressCounterNeutralInstruction
  introduceInversePrimeCounterNeutral : Signed.SSPPrime -> AddressCounterNeutralInstruction
  introduceInvariantUnitCounterNeutral : AddressCounterNeutralInstruction

eraseCounterNeutral : AddressCounterNeutralInstruction -> Signed.WeaveInstruction
eraseCounterNeutral buildCounterNeutral = Signed.buildSixByNineFibre
eraseCounterNeutral removeInvariantCounterNeutral = Signed.removeInvariantMode
eraseCounterNeutral (introducePrimeCounterNeutral prime) = Signed.introducePrime prime
eraseCounterNeutral (introduceInversePrimeCounterNeutral prime) = Signed.introduceInversePrime prime
eraseCounterNeutral introduceInvariantUnitCounterNeutral = Signed.introduceInvariantUnit

counterNeutralInstructionPreservesRefinementSteps :
  (instruction : AddressCounterNeutralInstruction) ->
  (effect : Signed.WeaveEffect) ->
  Signed.refinementSteps
    (Signed.applyInstruction (eraseCounterNeutral instruction) effect)
  ≡ Signed.refinementSteps effect
counterNeutralInstructionPreservesRefinementSteps buildCounterNeutral effect = refl
counterNeutralInstructionPreservesRefinementSteps removeInvariantCounterNeutral effect = refl
counterNeutralInstructionPreservesRefinementSteps (introducePrimeCounterNeutral prime) effect = refl
counterNeutralInstructionPreservesRefinementSteps (introduceInversePrimeCounterNeutral prime) effect = refl
counterNeutralInstructionPreservesRefinementSteps introduceInvariantUnitCounterNeutral effect = refl

-- Minimal conservative extension policy.  This is available to a downstream
-- compiler if explicitly selected; it is not claimed as recovered source law.
conservativeIdentityAddressStep :
  AddressCounterNeutralInstruction -> SSP.Address 3 -> SSP.Address 3
conservativeIdentityAddressStep instruction address = address

conservativeIdentityAddressStepIsIdentity :
  (instruction : AddressCounterNeutralInstruction) ->
  (address : SSP.Address 3) ->
  conservativeIdentityAddressStep instruction address ≡ address
conservativeIdentityAddressStepIsIdentity instruction address = refl

------------------------------------------------------------------------
-- Exact max-cut consequence.
------------------------------------------------------------------------

record AddressDynamicsMaxCut : Set where
  constructor address-dynamics-max-cut
  field
    nonRefinementCounterPreservationPaid : Bool
    conservativeIdentityPolicyTyped : Bool
    conservativeIdentityPolicyIsSourceSemantics : Bool
    buildAddressSourceLawPaid : Bool
    removeInvariantAddressSourceLawPaid : Bool
    introducePrimeAddressSourceLawPaid : Bool
    introduceInversePrimeAddressSourceLawPaid : Bool
    introduceInvariantUnitAddressSourceLawPaid : Bool
    refineAt369AddressSourceLawPaid : Bool

open AddressDynamicsMaxCut public

canonicalAddressDynamicsMaxCut : AddressDynamicsMaxCut
canonicalAddressDynamicsMaxCut =
  address-dynamics-max-cut
    true
    true
    false
    false false false false false false
