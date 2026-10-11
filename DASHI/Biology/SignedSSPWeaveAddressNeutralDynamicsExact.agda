module DASHI.Biology.SignedSSPWeaveAddressNeutralDynamicsExact where

------------------------------------------------------------------------
-- ADDRESS-NEUTRAL SUBLANGUAGE OF THE SIGNED SSP WEAVE
--
-- The executable WeaveEffect semantics has exactly one instruction which
-- changes the refinement counter: refineAt369.  The remaining five instruction
-- forms change carrier/token bookkeeping only.  This owner turns that fact into
-- a typed partial metadata dynamics instead of leaving "general instruction
-- address semantics" as one undifferentiated external debt.
--
-- We do NOT invent the missing refineAt369 address transition.  The theorem is
-- only that all non-refinement instructions admit the conservative identity
-- action on an already supplied 3/6/9 address.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Geometry.SSP369Ultrametric as SSP

data AddressNeutralInstruction : Set where
  buildNeutral : AddressNeutralInstruction
  removeInvariantNeutral : AddressNeutralInstruction
  introducePrimeNeutral : Signed.SSPPrime -> AddressNeutralInstruction
  introduceInversePrimeNeutral : Signed.SSPPrime -> AddressNeutralInstruction
  introduceInvariantUnitNeutral : AddressNeutralInstruction

eraseNeutral : AddressNeutralInstruction -> Signed.WeaveInstruction
eraseNeutral buildNeutral = Signed.buildSixByNineFibre
eraseNeutral removeInvariantNeutral = Signed.removeInvariantMode
eraseNeutral (introducePrimeNeutral prime) = Signed.introducePrime prime
eraseNeutral (introduceInversePrimeNeutral prime) = Signed.introduceInversePrime prime
eraseNeutral introduceInvariantUnitNeutral = Signed.introduceInvariantUnit

neutralInstructionPreservesRefinementSteps :
  (instruction : AddressNeutralInstruction) ->
  (effect : Signed.WeaveEffect) ->
  Signed.refinementSteps
    (Signed.applyInstruction (eraseNeutral instruction) effect)
  ≡ Signed.refinementSteps effect
neutralInstructionPreservesRefinementSteps buildNeutral effect = refl
neutralInstructionPreservesRefinementSteps removeInvariantNeutral effect = refl
neutralInstructionPreservesRefinementSteps (introducePrimeNeutral prime) effect = refl
neutralInstructionPreservesRefinementSteps (introduceInversePrimeNeutral prime) effect = refl
neutralInstructionPreservesRefinementSteps introduceInvariantUnitNeutral effect = refl

neutralStepAddress :
  AddressNeutralInstruction -> SSP.Address 3 -> SSP.Address 3
neutralStepAddress instruction address = address

neutralStepAddressIsIdentity :
  (instruction : AddressNeutralInstruction) ->
  (address : SSP.Address 3) ->
  neutralStepAddress instruction address ≡ address
neutralStepAddressIsIdentity instruction address = refl

------------------------------------------------------------------------
-- Exact max-cut consequence.
------------------------------------------------------------------------

record AddressDynamicsMaxCut : Set where
  constructor address-dynamics-max-cut
  field
    buildAddressDynamicsPaid : Bool
    removeInvariantAddressDynamicsPaid : Bool
    introducePrimeAddressDynamicsPaid : Bool
    introduceInversePrimeAddressDynamicsPaid : Bool
    introduceInvariantUnitAddressDynamicsPaid : Bool
    refineAt369AddressDynamicsPaid : Bool

open AddressDynamicsMaxCut public

canonicalAddressDynamicsMaxCut : AddressDynamicsMaxCut
canonicalAddressDynamicsMaxCut =
  address-dynamics-max-cut true true true true true false
