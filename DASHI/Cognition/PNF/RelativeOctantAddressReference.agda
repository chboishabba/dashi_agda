module DASHI.Cognition.PNF.RelativeOctantAddressReference where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

open import DASHI.Cognition.PNF.ComplexityArithmetic

------------------------------------------------------------------------
-- Relative 8-way refinement address.
--
-- Three independent binary refinement coordinates give eight relative child
-- states.  This is the precise sense in which an octree-like local refinement
-- digit appears.  It does NOT mean an entire provenance-bearing PNF cell fits in
-- one byte: only the child choice relative to an already-known parent has eight
-- states.  Physical layout remains a measured codec question.
------------------------------------------------------------------------

data Octant : Set where
  o000 o001 o010 o011 o100 o101 o110 o111 : Octant

encodeOctant : Octant → Nat
encodeOctant o000 = 0
encodeOctant o001 = 1
encodeOctant o010 = 2
encodeOctant o011 = 3
encodeOctant o100 = 4
encodeOctant o101 = 5
encodeOctant o110 = 6
encodeOctant o111 = 7

decodeOctant : Nat → Octant
decodeOctant 0 = o000
decodeOctant 1 = o001
decodeOctant 2 = o010
decodeOctant 3 = o011
decodeOctant 4 = o100
decodeOctant 5 = o101
decodeOctant 6 = o110
decodeOctant _ = o111

decodeEncodeOctant : (octant : Octant) →
  decodeOctant (encodeOctant octant) ≡ octant
decodeEncodeOctant o000 = refl
decodeEncodeOctant o001 = refl
decodeEncodeOctant o010 = refl
decodeEncodeOctant o011 = refl
decodeEncodeOctant o100 = refl
decodeEncodeOctant o101 = refl
decodeEncodeOctant o110 = refl
decodeEncodeOctant o111 = refl

RelativeOctantAddress : Set
RelativeOctantAddress = List Octant

octreeCellCount : Nat → Nat
octreeCellCount zero = 1
octreeCellCount (suc depth) = 8 *ᶜ octreeCellCount depth

record RelativeAddressStorageReceipt : Set where
  constructor relativeAddressStorageReceipt
  field
    depth : Nat
    relativeSteps : Nat
    encodedBytes : Nat
    parentAddressImplicit : Bool

open RelativeAddressStorageReceipt public

data OneByteWholeCellAuthority : Set where

oneOctantDigitDoesNotProveOneByteWholeCell : OneByteWholeCellAuthority → ⊥
oneOctantDigitDoesNotProveOneByteWholeCell ()

record RelativeOctantBoundary : Set where
  constructor relativeOctantBoundary
  field
    oneRelativeStepHasEightStates : Bool
    oneRelativeStepHasEightStatesIsTrue : oneRelativeStepHasEightStates ≡ true
    wholePNFCellAutomaticallyOneByte : Bool
    wholePNFCellAutomaticallyOneByteIsFalse :
      wholePNFCellAutomaticallyOneByte ≡ false
    parentRelativeAddressingMayReduceRepeatedStorage : Bool
    parentRelativeAddressingMayReduceRepeatedStorageIsTrue :
      parentRelativeAddressingMayReduceRepeatedStorage ≡ true

open RelativeOctantBoundary public

canonicalRelativeOctantBoundary : RelativeOctantBoundary
canonicalRelativeOctantBoundary =
  relativeOctantBoundary true refl false refl true refl
