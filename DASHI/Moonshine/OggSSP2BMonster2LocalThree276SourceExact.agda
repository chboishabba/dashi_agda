module DASHI.Moonshine.OggSSP2BMonster2LocalThree276SourceExact where

------------------------------------------------------------------------
-- SOURCE-NATIVE MONSTER 2-LOCAL THREE-276 DONOR
--
-- Holmes--Wilson, "A new computer construction of the Monster using 2-local
-- subgroups" construct the 196882-dimensional Monster module over GF(3).
-- Restriction to K = C_M(<2B,2B>) has three literal 276-dimensional
-- constituents 276a, 276b, 276c.  Their order-three normalizer matrix T cycles
-- the three constituents.  An outer K.2 element interchanges 276b and 276c.
--
-- This is highly aligned with the repository's three-2B-fibre architecture,
-- but it is NOT the missing same-object theorem: the published module here is
-- over GF(3), whereas the 2B Tate head is over GF(2).  No characteristic-change
-- or Tate identification is manufactured in this owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. The sourced three 276-dimensional constituents.
------------------------------------------------------------------------

data Three276 : Set where
  module276a module276b module276c : Three276

moduleDimension : Three276 → Nat
moduleDimension module276a = 276
moduleDimension module276b = 276
moduleDimension module276c = 276

allThreeHaveDimension276 :
  moduleDimension module276a
  + moduleDimension module276b
  + moduleDimension module276c
  ≡ 828
allThreeHaveDimension276 = refl

trialityT : Three276 → Three276
trialityT module276a = module276b
trialityT module276b = module276c
trialityT module276c = module276a

trialityTOrderThree :
  (m : Three276) → trialityT (trialityT (trialityT m)) ≡ m
trialityTOrderThree module276a = refl
trialityTOrderThree module276b = refl
trialityTOrderThree module276c = refl

outerK2Swap : Three276 → Three276
outerK2Swap module276a = module276a
outerK2Swap module276b = module276c
outerK2Swap module276c = module276b

outerK2SwapInvolutive :
  (m : Three276) → outerK2Swap (outerK2Swap m) ≡ m
outerK2SwapInvolutive module276a = refl
outerK2SwapInvolutive module276b = refl
outerK2SwapInvolutive module276c = refl

------------------------------------------------------------------------
-- 2. Source / characteristic boundary.
------------------------------------------------------------------------

record Monster2LocalThree276Source : Set where
  constructor monster-2local-three276-source
  field
    sourceReference : String
    ambientMonsterModuleDimension : Nat
    ambientCharacteristic : Nat
    literalThree276ConstituentsSourced : Bool
    orderThreeTrialityCyclesThree276 : Bool
    outerK2Swaps276b276c : Bool
    identifiedWithCharacteristicTwoTateFibres : Bool
    characteristicChangeReceiptPaid : Bool

open Monster2LocalThree276Source public

canonicalMonster2LocalThree276Source : Monster2LocalThree276Source
canonicalMonster2LocalThree276Source =
  monster-2local-three276-source
    "Holmes--Wilson, A new computer construction of the Monster using 2-local subgroups"
    196882 3
    true true true
    false false

three276SourcePaid :
  literalThree276ConstituentsSourced canonicalMonster2LocalThree276Source ≡ true
three276SourcePaid = refl

trialitySourcePaid :
  orderThreeTrialityCyclesThree276 canonicalMonster2LocalThree276Source ≡ true
trialitySourcePaid = refl

characteristicTwoTateIdentificationStillOpen :
  identifiedWithCharacteristicTwoTateFibres canonicalMonster2LocalThree276Source ≡ false
characteristicTwoTateIdentificationStillOpen = refl

characteristicChangeStillOpen :
  characteristicChangeReceiptPaid canonicalMonster2LocalThree276Source ≡ false
characteristicChangeStillOpen = refl

------------------------------------------------------------------------
-- 3. Promotion firewall.
------------------------------------------------------------------------

data GF3Three276IsCharacteristicTwoTateThreeFibre : Set where

gf3Three276DoesNotConstructTateThreeFibre :
  GF3Three276IsCharacteristicTwoTateThreeFibre → ⊥
gf3Three276DoesNotConstructTateThreeFibre ()
