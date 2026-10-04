module DASHI.Moonshine.OggSSPP2Gamma0FourCanonicalRawFlagExact where

------------------------------------------------------------------------
-- p=2 CANONICAL RAW GAMMA_0(4) FLAG
--
-- EXTERNAL SOURCE CONTEXT
--
-- Reuses the same source statement already attributed in
-- OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparationExact:
--
-- on a supersingular elliptic curve over an algebraic closure of F_p, the
-- unique Drinfeld cyclic subgroup scheme of order p^r is ker(F^r).
--
-- Specializing at p=2 for r=1 and r=2 gives the source-level raw flag
--
--       ker(F) <= ker(F^2)
--
-- of ranks 2 and 4.
--
-- DASHI CONTRIBUTION
--
-- This file makes that RAW flag explicit.  It does not construct the
-- finite-flat group-scheme inclusion inside a concrete universal family.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparationExact as Unique
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

data SupersingularRawOrderTwoSubgroup : Set where
  kerFrobenius : SupersingularRawOrderTwoSubgroup

SupersingularRawOrderFourSubgroup : Set
SupersingularRawOrderFourSubgroup =
  Unique.SupersingularRawGamma0FourSubgroup

rawOrderTwoSubgroupCount : Nat
rawOrderTwoSubgroupCount = 1

rawOrderFourSubgroupCount : Nat
rawOrderFourSubgroupCount = Unique.rawSubgroupCount

rawOrderTwoIsUnique :
  (subgroup : SupersingularRawOrderTwoSubgroup) ->
  subgroup ≡ kerFrobenius
rawOrderTwoIsUnique kerFrobenius = refl

record RawGamma0FourFlag : Set where
  constructor raw-gamma0-four-flag
  field
    orderTwo : SupersingularRawOrderTwoSubgroup
    orderFour : SupersingularRawOrderFourSubgroup

    orderTwoIsKerFrobenius :
      orderTwo ≡ kerFrobenius

    orderFourIsKerFrobeniusSquared :
      orderFour ≡ Unique.kerFrobeniusSquared

    sourceBackedSubflagRelation : Bool
    sourceBackedSubflagRelationIsTrue :
      sourceBackedSubflagRelation ≡ true

open RawGamma0FourFlag public

canonicalRawFlag : RawGamma0FourFlag
canonicalRawFlag =
  raw-gamma0-four-flag
    kerFrobenius
    Unique.kerFrobeniusSquared
    refl
    refl
    true
    refl

rawFlagChoiceIsUnique :
  (flag : RawGamma0FourFlag) ->
  (orderTwo flag ≡ orderTwo canonicalRawFlag)
  ×
  (orderFour flag ≡ orderFour canonicalRawFlag)
rawFlagChoiceIsUnique flag =
  orderTwoUnique , orderFourUnique
  where
    orderTwoUnique :
      orderTwo flag ≡ orderTwo canonicalRawFlag
    orderTwoUnique
      rewrite orderTwoIsKerFrobenius flag = refl

    orderFourUnique :
      orderFour flag ≡ orderFour canonicalRawFlag
    orderFourUnique
      rewrite orderFourIsKerFrobeniusSquared flag = refl

rawFlagChoiceCountDoesNotExplainTen :
  (rawOrderTwoSubgroupCount * rawOrderFourSubgroupCount) ≡ 10 ->
  ⊥
rawFlagChoiceCountDoesNotExplainTen ()

data RawFlagCreatesConcreteFiniteFlatRealization : Set where

rawFlagDoesNotCreateConcreteFiniteFlatRealization :
  RawFlagCreatesConcreteFiniteFlatRealization -> ⊥
rawFlagDoesNotCreateConcreteFiniteFlatRealization ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record CanonicalRawGamma0FourFlagBoundary : Set where
  constructor canonical-raw-gamma0-four-flag-boundary
  field
    uniqueRawOrderTwoSubgroupRecorded : Bool
    uniqueRawOrderFourSubgroupReused : Bool
    rawKerFInsideKerF2FlagRecorded : Bool
    rawFlagChoiceUnique : Bool
    rawFlagExplainsTenResidualStates : Bool
    concreteFiniteFlatFlagRealizationConstructed : Bool

canonicalCanonicalRawGamma0FourFlagBoundary :
  CanonicalRawGamma0FourFlagBoundary
canonicalCanonicalRawGamma0FourFlagBoundary =
  canonical-raw-gamma0-four-flag-boundary
    true true true true false false
