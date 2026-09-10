module DASHI.Wikimedia.IbrahimOneThreeSixOneNineTenBulkOEISSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonster3BNineStratificationOEISPrimarySourceSnowballExact as Nine
import DASHI.Wikimedia.DASHIMathOEISTypedCarrierAuditHarnessExact as Audit

------------------------------------------------------------------------
-- TWO DISTINCT DECOMPOSITIONS AROUND THE SAME 196830 BULK
--
-- Existing exponent stratification:
--   9 = 1 + 2 + 6.
--
-- New outer-coefficient decompositions requested by the audit:
--   10 = 1 + 9
--   10 = 1 + 3 + 6.
--
-- Therefore
--   196830 = 10*3^9
--          = (1+9)*3^9
--          = (1+3+6)*3^9.
--
-- These are arithmetic re-factorisations of the OUTER coefficient 10.  They
-- are not the same object as the existing exponent split 9=1+2+6, and they do
-- not by themselves assign E6/Weyl/Monster representation roles to 1,3,6,9.
------------------------------------------------------------------------

onePlusNineIsTen : 1 + 9 ≡ 10
onePlusNineIsTen = refl

onePlusThreePlusSixIsTen : 1 + 3 + 6 ≡ 10
onePlusThreePlusSixIsTen = refl

nineAsOnePlusTwoPlusSix : 1 + 2 + 6 ≡ 9
nineAsOnePlusTwoPlusSix = Nine.nineExponentAsOnePlusTwoPlusSix

bulk : Nat
bulk = 196830

bulkAsTenTimesThreePowerNine : 10 * Nine.a000244 9 ≡ bulk
bulkAsTenTimesThreePowerNine = refl

bulkAsOnePlusNineTimesThreePowerNine : (1 + 9) * Nine.a000244 9 ≡ bulk
bulkAsOnePlusNineTimesThreePowerNine = refl

bulkAsOnePlusThreePlusSixTimesThreePowerNine :
  (1 + 3 + 6) * Nine.a000244 9 ≡ bulk
bulkAsOnePlusThreePlusSixTimesThreePowerNine = refl

------------------------------------------------------------------------
-- OEIS coordinates.
------------------------------------------------------------------------

record TenBulkOEISCoordinates : Set where
  constructor ten-bulk-oeis-coordinates
  field
    powerThreeOEIS : String
    tenTimesPowerThreeOEIS : String
    coefficientTenAtLevelZeroPaid : Bool
    levelNineBulkPaid : Bool
    onePlusNineDecompositionPaid : Bool
    onePlusThreePlusSixDecompositionPaid : Bool
open TenBulkOEISCoordinates public

canonicalTenBulkOEISCoordinates : TenBulkOEISCoordinates
canonicalTenBulkOEISCoordinates = ten-bulk-oeis-coordinates
  "A000244" "A005052" true true true true

------------------------------------------------------------------------
-- Typed-role discipline.
------------------------------------------------------------------------

data OuterTenSplitEqualsExponentNineSplit : Set where
data OneThreeSixCreatesE6RepresentationMeaning : Set where
data OneNineCreatesPointedCompletionIdentity : Set where
data SameNumeralsCreateSameCarrierRoles : Set where

outerAndExponentSplitsAreNotIdentified : OuterTenSplitEqualsExponentNineSplit → ⊥
outerAndExponentSplitsAreNotIdentified ()

oneThreeSixDoesNotCreateE6Meaning : OneThreeSixCreatesE6RepresentationMeaning → ⊥
oneThreeSixDoesNotCreateE6Meaning ()

oneNineDoesNotCreatePointedIdentity : OneNineCreatesPointedCompletionIdentity → ⊥
oneNineDoesNotCreatePointedIdentity ()

sameNumeralsDoNotCreateSameRoles : SameNumeralsCreateSameCarrierRoles → ⊥
sameNumeralsDoNotCreateSameRoles ()

record OneThreeSixOneNineFrontier : Set where
  constructor one-three-six-one-nine-frontier
  field
    tenAsOnePlusNinePaid : Bool
    tenAsOnePlusThreePlusSixPaid : Bool
    bulkAsOnePlusNineTimesThreePowerNinePaid : Bool
    bulkAsOnePlusThreePlusSixTimesThreePowerNinePaid : Bool
    exponentNineAsOnePlusTwoPlusSixPaid : Bool
    outerCoefficientAndExponentSplitKeptDistinct : Bool
    oeisCreatesSemanticIdentity : Bool
    nextResidual : String
open OneThreeSixOneNineFrontier public

currentOneThreeSixOneNineFrontier : OneThreeSixOneNineFrontier
currentOneThreeSixOneNineFrontier = one-three-six-one-nine-frontier
  true true true true true true false
  "compare these outer-ten decompositions against existing pointed-completion, E6 invariant-degree, and Monster action carriers. Promote only where the same indexed consumer survives; do not identify the outer 1/3/6/9 roles with the exponent 1/2/6 roles by numeral alone."
