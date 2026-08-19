module DASHI.Moonshine.MonsterLowPrimeLocalSubgroupDepthExact where

------------------------------------------------------------------------
-- LOW-PRIME MONSTER DEPTH FROM STANDARD LOCAL SUBGROUP STRUCTURE
--
-- SOURCE AUTHORITY
--
-- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker,
-- Robert A. Wilson,
-- "Atlas of Finite Groups", Oxford University Press, 1985.
-- ISBN 0-19-853199-0. No DOI is asserted for the book.
--
-- The online ATLAS of Finite Group Representations records for the Monster:
--
--   2^{1+24}.Co_1
--   3^{1+12}.2Suz.2
--
-- as standard maximal 2-local / 3-local subgroup shapes.  The 2-local order is
-- also the centralizer order of class 2B.  The 3-local maximal subgroup has the
-- same 3-primary depth as the 3B centralizer/normalizer lane.
--
-- ATLAS also records
--
--   |Co_1| has 2-primary exponent 21,
--   |Suz|  has 3-primary exponent 7.
--
-- Hence the displayed local shapes carry
--
--   2-primary depth: (1+24) + 21 = 46,
--   3-primary depth: (1+12) + 7 = 20.
--
-- DASHI CONTRIBUTION
--
-- Weld those standard local subgroup exponents to the repository's exact
-- Monster exponent carrier, then compare them with the Duncan--Swisher small-
-- prime right-hand sides 36 and 18.  This gives an independent LOCAL GROUP
-- structural realization of the full exceptional exponents.
--
-- IMPORTANT BOUNDARY
--
-- This does NOT prove that the Duncan--Swisher residuals 10 and 2 are caused by
-- a specific factor inside Co_1 or Suz.  What is proved is the exact comparison
--
--   geometric/modular RHS + residual = local-subgroup p-depth = v_p(|M|).
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.DuncanSwisherLowPrimeResidualExact as Low
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Published local-shape p-primary coordinates.
------------------------------------------------------------------------

twoBExtraspecialExponent : Nat
twoBExtraspecialExponent = 1 + 24

co1TwoExponent : Nat
co1TwoExponent = 21

twoBLocalTwoDepth : Nat
twoBLocalTwoDepth = twoBExtraspecialExponent + co1TwoExponent

threeBExtraspecialExponent : Nat
threeBExtraspecialExponent = 1 + 12

suzThreeExponent : Nat
suzThreeExponent = 7

threeBLocalThreeDepth : Nat
threeBLocalThreeDepth = threeBExtraspecialExponent + suzThreeExponent

twoBLocalTwoDepthIs46 : twoBLocalTwoDepth ≡ 46
twoBLocalTwoDepthIs46 = refl

threeBLocalThreeDepthIs20 : threeBLocalThreeDepth ≡ 20
threeBLocalThreeDepthIs20 = refl

------------------------------------------------------------------------
-- Same exponents as the exact published Monster-order carrier.
------------------------------------------------------------------------

twoBLocalDepthEqualsMonsterExponent :
  twoBLocalTwoDepth ≡ Exponent.monsterOrderExponent Lane.p2
twoBLocalDepthEqualsMonsterExponent = refl

threeBLocalDepthEqualsMonsterExponent :
  threeBLocalThreeDepth ≡ Exponent.monsterOrderExponent Lane.p3
threeBLocalDepthEqualsMonsterExponent = refl

------------------------------------------------------------------------
-- Compare directly with the two Duncan--Swisher exceptional RHS values.
------------------------------------------------------------------------

p2RHSPlusResidualEqualsLocalDepth :
  Low.commonDuncanSwisherRHS Low.low2 + Low.lowPrimeResidual Low.low2
  ≡ twoBLocalTwoDepth
p2RHSPlusResidualEqualsLocalDepth = refl

p3RHSPlusResidualEqualsLocalDepth :
  Low.commonDuncanSwisherRHS Low.low3 + Low.lowPrimeResidual Low.low3
  ≡ threeBLocalThreeDepth
p3RHSPlusResidualEqualsLocalDepth = refl

p2RHSPlusResidualEqualsMonsterExponent :
  Low.commonDuncanSwisherRHS Low.low2 + Low.lowPrimeResidual Low.low2
  ≡ Exponent.monsterOrderExponent Lane.p2
p2RHSPlusResidualEqualsMonsterExponent = refl

p3RHSPlusResidualEqualsMonsterExponent :
  Low.commonDuncanSwisherRHS Low.low3 + Low.lowPrimeResidual Low.low3
  ≡ Exponent.monsterOrderExponent Lane.p3
p3RHSPlusResidualEqualsMonsterExponent = refl

------------------------------------------------------------------------
-- The local decomposition itself is informative but is NOT identified with the
-- Duncan--Swisher decomposition.
------------------------------------------------------------------------

record MonsterLowPrimeLocalSubgroupDepthBoundary : Set where
  constructor monsterLowPrimeLocalSubgroupDepthBoundary
  field
    atlasTwoLocalShapeRetained : Bool
    atlasThreeLocalShapeRetained : Bool
    co1TwoPrimaryExponentRetained : Bool
    suzThreePrimaryExponentRetained : Bool
    localTwoDepthRecoversMonsterExponent46 : Bool
    localThreeDepthRecoversMonsterExponent20 : Bool
    duncanSwisherResidualClosesToLocalDepth : Bool
    residualIdentifiedWithSpecificCo1Factor : Bool
    residualIdentifiedWithSpecificSuzFactor : Bool
    localSubgroupDepthProvesDuncanSwisherAnalyticMechanism : Bool

canonicalMonsterLowPrimeLocalSubgroupDepthBoundary :
  MonsterLowPrimeLocalSubgroupDepthBoundary
canonicalMonsterLowPrimeLocalSubgroupDepthBoundary =
  monsterLowPrimeLocalSubgroupDepthBoundary
    true true true true true true true false false false
