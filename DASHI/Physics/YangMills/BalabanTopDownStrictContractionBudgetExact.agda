module DASHI.Physics.YangMills.BalabanTopDownStrictContractionBudgetExact where

------------------------------------------------------------------------
-- ROUND79: TOP-DOWN STRICT CONTRACTION, NOT A PRESELECTED 17/32
--
-- PRIMARY SOURCES / CALIBRATION
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- David C. Brydges, P. K. Mitter and B. Scoppola,
-- "Critical (Phi^4)_{3,epsilon}", Communications in Mathematical Physics
-- 240 (2003), 281--327. DOI: 10.1007/s00220-003-0895-4.
--
-- Abdelmalek Abdesselam,
-- "A Complete Renormalization Group Trajectory Between Two Fixed Points",
-- Communications in Mathematical Physics 276 (2007), 727--772.
-- DOI: 10.1007/s00220-007-0352-x.
--
-- Tadeusz Bałaban, John Imbrie and Arthur Jaffe,
-- "Exact Renormalization Group for Gauge Theories",
-- in Progress in Gauge Field Theory (1984), 79--103.
-- DOI: 10.1007/978-1-4757-0280-4_4.
--
-- DASHI CONTRIBUTION
--
-- Round66 chose the convenient sufficient budget
--
--       q_small <= 1/2,      q_large <= 1/32,
--       q_total <= q_small+q_large <= 17/32.
--
-- The Clay-facing UV theorem does not require 17/32.  It requires a genuine
-- q<1 in the ONE corrected source-native norm.  Therefore, retaining the
-- existing small/KP target q_small <= 1/2, the weakest simple complementary
-- condition is merely
--
--       q_large < 1/2.
--
-- Then q_total < 1.  The former 1/32 large-polymer target is sixteen times
-- smaller than the boundary 1/2 and is analytically unnecessary unless another
-- downstream estimate specifically consumes its extra headroom.
--
-- More generally, any rational caps s,l with
--
--       q_small <= s, q_large <= l, s+l < 1
--
-- close the strict contraction theorem.  This is the budget region we should
-- optimize over while constructing the physical polymer estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanCorrectedSmallPolymerExtractionContractionExact as OldLarge

record RationalAdditiveContractionCosts : Set where
  field
    smallCost largeCost totalCost : ℚ
    totalBelowSum : totalCost ≤ smallCost + largeCost
open RationalAdditiveContractionCosts public

record StrictContractionAllocation
    (costs : RationalAdditiveContractionCosts) : Set where
  field
    smallCap largeCap : ℚ
    smallBelowCap : smallCost costs ≤ smallCap
    largeBelowCap : largeCost costs ≤ largeCap
    capsStrictlyFit : smallCap + largeCap < 1ℚ
open StrictContractionAllocation public

allocatedCostsStrictlyContract :
  ∀ {costs : RationalAdditiveContractionCosts} →
  StrictContractionAllocation costs →
  totalCost costs < 1ℚ
allocatedCostsStrictlyContract {costs} allocation =
  let
    sumBelowCaps :
      smallCost costs + largeCost costs
      ≤ smallCap allocation + largeCap allocation
    sumBelowCaps = ℚP.+-mono-≤
      (smallBelowCap allocation)
      (largeBelowCap allocation)

    totalBelowCaps :
      totalCost costs ≤ smallCap allocation + largeCap allocation
    totalBelowCaps = ℚP.≤-trans (totalBelowSum costs) sumBelowCaps
  in
  ℚP.≤-<-trans totalBelowCaps (capsStrictlyFit allocation)

------------------------------------------------------------------------
-- Direct top-down replacement of the old 1/32 large-branch target.
------------------------------------------------------------------------

half : ℚ
half = + 1 / 2

halfPlusHalfIsOne : half + half ≡ 1ℚ
halfPlusHalfIsOne = ℚRing.solve []

halfSmallStrictLargeContracts :
  (costs : RationalAdditiveContractionCosts) →
  smallCost costs ≤ half →
  largeCost costs < half →
  totalCost costs < 1ℚ
halfSmallStrictLargeContracts costs smallHalf largeHalf =
  let
    summed :
      smallCost costs + largeCost costs < half + half
    summed = ℚP.+-mono-≤-< smallHalf largeHalf

    sumStrictOne : smallCost costs + largeCost costs < 1ℚ
    sumStrictOne = subst
      (λ upper → smallCost costs + largeCost costs < upper)
      halfPlusHalfIsOne
      summed
  in
  ℚP.≤-<-trans (totalBelowSum costs) sumStrictOne

------------------------------------------------------------------------
-- Quantify how conservative the old large target was.
------------------------------------------------------------------------

sixteenTimesOldLargeIsHalf :
  (+ 16 / 1) * OldLarge.oneThirtySecond ≡ half
sixteenTimesOldLargeIsHalf = ℚRing.solve []

oldSeventeenThirtySecondBudgetIsOneAdmissibleInteriorPoint :
  StepV.half + OldLarge.oneThirtySecond < 1ℚ
oldSeventeenThirtySecondBudgetIsOneAdmissibleInteriorPoint =
  let
    oldLargeStrictHalf : OldLarge.oneThirtySecond < half
    oldLargeStrictHalf =
      ℚP.<-≤-trans OldLarge.oneThirtySecondPositive
        (subst
          (λ upper → OldLarge.oneThirtySecond ≤ upper)
          (ℚRing.solve [])
          ℚP.≤-refl)
  in
  ℚP.+-mono-≤-< ℚP.≤-refl oldLargeStrictHalf

topDownStrictContractionBudgetLevel : ProofLevel
topDownStrictContractionBudgetLevel = machineChecked

-- Physical boundary: the costs must be those of the SAME corrected norm.  The
-- theorem does not license adding unrelated estimates from different norms.
physicalSameNormSmallBelowHalfLevel : ProofLevel
physicalSameNormSmallBelowHalfLevel = conditional

physicalSameNormLargeStrictlyBelowHalfLevel : ProofLevel
physicalSameNormLargeStrictlyBelowHalfLevel = conditional
