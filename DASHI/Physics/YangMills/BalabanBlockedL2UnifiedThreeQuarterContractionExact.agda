module DASHI.Physics.YangMills.BalabanBlockedL2UnifiedThreeQuarterContractionExact where

------------------------------------------------------------------------
-- ROUND80: BLOCKED-L2 q < 1/4 + SMALL BRANCH <= 1/2 -> TOTAL < 3/4
--
-- PRIMARY / CALIBRATION SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- DASHI CONTRIBUTION
--
-- Round79 removed the arbitrary 17/32 target and proved that any same-norm
-- allocation s+l<1 suffices.  Round80 recovers the older blocked-L2 numerical
-- factor as an exact rational q with q<1/4.  Therefore, if the source-native
-- small branch is <=1/2 and the SAME corrected unified-norm large branch is
-- bounded by that blocked-L2 q, the full one-step cost is actually <3/4.
--
-- This is a strict improvement over merely proving <1 and a much weaker target
-- than the historical 17/32.  The theorem does not identify the old WC3
-- polymer activity with the new unified norm; that one same-object comparison
-- remains the physical analytic seam.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTopDownStrictContractionBudgetExact as Top
import DASHI.Physics.YangMills.BalabanBlockedL2LargeBranchQuarterContractionExact as Blocked

threeFourths : ℚ
threeFourths = + 3 / 4

halfPlusQuarterIsThreeFourths :
  Top.half + Blocked.oneFourth ≡ threeFourths
halfPlusQuarterIsThreeFourths = ℚRing.solve []

blockedL2SameNormGivesThreeQuarterContraction :
  (costs : Top.RationalAdditiveContractionCosts) →
  Top.smallCost costs ≤ Top.half →
  Top.largeCost costs ≤ Blocked.blockedL2Q →
  Top.totalCost costs < threeFourths
blockedL2SameNormGivesThreeQuarterContraction costs smallHalf largeBlocked =
  let
    largeQuarter : Top.largeCost costs < Blocked.oneFourth
    largeQuarter = ℚP.≤-<-trans largeBlocked Blocked.blockedL2QBelowQuarter

    sumThreeQuarters :
      Top.smallCost costs + Top.largeCost costs < threeFourths
    sumThreeQuarters =
      subst
        (λ upper → Top.smallCost costs + Top.largeCost costs < upper)
        halfPlusQuarterIsThreeFourths
        (ℚP.+-mono-≤-< smallHalf largeQuarter)
  in
  ℚP.≤-<-trans (Top.totalBelowSum costs) sumThreeQuarters

blockedL2UnifiedThreeQuarterCompilerLevel : ProofLevel
blockedL2UnifiedThreeQuarterCompilerLevel = machineChecked

-- The two genuinely physical inputs are deliberately visible:
-- (1) the actual corrected unified small branch is <=1/2;
-- (2) its actual large branch is <= the SAME blocked-L2 q.
physicalUnifiedSmallHalfLevel : ProofLevel
physicalUnifiedSmallHalfLevel = conditional

physicalUnifiedLargeBlockedL2Level : ProofLevel
physicalUnifiedLargeBlockedL2Level = conditional
