module DASHI.Physics.YangMills.BalabanBlockedL2LargeBranchQuarterContractionExact where

------------------------------------------------------------------------
-- ROUND80: EXACT BLOCKED-L2 LARGE-BRANCH NUMERICS
--
-- PRIMARY / SOURCE CONTEXT
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
-- Robert Kotecky and David Preiss,
-- "Cluster expansion for abstract polymer models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- REPOSITORY CROSS-POLLINATION
--
-- The older Sprint95/Sprint103 lane recorded a blocked L=2 weighted-KP factor
--
--   q = 0.23178189475262734
--
-- with entropy factor eta=4 and 4q<1.  Those older modules encode much of the
-- physical derivation as receipt/string authority and therefore are NOT, by
-- themselves, a proof of the new Round79 source-native unified-norm estimate.
--
-- This module extracts only the exact arithmetic content and proves it over Q:
--
--   q = 11589094737631367 / 50000000000000000
--   4 q < 1
--   q < 1/4 < 1/2.
--
-- Hence any SAME-OBJECT theorem identifying the actual unified-norm large
-- polymer contraction cost with a quantity <= q immediately closes the
-- Round79 large-branch requirement q_large < 1/2, with a factor-two margin.
-- No such same-object identification is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

blockedL2Q oneFourth oneHalf four : ℚ
blockedL2Q = + 11589094737631367 / 50000000000000000
oneFourth = + 1 / 4
oneHalf = + 1 / 2
four = + 4 / 1

blockedL2QPositive : 0ℚ < blockedL2Q
blockedL2QPositive = ℚP.positive⁻¹ blockedL2Q

fourQBelowOne : four * blockedL2Q < 1ℚ
fourQBelowOne = ℚP.positive⁻¹ (1ℚ - four * blockedL2Q)

blockedL2QBelowQuarter : blockedL2Q < oneFourth
blockedL2QBelowQuarter =
  let
    scaled : four * blockedL2Q < four * oneFourth
    scaled = subst
      (λ upper → four * blockedL2Q < upper)
      (ℚRing.solve [])
      fourQBelowOne
  in
  let instance fourPositive = ℚ.positive (ℚP.positive⁻¹ four)
  in ℚP.*-cancelˡ-< blockedL2Q oneFourth four scaled

quarterBelowHalf : oneFourth < oneHalf
quarterBelowHalf = ℚP.positive⁻¹ (oneHalf - oneFourth)

blockedL2QBelowHalf : blockedL2Q < oneHalf
blockedL2QBelowHalf = ℚP.<-trans blockedL2QBelowQuarter quarterBelowHalf

record SameUnifiedLargeCostBelowBlockedL2Q : Set where
  field
    largeCost : ℚ
    largeCostNonnegative : 0ℚ ≤ largeCost
    sameObjectBlockedL2Bound : largeCost ≤ blockedL2Q
open SameUnifiedLargeCostBelowBlockedL2Q public

sameUnifiedLargeCostStrictlyBelowHalf :
  (dataSet : SameUnifiedLargeCostBelowBlockedL2Q) →
  largeCost dataSet < oneHalf
sameUnifiedLargeCostStrictlyBelowHalf dataSet =
  ℚP.≤-<-trans (sameObjectBlockedL2Bound dataSet) blockedL2QBelowHalf

sameUnifiedLargeCostStrictlyBelowQuarter :
  (dataSet : SameUnifiedLargeCostBelowBlockedL2Q) →
  largeCost dataSet < oneFourth
sameUnifiedLargeCostStrictlyBelowQuarter dataSet =
  ℚP.≤-<-trans (sameObjectBlockedL2Bound dataSet) blockedL2QBelowQuarter

blockedL2LargeBranchQuarterArithmeticLevel : ProofLevel
blockedL2LargeBranchQuarterArithmeticLevel = machineChecked

-- This is now the only large-branch physical seam exposed by this route:
-- identify the actual Round79 corrected unified-norm large cost with the SAME
-- blocked-L2 physical polymer activity controlled by CMP116/WC3, and prove the
-- comparison largeCost <= blockedL2Q.  The older receipt/string modules do not
-- count as that proof.
physicalUnifiedLargeCostToBlockedL2QLevel : ProofLevel
physicalUnifiedLargeCostToBlockedL2QLevel = conditional
