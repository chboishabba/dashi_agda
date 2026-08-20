module DASHI.Physics.YangMills.BalabanSourceNativeUnifiedThreeQuarterStepExact where

------------------------------------------------------------------------
-- ROUND80: SAME-OBJECT SOURCE-NATIVE L3 COMPILER
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- DASHI CONTRIBUTION
--
-- Remove L3c ("prove the small and large estimates concern the same state") as
-- an independent analytic obligation.  Round76 already defines the strong Clay
-- state by EXTENDING the literal CMP119/CMP122 complete density rather than
-- rebuilding it.  This module therefore indexes both contraction costs by one
-- `SourceNativeUnifiedState` value and one cost decomposition.
--
-- The remaining analytic inputs are exactly two inequalities on that object:
--
--   small/KP cost <= 1/2,
--   large cost    <= q_blocked,
--
-- where Round80 proves q_blocked < 1/4.  The total cost is then <3/4.
--
-- This does not assert either physical inequality.  It does prove that no
-- third source/repository equality or cross-norm provenance lemma is required
-- once the estimates are stated on this carrier.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSourceNativeStrongStateEntryExact as Source
import DASHI.Physics.YangMills.BalabanTopDownStrictContractionBudgetExact as Top
import DASHI.Physics.YangMills.BalabanBlockedL2LargeBranchQuarterContractionExact as Blocked
import DASHI.Physics.YangMills.BalabanBlockedL2UnifiedThreeQuarterContractionExact as ThreeQuarter

record SourceNativeUnifiedStepCosts
    {base : Source.SourceNativeBalabanBaseline}
    (state : Source.SourceNativeUnifiedState base) : Set where
  field
    costs : Top.RationalAdditiveContractionCosts

    -- These interpretation maps make the numerical costs coordinates of THIS
    -- source-native state.  They are not equality receipts to another carrier.
    SmallAndKPCostOf : Source.SourceNativeUnifiedState base → ℚ
    LargeCostOf : Source.SourceNativeUnifiedState base → ℚ
    TotalCostOf : Source.SourceNativeUnifiedState base → ℚ

    smallCostIsStateCost :
      Top.smallCost costs ≡ SmallAndKPCostOf state
    largeCostIsStateCost :
      Top.largeCost costs ≡ LargeCostOf state
    totalCostIsStateCost :
      Top.totalCost costs ≡ TotalCostOf state

open SourceNativeUnifiedStepCosts public

record SourceNativeThreeQuarterPhysicalInputs
    {base : Source.SourceNativeBalabanBaseline}
    {state : Source.SourceNativeUnifiedState base}
    (dataSet : SourceNativeUnifiedStepCosts state) : Set where
  field
    smallStateCostBelowHalf :
      SmallAndKPCostOf dataSet state ≤ Top.half
    largeStateCostBelowBlockedL2 :
      LargeCostOf dataSet state ≤ Blocked.blockedL2Q

open SourceNativeThreeQuarterPhysicalInputs public

sourceNativeUnifiedStepStrictlyBelowThreeQuarters :
  ∀ {base state}
    (dataSet : SourceNativeUnifiedStepCosts {base = base} state) →
  SourceNativeThreeQuarterPhysicalInputs dataSet →
  TotalCostOf dataSet state < ThreeQuarter.threeFourths
sourceNativeUnifiedStepStrictlyBelowThreeQuarters dataSet inputs =
  let
    small : Top.smallCost (costs dataSet) ≤ Top.half
    small =
      subst
        (λ selected → selected ≤ Top.half)
        (smallCostIsStateCost dataSet)
        (smallStateCostBelowHalf inputs)

    large : Top.largeCost (costs dataSet) ≤ Blocked.blockedL2Q
    large =
      subst
        (λ selected → selected ≤ Blocked.blockedL2Q)
        (largeCostIsStateCost dataSet)
        (largeStateCostBelowBlockedL2 inputs)

    total = ThreeQuarter.blockedL2SameNormGivesThreeQuarterContraction
      (costs dataSet) small large
  in
  subst
    (λ selected → selected < ThreeQuarter.threeFourths)
    (totalCostIsStateCost dataSet)
    total

sourceNativeSameObjectContractionCompilerLevel : ProofLevel
sourceNativeSameObjectContractionCompilerLevel = machineChecked

-- The former same-object/cross-norm bookkeeping seam is eliminated by the
-- carrier choice above.  The remaining L3 physical work is now only the two
-- quantitative estimates themselves.
physicalSourceNativeSmallHalfLevel : ProofLevel
physicalSourceNativeSmallHalfLevel = conditional

physicalSourceNativeLargeBlockedL2Level : ProofLevel
physicalSourceNativeLargeBlockedL2Level = conditional
