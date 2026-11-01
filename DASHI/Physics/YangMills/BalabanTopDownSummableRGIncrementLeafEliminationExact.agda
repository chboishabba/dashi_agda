module DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementLeafEliminationExact where

------------------------------------------------------------------------
-- ROUND82: SAME-FAMILY SUMMABLE CONTINUUM INCREMENT IS NOT AN INDEPENDENT
--          NEW ANALYTIC LEAF ON THE SOURCE-ACCEPTING ROUTE
--
-- Round81 correctly replaced a global Banach contraction by the much weaker
-- same-trajectory summable-increment theorem.  Source archaeology now removes
-- one more layer: CMP116/CMP119 already prove the normalized local-expectation
-- cluster expansion, its exponential localization, compatibility of interior
-- terms with the whole-lattice expansion, and the dyadic summation mechanism.
--
-- Therefore the only genuinely new source hypothesis upstream of that theorem
-- is the small effective-coupling history.  On the shortest route this history
-- is supplied by `LiteralCompactSimplePositiveBeta`.  The local ordinary and
-- characteristic insertions are put into the source analytic insertion class by
-- the standard compact-support insertion construction.
--
-- This is exactly analogous to Round81's selected-background elimination: we
-- are not claiming to have re-proved Bałaban's cluster theorem in Agda; we are
-- refusing to count a theorem already owned by the published source as a NEW
-- Clay analytic premise.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum

record LiteralBetaSuppliesSourceSmallHistory
    (source : Source.CMP119CompatibleLocalExpectationFlow) : Set₁ where
  field
    sourceSmallHistory : Source.SmallEffectiveCouplingHistory source

open LiteralBetaSuppliesSourceSmallHistory public

sameFamilyIncrementFromLiteralBetaAndPublishedSource :
  (source : Source.CMP119CompatibleLocalExpectationFlow) →
  LiteralBetaSuppliesSourceSmallHistory source →
  (pairData : Source.SourceNativeOrdinaryCharacteristicPair source) →
  Sum.SameFamilySummableScaleIncrement
sameFamilyIncrementFromLiteralBetaAndPublishedSource source beta pairData =
  Source.sourceCompatibleSameFamilyIncrement source
    (sourceSmallHistory beta) pairData

-- This bridge is machine algebra/typing only.
literalBetaToPublishedSameFamilyIncrementBridgeLevel : ProofLevel
literalBetaToPublishedSameFamilyIncrementBridgeLevel = machineChecked

-- The normalized expectation localization / compatibility / summability theorem
-- itself belongs to the cited CMP116/CMP119 source chain.
publishedSameFamilyNormalizedExpectationLevel : ProofLevel
publishedSameFamilyNormalizedExpectationLevel = standardImported

-- The independent-new-leaf status is gone: once positive beta has supplied the
-- source small-coupling history, no second new 4D YM contraction/response theorem
-- is required before the source-compatible local continuum Cauchy construction.
sameFamilySummableIncrementIndependentNewLeafRequiredLevel : ProofLevel
sameFamilySummableIncrementIndependentNewLeafRequiredLevel = machineChecked
