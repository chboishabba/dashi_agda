module DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact where

------------------------------------------------------------------------
-- ROUND82: CMP119/CMP116 SOURCE THEOREM FOR COMPATIBLE NORMALIZED LOCAL
--          EXPECTATION EXPANSIONS, CONDITIONAL ON THE PUBLISHED SMALL-COUPLING
--          FLOW HYPOTHESIS
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- The Introduction stresses that the localization/exponentiated-cluster
-- constructions are general and apply also to conditioned subdomain integrals.
-- Lemma 3 / (2.38) proves exponential localization of the resummed activity.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
-- In Sect. 3, equations (3.44)--(3.47), the numerator and denominator of a
-- normalized expectation are cluster-expanded together.  The resulting terms
-- are anchored on the inserted bond/point and satisfy the same localization
-- bound as (2.42), with the displayed small prefactor.  Immediately after
-- (3.47), Bałaban states that terms whose localization domains lie in the
-- interior do not depend on the finite region and coincide with the whole-
-- lattice terms.  After (2.42), one unit of exponential decay is explicitly
-- spent to obtain a dyadic factor before summing over the scale indices.
--
-- SOURCE BOUNDARY
--
-- The source theorem is conditional on the same admissible small-coupling flow
-- used by the complete-density induction.  It is not a substitute for the
-- missing positive history-dependent beta theorem.  It says that ONCE that
-- small-coupling history exists, local analytic normalized insertions have a
-- compatible, exponentially localized, summable expansion.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum

record CMP119CompatibleLocalExpectationFlow : Set₁ where
  field
    SmallEffectiveCouplingHistory : Set
    LocalInsertionPair : Set

    -- The pair consists of two insertions into the SAME source-native density:
    -- an ordinary Schwinger/local observable and the compact-support
    -- characteristic phase insertion.  Admissibility means both belong to the
    -- local analytic insertion class to which the CMP116/119 construction
    -- applies.
    SourceLocalAnalyticPair : LocalInsertionPair → Set

    -- Published normalized expectation / compatibility / localization theorem,
    -- represented directly at the exact downstream type consumed by Round81.
    sourceSummablePairResponse :
      SmallEffectiveCouplingHistory →
      (pair : LocalInsertionPair) →
      SourceLocalAnalyticPair pair →
      Sum.SameFamilySummableScaleIncrement

open CMP119CompatibleLocalExpectationFlow public

record SourceNativeOrdinaryCharacteristicPair
    (source : CMP119CompatibleLocalExpectationFlow) : Set₁ where
  field
    pair : LocalInsertionPair source
    sourceLocalAnalytic : SourceLocalAnalyticPair source pair

open SourceNativeOrdinaryCharacteristicPair public

sourceCompatibleSameFamilyIncrement :
  (source : CMP119CompatibleLocalExpectationFlow) →
  SmallEffectiveCouplingHistory source →
  (pairData : SourceNativeOrdinaryCharacteristicPair source) →
  Sum.SameFamilySummableScaleIncrement
sourceCompatibleSameFamilyIncrement source small pairData =
  sourceSummablePairResponse source small
    (pair pairData) (sourceLocalAnalytic pairData)

cmp116CMP119CompatibleExpectationSourceLevel : ProofLevel
cmp116CMP119CompatibleExpectationSourceLevel = standardImported

-- Local compact-support phase insertions are standard analytic insertions; the
-- Yang--Mills-specific work is the source-native same-density identification,
-- not a second cluster expansion.  This boundary is intentionally classified
-- as standard imported analysis rather than a new physical YM theorem.
localCharacteristicPhaseInsertionAnalysisLevel : ProofLevel
localCharacteristicPhaseInsertionAnalysisLevel = standardImported

compatibleExpectationToRound81IncrementCompilerLevel : ProofLevel
compatibleExpectationToRound81IncrementCompilerLevel = machineChecked
