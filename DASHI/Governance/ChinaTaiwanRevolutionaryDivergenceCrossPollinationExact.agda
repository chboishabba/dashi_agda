module DASHI.Governance.ChinaTaiwanRevolutionaryDivergenceCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Governance.ComparativeMarxianRevolutionaryTranslationFamilyExact as Marxian
import DASHI.Governance.ChinaTaiwanHistoricalSuccessionIdentityExact as History
import DASHI.Governance.ChinaTaiwanUSPolicyPluralAuthority2026Exact as USPolicy
import DASHI.Economics.CUDAROCmTSMCManufacturingCrossPollinationExact as TSMC

------------------------------------------------------------------------
-- CHINA / TAIWAN DIVERGENCE CROSS-POLLINATION
--
-- The shared Chinese civil-war genealogy forks into divergent institutional
-- histories.  PRC revolutionary state formation and ROC-on-Taiwan
-- authoritarian continuity/democratisation are represented as different
-- process histories.  Present U.S. policy and semiconductor interdependence are
-- later layers, not retroactive causes of the 1949 fork.
------------------------------------------------------------------------

data DivergenceAxis : Set where
  civilWarOutcomeAxis : DivergenceAxis
  revolutionaryStateAxis : DivergenceAxis
  authoritarianContinuityAxis : DivergenceAxis
  democratisationAxis : DivergenceAxis
  nationalIdentityAxis : DivergenceAxis
  sovereigntyClaimAxis : DivergenceAxis
  usSecurityPolicyAxis : DivergenceAxis
  semiconductorPowerAxis : DivergenceAxis

record CrossStraitDivergence : Set where
  constructor cross-strait-divergence
  field
    chinaRevolutionaryProfile : Marxian.RevolutionaryTranslationProfile
    rocRetreatTransition : History.HistoricalTransition
    taiwanDemocratisationTransition : History.HistoricalTransition
    currentUSExecutivePosition : USPolicy.PolicyPosition
    currentCongressionalPressure : USPolicy.PolicyPosition
    sharedCivilWarHistory : Bool
    samePresentPoliticalSystem : Bool
    sharedHistoryDeterminesPresentIdentity : Bool
    semiconductorPowerSettlesSovereignty : Bool
    usPolicySettlesHistoricalLegitimacy : Bool

open CrossStraitDivergence public

canonicalCrossStraitDivergence : CrossStraitDivergence
canonicalCrossStraitDivergence =
  cross-strait-divergence
    Marxian.chinaProfile
    History.rocCivilWarRetreat
    History.rocAuthoritarianToDemocraticTaiwan
    USPolicy.trumpAdministrationUnchangedPolicy
    USPolicy.wickerSecurityPressure
    true false false false false

data SharedCivilWarMeansSamePresentPolity : Set where
data SemiconductorCentralityDeterminesPoliticalStatus : Set where
data USAlignmentDeterminesTaiwaneseIdentity : Set where
data PRCRevolutionaryHistoryDeterminesTaiwanPoliticalTrajectory : Set where

sharedCivilWarDoesNotMeanSamePresentPolity :
  SharedCivilWarMeansSamePresentPolity → ⊥
sharedCivilWarDoesNotMeanSamePresentPolity ()

semiconductorCentralityDoesNotDeterminePoliticalStatus :
  SemiconductorCentralityDeterminesPoliticalStatus → ⊥
semiconductorCentralityDoesNotDeterminePoliticalStatus ()

usAlignmentDoesNotDetermineTaiwaneseIdentity :
  USAlignmentDeterminesTaiwaneseIdentity → ⊥
usAlignmentDoesNotDetermineTaiwaneseIdentity ()

prcRevolutionDoesNotDetermineTaiwanTrajectory :
  PRCRevolutionaryHistoryDeterminesTaiwanPoliticalTrajectory → ⊥
prcRevolutionDoesNotDetermineTaiwanTrajectory ()
