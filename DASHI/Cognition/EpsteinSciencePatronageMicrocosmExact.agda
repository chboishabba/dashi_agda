module DASHI.Cognition.EpsteinSciencePatronageMicrocosmExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- BROADER SCIENCE-PATRONAGE CONTEXT
--
-- 2026 AP/Nature reporting characterises Epstein's academic role as more than a
-- set of isolated friendships: researchers and institutions sought money,
-- introductions and unusually low-friction patronage, including after his 2008
-- conviction.  Nature explicitly frames the episode as a governance and
-- due-diligence failure around wealthy individual donors.
------------------------------------------------------------------------

data PatronageMechanism : Set where
  privateDonorBrokerage : PatronageMechanism
  lowFrictionPatronage : PatronageMechanism
  academicFundingPressure : PatronageMechanism
  institutionalDueDiligenceFailure : PatronageMechanism
  eliteNetworkAccess : PatronageMechanism
  unconventionalResearchFunding : PatronageMechanism

record SciencePatronageContext : Set where
  constructor science-patronage-context
  field
    directMoney : Bool
    introductions : Bool
    socialAccess : Bool
    bypassesOrdinaryGrantFriction : Bool
    postConvictionRelationshipsObserved : Bool
    institutionalOversightProblemDocumented : Bool
open SciencePatronageContext public

canonicalSciencePatronageContext : SciencePatronageContext
canonicalSciencePatronageContext =
  science-patronage-context true true true true true true

------------------------------------------------------------------------
-- THE YU/PSYCHEDELIC LANE AS A MICRO-COSM
------------------------------------------------------------------------

record MicrocosmReceipt : Set where
  constructor microcosm-receipt
  field
    fundingPresent : Bool
    introductionsPresent : Bool
    conveningPresent : Bool
    unconventionalResearchPresent : Bool
    alteredStateResearchPresent : Bool
    representsWholeScienceNetwork : Bool
open MicrocosmReceipt public

yuPsychedelicMicrocosm : MicrocosmReceipt
yuPsychedelicMicrocosm =
  microcosm-receipt true true true true true false

------------------------------------------------------------------------
-- PROMOTION FIREWALLS
------------------------------------------------------------------------

data PatronageImpliesExpertise : Set where
data NetworkAccessImpliesScientificAuthority : Set where
data MicrocosmImpliesUniversalNetworkControl : Set where
data FundingPressureExcusesDueDiligence : Set where
data UnconventionalResearchImpliesPseudoscience : Set where

sciencePatronageDoesNotImplyScientificExpertise : PatronageImpliesExpertise → ⊥
sciencePatronageDoesNotImplyScientificExpertise ()

networkAccessDoesNotImplyScientificAuthority : NetworkAccessImpliesScientificAuthority → ⊥
networkAccessDoesNotImplyScientificAuthority ()

microcosmDoesNotEstablishUniversalNetworkControl :
  MicrocosmImpliesUniversalNetworkControl → ⊥
microcosmDoesNotEstablishUniversalNetworkControl ()

fundingPressureDoesNotExcuseDueDiligence : FundingPressureExcusesDueDiligence → ⊥
fundingPressureDoesNotExcuseDueDiligence ()

unconventionalDoesNotEqualPseudoscience : UnconventionalResearchImpliesPseudoscience → ⊥
unconventionalDoesNotEqualPseudoscience ()

record EpsteinSciencePatronageBoundary : Set where
  constructor epstein-science-patronage-boundary
  field
    systemicPatronagePatternSupported : Bool
    yuLaneFitsPattern : Bool
    wholeNetworkControlledByEpstein : Bool
    fundingEqualsScientificAuthority : Bool
    institutionalGovernanceFailureRelevant : Bool

canonicalEpsteinSciencePatronageBoundary : EpsteinSciencePatronageBoundary
canonicalEpsteinSciencePatronageBoundary =
  epstein-science-patronage-boundary true true false false true
