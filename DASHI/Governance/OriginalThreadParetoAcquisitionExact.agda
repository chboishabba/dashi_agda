module DASHI.Governance.OriginalThreadParetoAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.IRGCOpenLetter2026SourceAtlasExact as IRGCSources
import DASHI.Governance.IranianRevolutionaryIntellectualGenealogyExact as IranGenealogy
import DASHI.Governance.IRGCReviewedEventDualChronologyPacketExact as IRGCPacket

------------------------------------------------------------------------
-- ORIGINAL-THREAD SOURCE-ACQUISITION PARETO
--
-- Cost/gain values are routing calibration only. They are not truth,
-- political merit, probability, source authority or historical importance.
--
-- A candidate enters the live frontier only when it is required for the
-- current mechanism consumer, source-role admissible, and capable of
-- splitting/closing a live residual.
------------------------------------------------------------------------

data OriginalThreadRequirement : Set where
  irgcExactPrimarySpans : OriginalThreadRequirement
  iranGenealogyReviewedJoin : OriginalThreadRequirement
  irgcCausalMechanismReceipt : OriginalThreadRequirement
  friendlyjordiesGarnautFixtureRefresh : OriginalThreadRequirement
  friendlyjordiesFallaciesTypedBinding : OriginalThreadRequirement
  irisDenaOperationalRecord : OriginalThreadRequirement
  chinaEconomicLeadershipCrossSourceJoin : OriginalThreadRequirement
  broadCountryExpansion : OriginalThreadRequirement

irgcSpanCell : Pareto.RequirementCandidate OriginalThreadRequirement
irgcSpanCell = Pareto.requirement-candidate
  irgcExactPrimarySpans
  true true true true
  1 9
  "Acquire exact page/span locators in the primary IRGC PDF for the people/state distinction, common-oppressor frame, agency appeal and neighbouring argument transitions. One source pass unlocks reviewed statement roots and makes later causal joins auditable."

iranGenealogyJoinCell : Pareto.RequirementCandidate OriginalThreadRequirement
iranGenealogyJoinCell = Pareto.requirement-candidate
  iranGenealogyReviewedJoin
  true true true true
  3 9
  "Review exact passages for Shariati/Marxian/Fanonian/Third-Worldist and Iranian-left/Khomeini continuity edges, then construct explicit join bases rather than source-list adjacency."

irgcCausalCell : Pareto.RequirementCandidate OriginalThreadRequirement
irgcCausalCell = Pareto.requirement-candidate
  irgcCausalMechanismReceipt
  true true true false
  4 10
  "Mechanism receipt connecting historical revolutionary grammar to the 2026 letter. Currently inert until exact primary spans and reviewed genealogy joins are paid."

fjordiesGarnautCell : Pareto.RequirementCandidate OriginalThreadRequirement
fjordiesGarnautCell = Pareto.requirement-candidate
  friendlyjordiesGarnautFixtureRefresh
  true true true true
  1 5
  "Refresh/archive-bind the Garnaut authority wrapper on the dedicated SensibLaw branch; current pinned static fixture does not pay the Garnaut text."

fjordiesFallaciesCell : Pareto.RequirementCandidate OriginalThreadRequirement
fjordiesFallaciesCell = Pareto.requirement-candidate
  friendlyjordiesFallaciesTypedBinding
  true true true true
  2 4
  "Bind generator-supported fallacies/framing output into a checked-in proposition root, claim leaf and comparison item with source trace."

irisDenaRecordCell : Pareto.RequirementCandidate OriginalThreadRequirement
irisDenaRecordCell = Pareto.requirement-candidate
  irisDenaOperationalRecord
  true true true true
  4 7
  "Acquire an authoritative operational/legal record capable of testing crew-role, command and participation claims beyond public government statements and news reporting."

chinaLeadershipJoinCell : Pareto.RequirementCandidate OriginalThreadRequirement
chinaLeadershipJoinCell = Pareto.requirement-candidate
  chinaEconomicLeadershipCrossSourceJoin
  true true true true
  3 5
  "Join PRC official self-position to independent comparable economic indicators without scalarising manufacturing, trade, finance, currency and domestic-demand dimensions into a winner score."

broadExpansionCell : Pareto.RequirementCandidate OriginalThreadRequirement
broadExpansionCell = Pareto.requirement-candidate
  broadCountryExpansion
  false true true false
  5 2
  "Add more countries/actors before the current reviewed-event and mechanism residuals are closed."

originalThreadPortfolio :
  List (Pareto.RequirementCandidate OriginalThreadRequirement)
originalThreadPortfolio =
    irgcSpanCell
  ∷ iranGenealogyJoinCell
  ∷ irgcCausalCell
  ∷ fjordiesGarnautCell
  ∷ fjordiesFallaciesCell
  ∷ irisDenaRecordCell
  ∷ chinaLeadershipJoinCell
  ∷ broadExpansionCell
  ∷ []

irgcSpanOnFrontier :
  Pareto.onParetoFrontier? originalThreadPortfolio irgcSpanCell ≡ true
irgcSpanOnFrontier = refl

iranGenealogyJoinOnFrontier :
  Pareto.onParetoFrontier? originalThreadPortfolio iranGenealogyJoinCell ≡ true
iranGenealogyJoinOnFrontier = refl

fjordiesGarnautOnFrontier :
  Pareto.onParetoFrontier? originalThreadPortfolio fjordiesGarnautCell ≡ true
fjordiesGarnautOnFrontier = refl

irgcCausalCurrentlyInert :
  Pareto.eligible? irgcCausalCell ≡ false
irgcCausalCurrentlyInert = refl

broadExpansionOffFrontier :
  Pareto.onParetoFrontier? originalThreadPortfolio broadExpansionCell ≡ false
broadExpansionOffFrontier = refl

------------------------------------------------------------------------
-- Attribution / Snowball remains authoritative and separate from the Pareto
-- route.  Ranking never upgrades source role.
------------------------------------------------------------------------

irgcPrimarySnowball :
  Snowball.SourceRoleSnowballReceipt IRGCSources.irgcPrimaryLetter
irgcPrimarySnowball =
  Snowball.canonicalSourceRoleSnowballReceipt IRGCSources.irgcPrimaryLetter

iranGenealogySnowball :
  Snowball.SourceRoleSnowballReceipt IranGenealogy.boroujerdiModernizingIslam
iranGenealogySnowball =
  Snowball.canonicalSourceRoleSnowballReceipt IranGenealogy.boroujerdiModernizingIslam

currentIRGCPacket : IRGCPacket.IRGCDualChronologyPacket
currentIRGCPacket = IRGCPacket.canonicalIRGCDualChronologyPacket

record CurrentOriginalThreadParetoRoute : Set where
  constructor current-original-thread-pareto-route
  field
    first : String
    second : String
    third : String
    deferredUntilParentsPaid : String
    breadthExpansionDeferred : Bool
    paretoPriorityCreatesAuthority : Bool
    paretoPriorityCreatesTruth : Bool

open CurrentOriginalThreadParetoRoute public

currentRoute : CurrentOriginalThreadParetoRoute
currentRoute =
  current-original-thread-pareto-route
    "1. Exact-span pass over the primary IRGC letter."
    "2. Exact-passage reviewed joins for the highest-leverage Iran genealogy edges."
    "3. In parallel, pay the low-cost Friendlyjordies Garnaut fixture refresh on PR #1078."
    "Only after 1+2: causal mechanism receipt relating historical grammar to the 2026 letter."
    true false false

data ParetoPriorityMeansSourceAuthority : Set where
data ParetoPriorityMeansTruth : Set where
data HighestGainMaySkipParentResidual : Set where
data OffFrontierRequirementIsDeleted : Set where

paretoPriorityDoesNotCreateSourceAuthority :
  ParetoPriorityMeansSourceAuthority → ⊥
paretoPriorityDoesNotCreateSourceAuthority ()

paretoPriorityDoesNotCreateTruth :
  ParetoPriorityMeansTruth → ⊥
paretoPriorityDoesNotCreateTruth ()

highGainMayNotSkipParentResidual :
  HighestGainMaySkipParentResidual → ⊥
highGainMayNotSkipParentResidual ()

offFrontierDoesNotDeleteRequirement :
  OffFrontierRequirementIsDeleted → ⊥
offFrontierDoesNotDeleteRequirement ()
