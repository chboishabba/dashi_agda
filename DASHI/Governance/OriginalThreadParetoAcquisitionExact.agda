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
  true true true false
  1 9
  "PAID for the selected argument moves by IRGCOpenLetter2026PrimarySpanReceiptsExact using the Tasnim full-text primary HTML carrier. PDF byte identity remains separately unpaid but is not required by the current mechanism consumer."

iranGenealogyJoinCell : Pareto.RequirementCandidate OriginalThreadRequirement
iranGenealogyJoinCell = Pareto.requirement-candidate
  iranGenealogyReviewedJoin
  true true true false
  3 9
  "PAID for the selected high-leverage edges by IranianRevolutionaryGenealogyReviewedJoinExact: Marxian field to Shariati, Shariati to revolutionary generation, and Iranian-left neocolonial framing to Khomeini's West discourse."

irgcCausalCell : Pareto.RequirementCandidate OriginalThreadRequirement
irgcCausalCell = Pareto.requirement-candidate
  irgcCausalMechanismReceipt
  true true true false
  4 10
  "PAID by IRGCMostazafinInstitutionalGrammarMechanismExact for a bounded institutional-grammar continuity claim. Direct textual borrowing, ontology identity and total explanation remain explicitly false."

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

irgcSpanPaidDropsFromFrontier :
  Pareto.onParetoFrontier? originalThreadPortfolio irgcSpanCell ≡ false
irgcSpanPaidDropsFromFrontier = refl

iranGenealogyJoinPaidDropsFromFrontier :
  Pareto.onParetoFrontier? originalThreadPortfolio iranGenealogyJoinCell ≡ false
iranGenealogyJoinPaidDropsFromFrontier = refl

fjordiesGarnautOnFrontier :
  Pareto.onParetoFrontier? originalThreadPortfolio fjordiesGarnautCell ≡ true
fjordiesGarnautOnFrontier = refl

irgcCausalPaidDropsFromFrontier :
  Pareto.onParetoFrontier? originalThreadPortfolio irgcCausalCell ≡ false
irgcCausalPaidDropsFromFrontier = refl

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
    "1. Pay the low-cost Friendlyjordies Garnaut fixture refresh on PR #1078."
    "2. Bind Friendlyjordies fallacies/framing only if an archive-backed source unit is present."
    "3. Then pursue the highest remaining independent geopolitical evidence leaf: IRIS Dena operational/command record or China cross-source geo-economic join, depending source availability."
    "The selected IRGC spans, Iran genealogy joins and bounded institutional-grammar mechanism are paid and have dropped from the live frontier."
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
