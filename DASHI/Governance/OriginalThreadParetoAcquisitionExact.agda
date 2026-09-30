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
  true true true false
  1 5
  "PAID by SensibLaw archive recovery: authority-wrapper fixture now pins the Garnaut nested-attribution unit; Agda PR #1078 carries bidirectional M12 traces and retains external-world verification debt."

fjordiesFallaciesCell : Pareto.RequirementCandidate OriginalThreadRequirement
fjordiesFallaciesCell = Pareto.requirement-candidate
  friendlyjordiesFallaciesTypedBinding
  true true true false
  2 4
  "PAID by recovered archive unit plus right-only proposition/claim/comparison binding on Agda PR #1078; absence of a Friendlyjordies-source fallacies claim is explicit rather than orphaned."

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

fjordiesGarnautPaidDropsFromFrontier :
  Pareto.onParetoFrontier? originalThreadPortfolio fjordiesGarnautCell ≡ false
fjordiesGarnautPaidDropsFromFrontier = refl

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
    "1. Pursue the highest remaining independent geopolitical evidence leaf: IRIS Dena operational/command record."
    "2. In parallel, complete the China official-self-position versus independent geo-economic indicator join."
    "3. Recompute the frontier only after those same-object/source-role checks."
    "IRGC spans, Iran genealogy joins, bounded IRGC mechanism, Garnaut archive binding and fallacies source binding are paid and off the live frontier."
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
