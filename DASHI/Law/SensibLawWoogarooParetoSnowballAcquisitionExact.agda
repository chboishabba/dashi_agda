module DASHI.Law.SensibLawWoogarooParetoSnowballAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency
import DASHI.Law.SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact as S102
import DASHI.Law.SensibLawWoogarooS13EssentialityStressTestExact as S13
import DASHI.Law.SensibLawWoogarooEPBC43BHistoricalClearingApplicabilityExact as S43B

------------------------------------------------------------------------
-- WOOGAROO PARETO + SNOWBALL ACQUISITION ROUTER
--
-- Reuses the existing finite-requirement Pareto machinery.  The numerical
-- cost/gain values below are routing calibration only: they rank currently
-- live information demands.  They are not probabilities, legal weights,
-- ecological effect sizes, or merits scores.
------------------------------------------------------------------------

data S102Requirement : Set where
  independentCurrentEcologicalOpinion : S102Requirement
  currentExecutionRecords : S102Requirement
  anotherHistoricalHabitatMap : S102Requirement
  lidarTreeInventoryNow : S102Requirement

s102ExpertCell : Pareto.RequirementCandidate S102Requirement
s102ExpertCell = Pareto.requirement-candidate
  independentCurrentEcologicalOpinion
  true true true true
  2 6
  "Independent current ecological opinion applying NCA ss 12/102 to the approved 9281 process and current habitat/wildlife state."

s102ExecutionCell : Pareto.RequirementCandidate S102Requirement
s102ExecutionCell = Pareto.requirement-candidate
  currentExecutionRecords
  true true true true
  1 5
  "Condition 6(a), prestart, fauna/arborist and commencement records joined to A12705838."

s102ExtraMapCell : Pareto.RequirementCandidate S102Requirement
s102ExtraMapCell = Pareto.requirement-candidate
  anotherHistoricalHabitatMap
  true true true true
  3 2
  "Another habitat map from the same historical project ecology lineage."

s102LidarNowCell : Pareto.RequirementCandidate S102Requirement
s102LidarNowCell = Pareto.requirement-candidate
  lidarTreeInventoryNow
  true true true true
  5 3
  "LiDAR-derived individual-tree/crown layer before the current legal-effect and execution residuals are paid."

s102Portfolio : List (Pareto.RequirementCandidate S102Requirement)
s102Portfolio = s102ExpertCell ∷ s102ExecutionCell ∷ s102ExtraMapCell ∷ s102LidarNowCell ∷ []

s102ExpertOnFrontier : Pareto.onParetoFrontier? s102Portfolio s102ExpertCell ≡ true
s102ExpertOnFrontier = refl

s102ExecutionOnFrontier : Pareto.onParetoFrontier? s102Portfolio s102ExecutionCell ≡ true
s102ExecutionOnFrontier = refl

s102ExtraMapOffFrontier : Pareto.onParetoFrontier? s102Portfolio s102ExtraMapCell ≡ false
s102ExtraMapOffFrontier = refl

s102LidarNowOffFrontier : Pareto.onParetoFrontier? s102Portfolio s102LidarNowCell ≡ false
s102LidarNowOffFrontier = refl

s102FrontierExact :
  Pareto.paretoFrontier s102Portfolio ≡ s102ExpertCell ∷ s102ExecutionCell ∷ []
s102FrontierExact = refl

------------------------------------------------------------------------
-- s 13: population identity and present connectivity/counterfactual evidence.
------------------------------------------------------------------------

data S13Requirement : Set where
  independentViablePopulationIdentity : S13Requirement
  currentConnectivityUpdate : S13Requirement
  withoutSiteCounterfactual : S13Requirement
  another2019HabitatMap : S13Requirement
  lidarMaturityLayerNow : S13Requirement

s13PopulationCell : Pareto.RequirementCandidate S13Requirement
s13PopulationCell = Pareto.requirement-candidate
  independentViablePopulationIdentity
  true true true true
  3 7
  "Independent identification of the biologically relevant viable Koala population/community joined to the Woogaroo/Springview habitat function."

s13ConnectivityCell : Pareto.RequirementCandidate S13Requirement
s13ConnectivityCell = Pareto.requirement-candidate
  currentConnectivityUpdate
  true true true true
  2 4
  "Current corridor/barrier/development-pressure evidence testing whether the 2019 connectivity and isolation assumptions still hold."

s13CounterfactualCell : Pareto.RequirementCandidate S13Requirement
s13CounterfactualCell = Pareto.requirement-candidate
  withoutSiteCounterfactual
  true true true true
  4 8
  "Expert counterfactual: effect of removal/severance on persistence, movement, breeding/dispersal and resource access for the identified population."

s13ExtraMapCell : Pareto.RequirementCandidate S13Requirement
s13ExtraMapCell = Pareto.requirement-candidate
  another2019HabitatMap
  true true true true
  2 2
  "Additional historical habitat mapping that does not identify the viable population or pay essentiality."

s13LidarCell : Pareto.RequirementCandidate S13Requirement
s13LidarCell = Pareto.requirement-candidate
  lidarMaturityLayerNow
  true true true true
  5 3
  "LiDAR maturity/canopy structure before population identity and essentiality counterfactual are resolved."

s13Portfolio : List (Pareto.RequirementCandidate S13Requirement)
s13Portfolio =
  s13PopulationCell ∷ s13ConnectivityCell ∷ s13CounterfactualCell ∷
  s13ExtraMapCell ∷ s13LidarCell ∷ []

s13PopulationOnFrontier : Pareto.onParetoFrontier? s13Portfolio s13PopulationCell ≡ true
s13PopulationOnFrontier = refl

s13ConnectivityOnFrontier : Pareto.onParetoFrontier? s13Portfolio s13ConnectivityCell ≡ true
s13ConnectivityOnFrontier = refl

s13CounterfactualOnFrontier : Pareto.onParetoFrontier? s13Portfolio s13CounterfactualCell ≡ true
s13CounterfactualOnFrontier = refl

s13ExtraMapOffFrontier : Pareto.onParetoFrontier? s13Portfolio s13ExtraMapCell ≡ false
s13ExtraMapOffFrontier = refl

s13LidarOffFrontier : Pareto.onParetoFrontier? s13Portfolio s13LidarCell ≡ false
s13LidarOffFrontier = refl

------------------------------------------------------------------------
-- s 43B: do not spend on historical reconstruction until reliance is live.
------------------------------------------------------------------------

data S43BRequirement : Set where
  actualS43BRelianceRecord : S43BRequirement
  fifteenYearAerialHistory : S43BRequirement
  pre2000UseReconstruction : S43BRequirement
  forestryStatus : S43BRequirement

s43BRelianceCell : Pareto.RequirementCandidate S43BRequirement
s43BRelianceCell = Pareto.requirement-candidate
  actualS43BRelianceRecord
  true true true true
  1 7
  "Primary proponent/agency record actually invoking EPBC s 43B for a current clearing action."

s43BAerialCell : Pareto.RequirementCandidate S43BRequirement
s43BAerialCell = Pareto.requirement-candidate
  fifteenYearAerialHistory
  true true true false
  3 5
  "15-year historical clearing reconstruction; required only after a live s 43B reliance fibre exists."

s43BPre2000Cell : Pareto.RequirementCandidate S43BRequirement
s43BPre2000Cell = Pareto.requirement-candidate
  pre2000UseReconstruction
  true true true false
  3 4
  "Exact pre-EPBC land-use continuation history; currently inert because no s 43B reliance record is source-paid."

s43BForestryCell : Pareto.RequirementCandidate S43BRequirement
s43BForestryCell = Pareto.requirement-candidate
  forestryStatus
  true true true false
  2 3
  "Forestry-operation exception status; currently inert until a party actually relies on s 43B."

s43BPortfolio : List (Pareto.RequirementCandidate S43BRequirement)
s43BPortfolio = s43BRelianceCell ∷ s43BAerialCell ∷ s43BPre2000Cell ∷ s43BForestryCell ∷ []

s43BRelianceOnlyLiveFrontier :
  Pareto.paretoFrontier s43BPortfolio ≡ s43BRelianceCell ∷ []
s43BRelianceOnlyLiveFrontier = refl

------------------------------------------------------------------------
-- Ibrahim-style Snowball attribution/identifier discipline for acquisitions.
------------------------------------------------------------------------

data IdentifierState : Set where
  verified : String → IdentifierState
  unresolved : String → IdentifierState
  notApplicable : String → IdentifierState

data SourceTier : Set where
  primarySource : SourceTier
  secondarySource : SourceTier
  expertDerivedSource : SourceTier
  runtimeDerivedSource : SourceTier

record SnowballAcquisitionIdentity : Set where
  constructor snowball-acquisition-identity
  field
    acquisitionName : String
    sourceTier : SourceTier
    primaryIdentity : String
    doiState : IdentifierState
    qidState : IdentifierState
    deweyState : IdentifierState
    authorityRole : String
    upstreamDependency : String
    consumer : String
    noPromotionBoundary : String

open SnowballAcquisitionIdentity public

s102ExpertIdentity : SnowballAcquisitionIdentity
s102ExpertIdentity = snowball-acquisition-identity
  "Current independent s 102 ecological opinion"
  expertDerivedSource
  "Signed/dated expert report or declaration identifying author, qualifications, instructions, materials considered, methods and conclusions"
  (notApplicable "A commissioned expert opinion need not have a DOI; if it cites scientific literature, each cited publication retains its own DOI identity.")
  (unresolved "Expert-person QID is optional identity metadata and must not be guessed before author identity is known.")
  (unresolved "Dewey classification may index the ecology subject matter but is not source authority and is not required before the report exists.")
  "Independent ecological evidence applying the actual statutory question; not legal authority."
  "Must disclose whether it independently examines current evidence or merely restates SHG/project ecology."
  "NCA s 102 likely significant detrimental effect"
  "Expert authorship, DOI/QID/Dewey metadata, qualifications and independence do not themselves prove the statutory conclusion."

s102ExecutionIdentity : SnowballAcquisitionIdentity
s102ExecutionIdentity = snowball-acquisition-identity
  "9281 current execution/compliance record set"
  primarySource
  "Ipswich City Council / applicant records tied to 9281/2024/OW and A12705838: Condition 6(a), prestart, fauna/arborist and commencement records"
  (notApplicable "Government/administrative records ordinarily have no DOI; exact application/document IDs and dates are the primary identifiers.")
  (unresolved "Institution/person QIDs are optional lookup metadata and do not replace Council document identity.")
  (notApplicable "Dewey is not the primary identity system for an operational-works compliance record.")
  "Primary factual evidence for current execution state."
  "Must be joined to the exact approval/application/time state; a generic Council record does not pay execution for 9281."
  "s 102 urgency / current threatening-process state"
  "Approval, compliance-document existence, and actual commencement remain separate propositions."

s13PopulationIdentity : SnowballAcquisitionIdentity
s13PopulationIdentity = snowball-acquisition-identity
  "Independent viable-Koala-population study / expert population identification"
  expertDerivedSource
  "Study/report defining the biologically relevant population/community, spatial extent, movement/connectivity assumptions and evidence basis"
  (unresolved "Record DOI when the population evidence is a published study; otherwise preserve report/agency identifier instead of inventing a DOI.")
  (unresolved "Species/population/place QIDs may be recorded as semantic coordinates only after exact entity resolution; they do not establish population identity.")
  (unresolved "Ecology/biogeography Dewey classification may be attached for discovery after exact source identity; classification does not pay essentiality.")
  "Independent ecological evidence for the population half of the s 13 relation."
  "Must be independent of merely drawing the population boundary around the development site."
  "NCA s 13 essentiality"
  "Species occurrence, species QID, habitat polygon or project boundary does not identify the legally/biologically relevant viable population automatically."

s43BRelianceIdentity : SnowballAcquisitionIdentity
s43BRelianceIdentity = snowball-acquisition-identity
  "Actual EPBC s 43B reliance record"
  primarySource
  "Exact proponent/agency legal or assessment record asserting s 43B lawful-continuation exemption for a current clearing action"
  (notApplicable "The primary identity is the exact governmental/proponent record, not a DOI.")
  (unresolved "Agency/company/QID metadata is optional and cannot substitute for the exact reliance document.")
  (notApplicable "Dewey classification is not necessary to establish the existence or scope of a legal reliance record.")
  "Primary evidence that s 43B is actually in issue for the exact action."
  "Must identify the action/parcel/activity and the exemption relied on; general discussion of s 43B is not reliance."
  "EPBC s 43B applicability"
  "Historical aerial evidence or long-uncleared forest does not create an s 43B dispute where no party relies on s 43B."

------------------------------------------------------------------------
-- Current Pareto execution summary.
------------------------------------------------------------------------

record CurrentParetoRoute : Set where
  constructor current-pareto-route
  field
    s102First : String
    s102Second : String
    s13First : String
    s13Second : String
    s13Third : String
    s43BFirst : String
    lidarDeferred : Bool
    moreSameLineageSHGDocumentsDeferred : Bool

currentParetoRoute : CurrentParetoRoute
currentParetoRoute = current-pareto-route
  "Get current execution/compliance records: lowest cost and high immediate urgency gain."
  "Get an independent current ecological opinion applying ss 12/102 to the approved process/current state."
  "Identify the viable Koala population/community independently of the development boundary."
  "Update current connectivity/barrier/development-pressure evidence."
  "Run the without-site/severance counterfactual once population identity is paid."
  "First locate an actual s 43B reliance record; do not lead with aerial-history reconstruction."
  true
  true

------------------------------------------------------------------------
-- Reuse of current case/dependency state.
------------------------------------------------------------------------

s102State : S102.S102CaseState
s102State = S102.currentS102CaseState

s13State : S13.S13StressTest
s13State = S13.currentS13StressTest

s43BState : S43B.CurrentS43BConclusion
s43BState = S43B.currentS43BConclusion

s102Dependency : Dependency.ConsumerDependencyState
s102Dependency = Dependency.s102DependencyState

s13Dependency : Dependency.ConsumerDependencyState
s13Dependency = Dependency.s13DependencyState

s43BDependency : Dependency.ConsumerDependencyState
s43BDependency = Dependency.s43BDependencyState

------------------------------------------------------------------------
-- WrongType / no-promotion boundaries.
------------------------------------------------------------------------

data ParetoFrontierMeansRequirementSatisfied : Set where
data LowestCostMeansBestLegalArgument : Set where
data HighestGainMeansTruth : Set where
data MoreDocumentsMeanMoreIndependentEvidence : Set where
data DOIEqualsAuthority : Set where
data QIDEqualsIdentityProof : Set where
data DeweyEqualsLegalRelevance : Set where

doNotPromoteFrontierToPayment : ParetoFrontierMeansRequirementSatisfied → ⊥
doNotPromoteFrontierToPayment ()

costDoesNotMeanLegalStrength : LowestCostMeansBestLegalArgument → ⊥
costDoesNotMeanLegalStrength ()

gainDoesNotMeanTruth : HighestGainMeansTruth → ⊥
gainDoesNotMeanTruth ()

multiplicityDoesNotCreateIndependence : MoreDocumentsMeanMoreIndependentEvidence → ⊥
multiplicityDoesNotCreateIndependence ()

doiDoesNotCreateAuthority : DOIEqualsAuthority → ⊥
doiDoesNotCreateAuthority ()

qidDoesNotCreateIdentityProof : QIDEqualsIdentityProof → ⊥
qidDoesNotCreateIdentityProof ()

deweyDoesNotCreateLegalRelevance : DeweyEqualsLegalRelevance → ⊥
deweyDoesNotCreateLegalRelevance ()
