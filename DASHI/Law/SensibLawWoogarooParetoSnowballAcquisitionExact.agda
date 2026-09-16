module DASHI.Law.SensibLawWoogarooParetoSnowballAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency
import DASHI.Law.SensibLawWoogarooPopulationConnectivityAcquisitionExact as Acquisition
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Ibrahim
import DASHI.Law.SensibLawWoogarooKoalaEvidenceSnowballIdentifierExact as Identifier
import DASHI.Law.SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact as S102
import DASHI.Law.SensibLawWoogarooS13EssentialityStressTestExact as S13
import DASHI.Law.SensibLawWoogarooEPBC43BHistoricalClearingApplicabilityExact as S43B

------------------------------------------------------------------------
-- WOOGAROO PARETO + SNOWBALL ACQUISITION ROUTER
--
-- Thin routing owner only.  It reuses the canonical Pareto frontier, the
-- existing Woogaroo acquisition leaves/legal-atom bindings, the Ibrahim-style
-- DOI/QID/Dewey/source-role atlas, and the existing source-dependency matrix.
-- No second provenance, identifier, legal-atom or evidence ontology is made.
-- Cost/gain numbers are routing calibration only: not probabilities, legal
-- weights, ecological effect sizes, truth scores or merits scores.
------------------------------------------------------------------------

data S102Requirement : Set where
  independentCurrentEcologicalOpinion : S102Requirement
  currentExecutionRecords : S102Requirement
  anotherHistoricalHabitatMap : S102Requirement
  lidarTreeInventoryNow : S102Requirement

s102ExpertCell : Pareto.RequirementCandidate S102Requirement
s102ExpertCell = Pareto.requirement-candidate
  independentCurrentEcologicalOpinion true true true true 2 6
  "Existing acquisition leaf: independent current ecological opinion applying NCA ss 12/102 to the approved/current project state."

s102ExecutionCell : Pareto.RequirementCandidate S102Requirement
s102ExecutionCell = Pareto.requirement-candidate
  currentExecutionRecords true true true true 1 5
  "Existing acquisition leaf: Condition 6(a), prestart, fauna/arborist and commencement records joined to A12705838."

s102ExtraMapCell : Pareto.RequirementCandidate S102Requirement
s102ExtraMapCell = Pareto.requirement-candidate
  anotherHistoricalHabitatMap true true true true 3 2
  "Another historical habitat map from the already-dependent SHG/project ecology lineage."

s102LidarNowCell : Pareto.RequirementCandidate S102Requirement
s102LidarNowCell = Pareto.requirement-candidate
  lidarTreeInventoryNow true true true true 5 3
  "LiDAR/tree-crown execution before the current-effect and execution-state residuals are paid."

s102Portfolio : List (Pareto.RequirementCandidate S102Requirement)
s102Portfolio = s102ExpertCell ∷ s102ExecutionCell ∷ s102ExtraMapCell ∷ s102LidarNowCell ∷ []

s102FrontierExact :
  Pareto.paretoFrontier s102Portfolio ≡ s102ExpertCell ∷ s102ExecutionCell ∷ []
s102FrontierExact = refl

s102ExpertLeaf : Acquisition.AcquisitionLeafReceipt
s102ExpertLeaf = Acquisition.s102ExpertOpinionLeaf

s102ExecutionLeaf : Acquisition.AcquisitionLeafReceipt
s102ExecutionLeaf = Acquisition.executionLeaf

------------------------------------------------------------------------
-- s 13: population identity, live connectivity and without-site counterfactual.
------------------------------------------------------------------------

data S13Requirement : Set where
  independentViablePopulationIdentity : S13Requirement
  currentConnectivityUpdate : S13Requirement
  withoutSiteCounterfactual : S13Requirement
  another2019HabitatMap : S13Requirement
  lidarMaturityLayerNow : S13Requirement

s13PopulationCell : Pareto.RequirementCandidate S13Requirement
s13PopulationCell = Pareto.requirement-candidate
  independentViablePopulationIdentity true true true true 3 7
  "Existing acquisition leaf: defensible local/regional viable-Koala-population identity joined to Springview/Woogaroo habitat function."

s13ConnectivityCell : Pareto.RequirementCandidate S13Requirement
s13ConnectivityCell = Pareto.requirement-candidate
  currentConnectivityUpdate true true true true 2 4
  "Existing acquisition leaves: current functional-connectivity / habitat-condition / movement-risk evidence testing the 2019 isolation and connectivity assumptions."

s13CounterfactualCell : Pareto.RequirementCandidate S13Requirement
s13CounterfactualCell = Pareto.requirement-candidate
  withoutSiteCounterfactual true true true true 4 8
  "Existing acquisition leaf: effect of removal/severance on persistence, movement, breeding/dispersal and resource access for the identified population."

s13ExtraMapCell : Pareto.RequirementCandidate S13Requirement
s13ExtraMapCell = Pareto.requirement-candidate
  another2019HabitatMap true true true true 2 2
  "Additional historical mapping that does not identify the viable population or pay essentiality."

s13LidarCell : Pareto.RequirementCandidate S13Requirement
s13LidarCell = Pareto.requirement-candidate
  lidarMaturityLayerNow true true true true 5 3
  "LiDAR maturity/canopy structure before population identity and the essentiality counterfactual are resolved."

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

s13PopulationLeaf : Acquisition.AcquisitionLeafReceipt
s13PopulationLeaf = Acquisition.s13PopulationLeaf

s13ConnectivityLeaf : Acquisition.AcquisitionLeafReceipt
s13ConnectivityLeaf = Acquisition.functionalConnectivityLeaf

s13CounterfactualLeaf : Acquisition.AcquisitionLeafReceipt
s13CounterfactualLeaf = Acquisition.counterfactualLeaf

------------------------------------------------------------------------
-- s 43B: first prove that the exemption is actually being relied upon.
------------------------------------------------------------------------

data S43BRequirement : Set where
  actualS43BRelianceRecord : S43BRequirement
  fifteenYearAerialHistory : S43BRequirement
  pre2000UseReconstruction : S43BRequirement
  forestryStatus : S43BRequirement

s43BRelianceCell : Pareto.RequirementCandidate S43BRequirement
s43BRelianceCell = Pareto.requirement-candidate
  actualS43BRelianceRecord true true true true 1 7
  "Primary proponent/agency record actually invoking EPBC s 43B for a current clearing action."

s43BAerialCell : Pareto.RequirementCandidate S43BRequirement
s43BAerialCell = Pareto.requirement-candidate
  fifteenYearAerialHistory true true true false 3 5
  "15-year clearing-history reconstruction: required if reliance becomes live, but currently cannot split the live fibre because no reliance record is source-paid."

s43BPre2000Cell : Pareto.RequirementCandidate S43BRequirement
s43BPre2000Cell = Pareto.requirement-candidate
  pre2000UseReconstruction true true true false 3 4
  "Exact pre-EPBC land-use continuation history: currently inert pending an actual s 43B reliance record."

s43BForestryCell : Pareto.RequirementCandidate S43BRequirement
s43BForestryCell = Pareto.requirement-candidate
  forestryStatus true true true false 2 3
  "Forestry-operation exception status: currently inert pending an actual s 43B reliance record."

s43BPortfolio : List (Pareto.RequirementCandidate S43BRequirement)
s43BPortfolio = s43BRelianceCell ∷ s43BAerialCell ∷ s43BPre2000Cell ∷ s43BForestryCell ∷ []

s43BRelianceOnlyLiveFrontier :
  Pareto.paretoFrontier s43BPortfolio ≡ s43BRelianceCell ∷ []
s43BRelianceOnlyLiveFrontier = refl

------------------------------------------------------------------------
-- Ibrahim / Snowball / identifier coverage is reused, not redefined.
------------------------------------------------------------------------

ibrahimCoverage : Ibrahim.WoogarooIbrahimCoverage
ibrahimCoverage = Ibrahim.currentWoogarooIbrahimCoverage

identifierBoundary : Identifier.KoalaEvidenceIdentifierBoundary
identifierBoundary = Identifier.canonicalKoalaEvidenceIdentifierBoundary

record AttributionParetoBoundary : Set where
  constructor attribution-pareto-boundary
  field
    primarySourceRolesRetained : Bool
    doiQidDeweyCoordinatesRetained : Bool
    sameObjectStatusRetained : Bool
    legalAtomBindingsRetained : Bool
    sourceDependenciesRetained : Bool
    paretoRoutingCreatesAuthority : Bool
    metadataCreatesSameObjectPayment : Bool

canonicalAttributionParetoBoundary : AttributionParetoBoundary
canonicalAttributionParetoBoundary = attribution-pareto-boundary
  true true true true true false false

------------------------------------------------------------------------
-- Current execution route.
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
    sameLineageDocumentGrowthDeferred : Bool

currentParetoRoute : CurrentParetoRoute
currentParetoRoute = current-pareto-route
  "Get 9281 execution/compliance records first: low acquisition cost, immediate timing value, and a true same-object/time join."
  "Obtain an independent current ecological opinion applying ss 12/102 to the approved process/current ecological state, explicitly addressing mitigation and uncertainty."
  "Identify the relevant viable Koala population/community independently of the development boundary."
  "Update realised/current connectivity, barriers, habitat condition and movement-risk evidence."
  "Then run the without-site/severance counterfactual for persistence, movement, breeding/dispersal and resource access."
  "Locate an actual s 43B reliance record before spending on 15-year aerial or pre-2000-use reconstruction."
  true true

------------------------------------------------------------------------
-- Reuse current dependency/case states.
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
-- WrongType / no-promotion boundaries inherited by this router.
------------------------------------------------------------------------

data ParetoFrontierMeansRequirementSatisfied : Set where
data LowestCostMeansBestLegalArgument : Set where
data HighestGainMeansTruth : Set where
data MoreDocumentsMeanMoreIndependentEvidence : Set where
data DOIQIDDeweyMeansSameObjectEvidence : Set where

doNotPromoteFrontierToPayment : ParetoFrontierMeansRequirementSatisfied → ⊥
doNotPromoteFrontierToPayment ()

costDoesNotMeanLegalStrength : LowestCostMeansBestLegalArgument → ⊥
costDoesNotMeanLegalStrength ()

gainDoesNotMeanTruth : HighestGainMeansTruth → ⊥
gainDoesNotMeanTruth ()

multiplicityDoesNotCreateIndependence : MoreDocumentsMeanMoreIndependentEvidence → ⊥
multiplicityDoesNotCreateIndependence ()

metadataDoesNotCreateSameObjectEvidence : DOIQIDDeweyMeansSameObjectEvidence → ⊥
metadataDoesNotCreateSameObjectEvidence ()
