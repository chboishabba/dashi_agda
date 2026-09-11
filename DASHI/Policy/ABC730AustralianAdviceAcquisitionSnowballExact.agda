module DASHI.Policy.ABC730AustralianAdviceAcquisitionSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Policy.ABC730AustralianImplementationSnowballExact as Australia
import DASHI.Policy.ABC730AustralianOriginBaselineExact as Origin
import DASHI.Policy.ABC730C029IbrahimSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- Public-advice acquisition boundary.
--
-- A disclosure log is primary for what it publicly exposes on that surface.
-- Failure to find a matching released item is NOT proof that internal advice
-- does not exist, was not created, or was not relied upon.
------------------------------------------------------------------------

data AcquisitionSurfaceKind : Set where
  foiDisclosureLog : AcquisitionSurfaceKind
  ministerialRelease : AcquisitionSurfaceKind
  parliamentaryDocument : AcquisitionSurfaceKind
  agencyGuidance : AcquisitionSurfaceKind
  cabinetRelease : AcquisitionSurfaceKind

data AcquisitionObservation : Set where
  matchingItemObserved : AcquisitionObservation
  noMatchingItemObservedOnInspectedSurface : AcquisitionObservation
  inaccessibleOrUninspected : AcquisitionObservation

record AdviceAcquisitionReceipt : Set where
  constructor adviceAcquisitionReceipt
  field
    receiptId : String
    source : Source.AttributedSource
    surfaceKind : AcquisitionSurfaceKind
    deweyParent : String
    qidReference : String
    stableIdentifier : String
    canonicalLink : String
    inspectedTermsReference : String
    observation : AcquisitionObservation
    boundedFinding : String
    nonFindingDoesNotProveNonexistence : Bool

open AdviceAcquisitionReceipt public

dfatFoiLogSource : Source.AttributedSource
dfatFoiLogSource = Source.mkNoDOISource
  "Department of Foreign Affairs and Trade"
  "FOI disclosure log"
  "DFAT"
  "2026"
  "https://www.dfat.gov.au/about-us/corporate/freedom-of-information/foi-disclosure-log"
  Source.governmentSource
  "primary public index of documents released by DFAT under the Freedom of Information Act; acquisition surface only"
  Source.publicAttribution

dfatCurrentLogInspection : AdviceAcquisitionReceipt
dfatCurrentLogInspection = adviceAcquisitionReceipt
  "ABC730-advice:dfat-foi-log-current-inspection"
  dfatFoiLogSource
  foiDisclosureLog
  "353"
  "qid-unresolved-for-DFAT"
  "dfat:foi-disclosure-log:inspected-2026-09-11"
  "https://www.dfat.gov.au/about-us/corporate/freedom-of-information/foi-disclosure-log"
  "search terms inspected: settlement; import ban; Palestinians"
  noMatchingItemObservedOnInspectedSurface
  "No matching released settlement-import-ban impact or implementation analysis was observed on the inspected current DFAT disclosure-log surface using the recorded terms."
  true

------------------------------------------------------------------------
-- Exact advice object we need if/when a release is found.
------------------------------------------------------------------------

data AdviceField : Set where
  settlementOriginLegalTest : AdviceField
  productionLocationEvidenceStandard : AdviceField
  importerDeclarationChange : AdviceField
  customsSystemChange : AdviceField
  importerComplianceCost : AdviceField
  governmentAdministrationCost : AdviceField
  falsePositiveOrMisclassificationEstimate : AdviceField
  evasionOrRelabellingEstimate : AdviceField
  AustralianBusinessExposure : AdviceField
  PalestinianIncidenceMechanism : AdviceField
  IsraeliIncidenceMechanism : AdviceField
  targetedVsBlanketComparison : AdviceField
  consultationEvidence : AdviceField
  recommendationWeight : AdviceField

record AdviceTarget : Set where
  constructor adviceTarget
  field
    targetId : String
    institution : String
    candidateObject : String
    requiredFields : List AdviceField
    acquisitionPath : String
    paid : Bool

open AdviceTarget public

dfatImpactAdviceTarget : AdviceTarget
dfatImpactAdviceTarget = adviceTarget
  "ABC730-advice-target:dfat-impact-analysis"
  "DFAT"
  "final brief/submission/analysis supporting C029 implementation and unintended-consequence rationale"
  (settlementOriginLegalTest ∷ productionLocationEvidenceStandard ∷
   importerComplianceCost ∷ AustralianBusinessExposure ∷
   PalestinianIncidenceMechanism ∷ IsraeliIncidenceMechanism ∷
   targetedVsBlanketComparison ∷ consultationEvidence ∷ recommendationWeight ∷ [])
  "DFAT public releases/disclosure log first; FOI or parliamentary production if not already public"
  false

abfImplementationAdviceTarget : AdviceTarget
abfImplementationAdviceTarget = adviceTarget
  "ABC730-advice-target:abf-implementation"
  "Australian Border Force / Department of Home Affairs"
  "implementation advice on identifying and enforcing settlement-place origin at import"
  (settlementOriginLegalTest ∷ productionLocationEvidenceStandard ∷
   importerDeclarationChange ∷ customsSystemChange ∷ importerComplianceCost ∷
   governmentAdministrationCost ∷ falsePositiveOrMisclassificationEstimate ∷
   evasionOrRelabellingEstimate ∷ [])
  "ABF/Home Affairs guidance/disclosure surfaces; then FOI if necessary"
  false

treasuryBusinessImpactTarget : AdviceTarget
treasuryBusinessImpactTarget = adviceTarget
  "ABC730-advice-target:treasury-business-impact"
  "Australian Treasury"
  "business impact or regulatory-cost analysis for a settlement-goods import restriction"
  (importerComplianceCost ∷ governmentAdministrationCost ∷
   AustralianBusinessExposure ∷ targetedVsBlanketComparison ∷ [])
  "Treasury ministerial/publication/disclosure surfaces; then FOI if necessary"
  false

allAdviceTargets : List AdviceTarget
allAdviceTargets = dfatImpactAdviceTarget ∷ abfImplementationAdviceTarget ∷ treasuryBusinessImpactTarget ∷ []

------------------------------------------------------------------------
-- Snowball semantics.
------------------------------------------------------------------------

data NoPublicMatchMeansNoAdvice : Set where
noPublicMatchDoesNotMeanNoAdvice : NoPublicMatchMeansNoAdvice → ⊥
noPublicMatchDoesNotMeanNoAdvice ()

data MinisterialStatementSubstitutesForAdvice : Set where
ministerialStatementDoesNotSubstituteForAdvice : MinisterialStatementSubstitutesForAdvice → ⊥
ministerialStatementDoesNotSubstituteForAdvice ()

data ExistingOriginSystemPaysSettlementDesign : Set where
existingOriginSystemDoesNotPaySettlementDesign : ExistingOriginSystemPaysSettlementDesign → ⊥
existingOriginSystemDoesNotPaySettlementDesign ()

data FOIReleaseAutomaticallyPaysPolicyTruth : Set where
foiReleaseDoesNotAutomaticallyPayPolicyTruth : FOIReleaseAutomaticallyPaysPolicyTruth → ⊥
foiReleaseDoesNotAutomaticallyPayPolicyTruth ()

implementationFrontierAnchor : Australia.AustralianImplementationFrontier
implementationFrontierAnchor = Australia.canonicalAustralianImplementationFrontier

originCapabilityAnchor : Origin.AustralianOriginCapabilityState
originCapabilityAnchor = Origin.canonicalAustralianOriginCapabilityState

atlasBoundaryAnchor : Atlas.AtlasBoundary
atlasBoundaryAnchor = Atlas.canonicalAtlasBoundary
