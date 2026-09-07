module DASHI.Cognition.PNF.SensibLawPluralObserverCorrectionApplicationAtlasExact where

------------------------------------------------------------------------
-- PLURAL-OBSERVER / CORRECTION APPLICATION ATLAS
--
-- Separates already-instantiated in-repo theorem surfaces from prospective
-- application templates. A template says where the topology can be applied; it
-- does NOT assert that a named real-world system empirically exhibits the
-- failure until domain-specific evidence is supplied.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.PluralObserverCorrectionRealisationExact as Plural
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ApplicationCapabilityDominantChartCompressionExact as Capability
import DASHI.Law.SecurityRoutingDominantChartCompressionExact as Security
import DASHI.Law.SecurityRoutingComparatorHypervoxelExact as SecurityRouting
import DASHI.Cognition.PNF.SensibLawDeclaredReasonRealizedEffectOperationalExact as LegalOperation
import DASHI.Cognition.PNF.SensibLawBillyRemedyActuationTwoEyedPOSIWIDExact as Billy

------------------------------------------------------------------------
-- Exact bridge from the existing synthetic Billy terminal fixtures into the
-- generic plural-observer topology.
------------------------------------------------------------------------

data BillySyntheticState : Set where
  billyDeclarationWithoutOutcome : BillySyntheticState
  billyBraidedRealisation : BillySyntheticState


data BillyDeclared : Set where billyDeclaredRepair : BillyDeclared
data BillyInstitutional : Set where billyInstitutionReportsActivity : BillyInstitutional
data BillyAffected : Set where billyAffectedOpen billyAffectedSatisfied : BillyAffected
data BillyIndependent : Set where billyIndependentFails billyIndependentWorks : BillyIndependent
data BillyCorrection : Set where billyCorrectionFails billyCorrectionWorks : BillyCorrection
data BillyOutcome : Set where billyRepairOpen billyRepairRealised : BillyOutcome

billyDeclared : BillySyntheticState → BillyDeclared
billyDeclared _ = billyDeclaredRepair

billyInstitutional : BillySyntheticState → BillyInstitutional
billyInstitutional _ = billyInstitutionReportsActivity

billyAffected : BillySyntheticState → BillyAffected
billyAffected billyDeclarationWithoutOutcome = billyAffectedOpen
billyAffected billyBraidedRealisation = billyAffectedSatisfied

billyIndependent : BillySyntheticState → BillyIndependent
billyIndependent billyDeclarationWithoutOutcome = billyIndependentFails
billyIndependent billyBraidedRealisation = billyIndependentWorks

billyCorrection : BillySyntheticState → BillyCorrection
billyCorrection billyDeclarationWithoutOutcome = billyCorrectionFails
billyCorrection billyBraidedRealisation = billyCorrectionWorks

billyOutcome : BillySyntheticState → BillyOutcome
billyOutcome billyDeclarationWithoutOutcome = billyRepairOpen
billyOutcome billyBraidedRealisation = billyRepairRealised

billyPluralSystem :
  Plural.PluralOperationalSystem
    BillySyntheticState BillyDeclared BillyInstitutional BillyAffected
    BillyIndependent BillyCorrection BillyOutcome
billyPluralSystem = Plural.plural-operational-system
  billyDeclared
  billyInstitutional
  billyAffected
  billyIndependent
  billyCorrection
  billyOutcome

billyInstitutionalAffectedCollision : Plural.InstitutionalAffectedCollision billyPluralSystem
billyInstitutionalAffectedCollision = Plural.institutional-affected-collision
  billyDeclarationWithoutOutcome
  billyBraidedRealisation
  refl
  (λ ())

billyInstitutionalActivityCannotRecoverAffectedOutcome :
  INF.FactorsThrough billyInstitutional billyAffected → ⊥
billyInstitutionalActivityCannotRecoverAffectedOutcome =
  Plural.institutionalObservationCannotRecoverAffectedObservation
    billyInstitutionalAffectedCollision

billyExistingTerminalFixtureStillDistinguishesRepair :
  Billy.classifyRealisedRepair Billy.syntheticDeclarationWithoutOutcome
  ≡ false
billyExistingTerminalFixtureStillDistinguishesRepair = refl

billyExistingBraidedFixtureStillClosesRepair :
  Billy.classifyRealisedRepair Billy.syntheticBraidedRealisation
  ≡ true
billyExistingBraidedFixtureStillClosesRepair = refl

------------------------------------------------------------------------
-- Application domains.
------------------------------------------------------------------------

data ApplicationDomain : Set where
  countryAndTreatyRemedy : ApplicationDomain
  legalRemedyAndCourtGate : ApplicationDomain
  securityRouting : ApplicationDomain
  scientificOperationalCapability : ApplicationDomain
  policeComplaintOversight : ApplicationDomain
  disabilityAccessibilityCompliance : ApplicationDomain
  healthcareQualityAndSafety : ApplicationDomain
  workplaceGrievance : ApplicationDomain
  environmentalLicensing : ApplicationDomain
  algorithmicGovernance : ApplicationDomain
  corporateESGReporting : ApplicationDomain
  educationInclusion : ApplicationDomain


data ApplicationStatus : Set where
  exactInRepoInstance : ApplicationStatus
  prospectiveTemplateOnly : ApplicationStatus


record ApplicationAuditPattern : Set where
  constructor application-audit-pattern
  field
    domain : ApplicationDomain
    status : ApplicationStatus
    institutionalSurface : String
    affectedOrFineTarget : String
    independentOrComparatorSurface : String
    correctionSurface : String
    terminalOutcome : String
    theoremOrTemplateReference : String
    empiricalFailureClaimedByThisAtlas : Bool
    empiricalFailureClaimedByThisAtlasIsFalse :
      empiricalFailureClaimedByThisAtlas ≡ false

open ApplicationAuditPattern public

countryRemedyPattern : ApplicationAuditPattern
countryRemedyPattern = application-audit-pattern
  countryAndTreatyRemedy
  exactInRepoInstance
  "state implementation report / funding / consultation / declared remedy"
  "community-defined Country, safety, reparation and authority outcome"
  "independent monitoring + treaty-body assessment"
  "actual revision after deficiencies are identified"
  "realised repair under the declared consumer"
  "SensibLawBillyRemedyActuationTwoEyedPOSIWIDExact + PluralObserverCorrectionRealisationExact"
  false refl

legalRemedyPattern : ApplicationAuditPattern
legalRemedyPattern = application-audit-pattern
  legalRemedyAndCourtGate
  exactInRepoInstance
  "declared neutral legal rationale / available remedial surface"
  "realised loss distribution and realised remedy"
  "review/appellate/evidential comparator"
  "reopening or correction after evidence"
  "consumer-specific realised legal remedy"
  "SensibLawDeclaredReasonRealizedEffectOperationalExact"
  false refl

securityRoutingPattern : ApplicationAuditPattern
securityRoutingPattern = application-audit-pattern
  securityRouting
  exactInRepoInstance
  "coarse security intensity / declared protective purpose"
  "protective-versus-coercive realised routing"
  "security-need comparator"
  "independent correction rather than dissent-as-fault closure"
  "proportionate protective routing under source-backed need"
  "DASHI.Law.SecurityRoutingDominantChartCompressionExact"
  false refl

scientificCapabilityPattern : ApplicationAuditPattern
scientificCapabilityPattern = application-audit-pattern
  scientificOperationalCapability
  exactInRepoInstance
  "public governing-science / published architecture"
  "validated calibrated operational capability"
  "application-specific validation"
  "new capability-bearing information rather than relabelling public theory"
  "reconstructed and validated operational capability"
  "DASHI.Core.ApplicationCapabilityDominantChartCompressionExact"
  false refl

policeOversightTemplate : ApplicationAuditPattern
policeOversightTemplate = application-audit-pattern
  policeComplaintOversight
  prospectiveTemplateOnly
  "agency policy, complaint closure code, internal compliance report"
  "complainant/community safety, accountability and recurrence outcome"
  "independent investigation / external review"
  "discipline, policy revision, disclosure or operational change"
  "recurrence reduction and affected-party safety/accountability"
  "template only: requires jurisdiction- and source-specific evidence"
  false refl

accessibilityTemplate : ApplicationAuditPattern
accessibilityTemplate = application-audit-pattern
  disabilityAccessibilityCompliance
  prospectiveTemplateOnly
  "formal accessibility standard / checklist compliance"
  "realised usable access for differently situated users"
  "independent accessibility testing + affected-user reports"
  "actual remediation of barriers"
  "realised access rather than nominal compliance"
  "template only: instantiate with source-specific accessibility receipts"
  false refl

healthcareTemplate : ApplicationAuditPattern
healthcareTemplate = application-audit-pattern
  healthcareQualityAndSafety
  prospectiveTemplateOnly
  "protocol compliance / accreditation / process completion"
  "patient-defined and clinical outcome"
  "independent safety/quality review"
  "corrective clinical/system revision"
  "improved safety/outcome without recurrence"
  "template only: high-stakes medical use requires domain evidence and governance"
  false refl

workplaceTemplate : ApplicationAuditPattern
workplaceTemplate = application-audit-pattern
  workplaceGrievance
  prospectiveTemplateOnly
  "policy existence / grievance closed / training completed"
  "worker safety, retaliation absence and material condition"
  "independent investigation / worker representation"
  "workplace or power-structure change"
  "realised non-retaliatory safe work relation"
  "template only: requires employment-law and workplace evidence"
  false refl

environmentalTemplate : ApplicationAuditPattern
environmentalTemplate = application-audit-pattern
  environmentalLicensing
  prospectiveTemplateOnly
  "permit condition / consultation / monitoring report"
  "affected-community/Country/ecological outcome"
  "independent ecological and community observation"
  "licence modification, stop-work, restoration or enforcement"
  "realised ecological/Country protection"
  "template only: requires project, jurisdiction and community-authority receipts"
  false refl

algorithmicTemplate : ApplicationAuditPattern
algorithmicTemplate = application-audit-pattern
  algorithmicGovernance
  prospectiveTemplateOnly
  "model-card/fairness metric/compliance assertion"
  "situated distribution of errors, harms and options"
  "external audit + affected-user observation"
  "model/data/policy revision"
  "consumer-specific realised reduction of harm"
  "template only: requires model, population and deployment evidence"
  false refl

esgTemplate : ApplicationAuditPattern
esgTemplate = application-audit-pattern
  corporateESGReporting
  prospectiveTemplateOnly
  "sustainability disclosure / target / certification"
  "realised environmental, labour and community effect"
  "independent verification + affected-community/worker evidence"
  "capital allocation, operations, remediation and accountability change"
  "realised material effect rather than disclosure completion"
  "template only: requires issuer- and metric-specific evidence"
  false refl

educationTemplate : ApplicationAuditPattern
educationTemplate = application-audit-pattern
  educationInclusion
  prospectiveTemplateOnly
  "inclusion policy / enrolment / attendance / accommodation count"
  "student-defined safety, access, participation and learning outcome"
  "independent review + student/family/community observation"
  "pedagogy, environment, accommodation or governance revision"
  "realised inclusion and learning access"
  "template only: requires education-context evidence"
  false refl

------------------------------------------------------------------------
-- Existing exact in-repo theorem pins.
------------------------------------------------------------------------

publicScienceStillCannotCarryOperationalCapability :
  INF.FactorsThrough Capability.publicScienceObserver Capability.operationalCapability → ⊥
publicScienceStillCannotCarryOperationalCapability =
  Capability.publicScienceCannotCarryOperationalCapability

securityIntensityStillCannotCarryRouting :
  INF.FactorsThrough SecurityRouting.coarseSecurityObserver SecurityRouting.routingTarget → ⊥
securityIntensityStillCannotCarryRouting = Security.securityIntensityCannotCarryRouting

neutralLegalRationaleStillCannotCarryDistribution :
  INF.FactorsThrough LegalOperation.declaredLegalRationale LegalOperation.realizedDistribution → ⊥
neutralLegalRationaleStillCannotCarryDistribution =
  LegalOperation.declaredRationaleCannotRecoverDistribution

------------------------------------------------------------------------
-- Generic application boundary.
------------------------------------------------------------------------

record ApplicationAtlasBoundary : Set where
  constructor application-atlas-boundary
  field
    templateMeansEmpiricalFailureAlreadyProved : Bool
    templateMeansEmpiricalFailureAlreadyProvedIsFalse :
      templateMeansEmpiricalFailureAlreadyProved ≡ false
    sameTopologyMeansSameDomainSemantics : Bool
    sameTopologyMeansSameDomainSemanticsIsFalse : sameTopologyMeansSameDomainSemantics ≡ false
    affectedObservationAutomaticallyWinsEveryDispute : Bool
    affectedObservationAutomaticallyWinsEveryDisputeIsFalse :
      affectedObservationAutomaticallyWinsEveryDispute ≡ false
    institutionalSelfReportAutomaticallyClosesOutcome : Bool
    institutionalSelfReportAutomaticallyClosesOutcomeIsFalse :
      institutionalSelfReportAutomaticallyClosesOutcome ≡ false
    correctionMustBeTestedAgainstRealisedOutcome : Bool
    correctionMustBeTestedAgainstRealisedOutcomeIsTrue :
      correctionMustBeTestedAgainstRealisedOutcome ≡ true

open ApplicationAtlasBoundary public

canonicalApplicationAtlasBoundary : ApplicationAtlasBoundary
canonicalApplicationAtlasBoundary = application-atlas-boundary
  false refl
  false refl
  false refl
  false refl
  true refl
