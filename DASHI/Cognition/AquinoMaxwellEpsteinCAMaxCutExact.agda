module DASHI.Cognition.AquinoMaxwellEpsteinCAMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as CA
import DASHI.Cognition.EpsteinMasterPlanAttributionBoundaryExact as Plan
import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Law.EvidenceProvenanceDependencyDagExact as Provenance
import DASHI.Core.ProvenanceClosureIndependenceExact as RootClosure
import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition
import DASHI.Core.ITIRInvestigationAcquisitionParetoExact as ITIR
import DASHI.Core.ITIRInvestigationWorkbenchProjectionExact as Workbench
import DASHI.Core.MultipartSameObjectReconstructionExact as Multipart

------------------------------------------------------------------------
-- AQUINO / MAXWELL / EPSTEIN / CA: EXISTING-CARRIER ATTRIBUTION MAX-CUT
--
-- Historical claims are about what a bounded source establishes. A court
-- decision, sworn testimony, a self-authored proposal, an agency statement
-- and an investigative allegation are different evidentiary acts. They do
-- not vote as independent witnesses just because documents repeat them.
--
-- This is a typed provenance/claim-promotion boundary, NOT a proof of
-- events in the external world or of the absence of unknown records.
-- The case reuses the existing CA and MasterPlan owners.
------------------------------------------------------------------------

data Person : Set where
  robertMaxwell : Person
  robertMercer : Person
  ghislaineMaxwell : Person
  jeffreyEpstein : Person
  michaelAquino : Person
  paulVallely : Person
  steveBannon : Person

robertMaxwellIsNotRobertMercer : robertMaxwell ≡ robertMercer → ⊥
robertMaxwellIsNotRobertMercer ()

data ResearchProgramme : Set where
  mindWarProposal : ResearchProgramme
  projectStargate : ResearchProgramme

mindWarIsNotStargate : mindWarProposal ≡ projectStargate → ⊥
mindWarIsNotStargate ()

data SourceRole : Set where
  contemporaryCorporateRecord : SourceRole
  attributedFirstPersonTestimony : SourceRole
  attributedAuthorProposal : SourceRole
  retrospectiveSelfAccount : SourceRole
  regulatoryFinding : SourceRole
  judicialProceduralDecision : SourceRole
  congressionalFinding : SourceRole
  disputedAgencyReview : SourceRole
  releasedCorrespondence : SourceRole
  crossSourceHypothesis : SourceRole

-- Source roots represent original authors or record-producing bodies.
-- Reposting a witness statement does not create another witness.
data OriginRoot : Set where
  wylieRoot : OriginRoot
  aquinoVallelyRoot : OriginRoot
  fourthCircuitRoot : OriginRoot
  ftcRoot : OriginRoot
  houseJudiciaryRoot : OriginRoot
  buaDOJRoot : OriginRoot
  dojFBIMemoRoot : OriginRoot
  epsteinCorrespondenceRoot : OriginRoot

data CaseClaim : Set where
  sclCAOperatingContinuity : CaseClaim
  mindWarAuthored : CaseClaim
  presidioAdministrativeDisposition : CaseClaim
  deceptiveFacebookCollection : CaseClaim
  inslawCongressionalFinding : CaseClaim
  inslawSpecialCounselCounterFinding : CaseClaim
  dojFBI2025ReviewPosition : CaseClaim
  bannonEpsteinMediaContact : CaseClaim

record BoundedSource : Set where
  constructor bounded-source
  field
    proposition : CaseClaim
    root : OriginRoot
    role : SourceRole
    locator : String
    sourceDate : String
    describedEventPeriod : String
    boundedFinding : String
    sourceStatementLocated : Bool
    specificOperationalTransferPaid : Bool
    unifiedIntelligenceCommandPaid : Bool
    criminalConductOfNamedUnchargedPersonsPaid : Bool
open BoundedSource public

canonicalSources : List BoundedSource
canonicalSources =
  bounded-source sclCAOperatingContinuity wylieRoot
    attributedFirstPersonTestimony
    "https://committees.parliament.uk/writtenevidence/89475/html/"
    "2018" "2013-2014"
    "Christopher Wylie testified to SCL/CA corporate and technique continuity and Mercer's/Bannon's roles. This is attributed testimony, not proof that Aquino's particular 1980 paper was adopted."
    true false false false
  ∷ bounded-source mindWarAuthored aquinoVallelyRoot
    attributedAuthorProposal
    "From PSYOP to MindWar, Paul E. Vallely / Michael A. Aquino, 1980; 2003 Aquino annotations"
    "1980 (2003 author retrospective is SAME origin)" "1980"
    "The named authors produced a discussion proposal. Aquino's later account is not an independent witness or a source of an executed command."
    true false false false
  ∷ bounded-source presidioAdministrativeDisposition fourthCircuitRoot
    judicialProceduralDecision
    "https://law.justia.com/cases/federal/appellate-courts/F2/957/139/2044/"
    "1992-02-26" "1986-1990"
    "Aquino v Stone affirmed refusal to alter CID records; the appellate holding is administrative, not a finding of criminal guilt. San Francisco police had ended their investigation for insufficient evidence."
    true false false false
  ∷ bounded-source deceptiveFacebookCollection ftcRoot
    regulatoryFinding
    "https://www.ftc.gov/legal-library/browse/cases-proceedings/182-3107-cambridge-analytica-llc-matter"
    "2019-12" "2014 onward"
    "FTC found Cambridge Analytica used deceptive collection of Facebook personal data; this does not establish election causation or a specific Aquino-to-SCL transfer."
    true false false false
  ∷ bounded-source inslawCongressionalFinding houseJudiciaryRoot
    congressionalFinding
    "House Judiciary Committee, The INSLAW Affair, H. Rept. 102-857 (1992)"
    "1992" "1980s-1992"
    "House investigators criticised DOJ conduct in the PROMIS dispute. Alleged Robert Maxwell intelligence distribution is a separate claim, not paid by this congressional finding."
    true false false false
  ∷ bounded-source inslawSpecialCounselCounterFinding buaDOJRoot
    disputedAgencyReview
    "Nicholas Bua, Report of Special Counsel Regarding INSLAW, 1993"
    "1993" "1980s-1993"
    "A separate DOJ-commissioned investigation contested significant INSLAW allegations. Distinct institutional author root; neither its findings nor House findings alone establish the Maxwell backdoor claim."
    true false false false
  ∷ bounded-source dojFBI2025ReviewPosition dojFBIMemoRoot
    disputedAgencyReview
    "https://www.justice.gov/opa/media/1407001/dl"
    "2025-07" "Epstein investigative holdings through 2025"
    "DOJ/FBI said its review found no credible evidence Epstein blackmailed prominent individuals. This is an attributed agency conclusion, not a proof that blackmail was logically impossible."
    true false false false
  ∷ bounded-source bannonEpsteinMediaContact epsteinCorrespondenceRoot
    releasedCorrespondence
    "DOJ-released Bannon/Epstein communications; canonical prior owner TrumpMarALagoBannonBridgeExact"
    "released 2025-2026" "2018-2019"
    "Direct correspondence documents media/political collaboration; neither personnel overlap with Cambridge Analytica nor a shared influence vocabulary pays transfer of its software or techniques."
    true false false false
  ∷ []

-- Case-specific negative closure is a current-source-state statement.
-- It does not assert that no additional witness or document can ever exist.
record CrossNetworkBoundary : Set where
  constructor cross-network-boundary
  field
    sclToCACorporateContinuityPaid : Bool
    caDeceptiveCollectionFindingPaid : Bool
    bannonEpsteinCorrespondencePaid : Bool
    aquinoAuthoredMindWarPaid : Bool
    aquinoDirectEpsteinWorkPaid : Bool
    aquinoDirectMaxwellWorkPaid : Bool
    aquinoSpecificTechniqueTransferredToSCLPaid : Bool
    aquinoProjectStargateOperationalIdentityPaid : Bool
    promisBackdoorMaxwellDistributionPaid : Bool
    epsteinIntelligenceBlackmailTaskingPaid : Bool
    unifiedSponsorAndHierarchyPaid : Bool
open CrossNetworkBoundary public

canonicalBoundary : CrossNetworkBoundary
canonicalBoundary = cross-network-boundary
  true true true true false false false false false false false

aquinoToSCLUnpaid :
  aquinoSpecificTechniqueTransferredToSCLPaid canonicalBoundary ≡ false
aquinoToSCLUnpaid = refl

aquinoToEpsteinUnpaid : aquinoDirectEpsteinWorkPaid canonicalBoundary ≡ false
aquinoToEpsteinUnpaid = refl

promisMaxwellUnpaid : promisBackdoorMaxwellDistributionPaid canonicalBoundary ≡ false
promisMaxwellUnpaid = refl

unifiedHierarchyUnpaid : unifiedSponsorAndHierarchyPaid canonicalBoundary ≡ false
unifiedHierarchyUnpaid = refl

existingCAMediaReuseUnpaid :
  CA.laterEpsteinMediaWorkProvesTechniqueReuse
    CA.canonicalBannonInfluenceInfrastructureBoundary ≡ false
existingCAMediaReuseUnpaid = refl

existingMasterPlanHierarchyUnpaid :
  Plan.unifiedCommandHierarchyPaid Plan.canonicalMasterPlanCoordinates ≡ false
existingMasterPlanHierarchyUnpaid = refl

existingGenealogyDoesNotPromoteAnalogy :
  Genealogy.historicalContinuityEqualsCentralCommand
    Genealogy.canonicalEvidenceGradedGenealogyBoundary ≡ false
existingGenealogyDoesNotPromoteAnalogy = refl

-- These token types are deliberately uninhabited. Their rejection is a
-- type-level API constraint, not an empirical proof of nonparticipation.
data SourceRepetitionImpliesIndependentCorroboration : Set where
data CommonMethodImpliesDirectTransfer : Set where
data AllegationImpliesAdjudicatedConduct : Set where
data NetworkPathImpliesUnifiedCommand : Set where

noWitnessMultiplication :
  SourceRepetitionImpliesIndependentCorroboration → ⊥
noWitnessMultiplication ()

noTechniquePromotion : CommonMethodImpliesDirectTransfer → ⊥
noTechniquePromotion ()

noGuiltByAllegation : AllegationImpliesAdjudicatedConduct → ⊥
noGuiltByAllegation ()

noUnifiedCommandFromNetworkPath : NetworkPathImpliesUnifiedCommand → ⊥
noUnifiedCommandFromNetworkPath ()


------------------------------------------------------------------------
-- WOOGAROO / INVESTIGATION CROSS-POLLINATION (CASE CONSUMER, NO NEW CORE)
--
-- Woogaroo's evidence-dependency matrix is source calibration: several
-- documents sourced from one ecological observation do not give independent
-- project evidence; statutory instruments and site identity have different
-- roles. The generic owners below already implement this discipline. Here
-- we consume them for this case rather than importing Woogaroo's legal
-- facts as evidence of an unrelated historical network.
------------------------------------------------------------------------

dependencyProvenanceAuthority : Provenance.ProvenanceDagBoundary
dependencyProvenanceAuthority = Provenance.canonicalProvenanceDagBoundary

independentRootsAuthority : RootClosure.ProvenanceClosureBoundary
independentRootsAuthority = RootClosure.canonicalProvenanceClosureBoundary

acquisitionStagesAuthority : Acquisition.SourceAcquisitionBoundary
acquisitionStagesAuthority = Acquisition.canonicalSourceAcquisitionBoundary

investigationParetoAuthority : ITIR.InvestigationAcquisitionBoundary
investigationParetoAuthority = ITIR.canonicalInvestigationAcquisitionBoundary

investigationUIAuthority : Workbench.InvestigationWorkbenchBoundary
investigationUIAuthority = Workbench.canonicalInvestigationWorkbenchBoundary

multipartIdentityAuthority : Multipart.MultipartReconstructionBoundary
multipartIdentityAuthority = Multipart.canonicalMultipartReconstructionBoundary

-- Constructive toy countermodel: two direct reprints of one author statement
-- have one shared declared producer. This is NOT a claim that any particular
-- two journalists copied Wylie; those historical edges require their own
-- source documents. It demonstrates why citation-count != independent roots.
data ReprintCarrier : Set where
  firstPersonStatement : ReprintCarrier
  excerptA : ReprintCarrier
  excerptB : ReprintCarrier

data ReprintDependency : ReprintCarrier → ReprintCarrier → Set where
  statementToExcerptA : ReprintDependency firstPersonStatement excerptA
  statementToExcerptB : ReprintDependency firstPersonStatement excerptB

data ReprintRoot : ReprintCarrier → Set where
  firstPersonRoot : ReprintRoot firstPersonStatement

reprintSystem : RootClosure.ProvenanceSystem ReprintCarrier
reprintSystem = RootClosure.provenanceSystem ReprintDependency ReprintRoot

twoExcerptsShareOneRoot :
  RootClosure.SharedUpstreamRoot reprintSystem excerptA excerptB
twoExcerptsShareOneRoot = RootClosure.sharedUpstreamRoot
  firstPersonStatement firstPersonRoot
  (Affected.affectedStep statementToExcerptA Affected.affectedRefl)
  (Affected.affectedStep statementToExcerptB Affected.affectedRefl)

sharedReprintRootRefutesIndependence :
  RootClosure.IndependentByUpstreamClosure reprintSystem excerptA excerptB → ⊥
sharedReprintRootRefutesIndependence =
  RootClosure.sharedUpstreamRootRefutesIndependence twoExcerptsShareOneRoot

-- BIDI: requests for independent corroboration must return to the original
-- producer; multiple indexed PDFs of one witness/claim do not suffice.
caseIndependentProducerRequirement :
  Provenance.reverseProvenance Provenance.independentCorroborationConsumer
    ≡ Provenance.independentProducerReceipt
caseIndependentProducerRequirement = refl

-- These are explicit stage states for *this* pass. A recoverable URL is not
-- evidence of full-text extraction or of a specific historical allegation.
-- Unlocated carriers are proposed targets, not documents asserted to exist.
sclCorporateWorkProductTarget : Acquisition.SourceAcquisitionTarget
sclCorporateWorkProductTarget = Acquisition.sourceAcquisitionTarget
  "Original signed SCL/Cambridge Analytica agreements, 2013-2015"
  "Exact executed signatures / governing schedules not acquired in this pass"
  Acquisition.directDigitalArchive Acquisition.physicalHolding
  false false false

bannonEpsteinFilmWorkProductTarget : Acquisition.SourceAcquisitionTarget
bannonEpsteinFilmWorkProductTarget = Acquisition.sourceAcquisitionTarget
  "Epstein-Bannon raw 2018-2019 production correspondence and edit/contract chain"
  "Match Bates IDs and complete film work products to date, authors, custody"
  Acquisition.directDigitalArchive Acquisition.nationalCatalogue
  false false false

promisMaxwellExecutableTarget : Acquisition.SourceAcquisitionTarget
promisMaxwellExecutableTarget = Acquisition.sourceAcquisitionTarget
  "Alleged Maxwell-linked PROMIS installation, version, contract and backdoor"
  "No authenticated executable or matched procurement record inspected in this pass"
  Acquisition.nationalCatalogue Acquisition.physicalHolding
  false false false

aquinoSCLTransferTarget : Acquisition.SourceAcquisitionTarget
aquinoSCLTransferTarget = Acquisition.sourceAcquisitionTarget
  "Hypothetical 1980 MindWar-to-SCL personnel/manual/technical transfer"
  "Unlocated exact handoff; not established by shared terminology"
  Acquisition.directDigitalArchive Acquisition.nationalCatalogue
  false false false

-- A question-indexed matrix, as in Woogaroo, avoids inventing source counts:
-- one verified legal fact, one factual contact and a named general method do
-- not sum to three independent observations of covert coordination.
data CaseConsumer : Set where
  historicalDocumentExists : CaseConsumer
  cambridgeAnalyticaLegalEntityIdentity : CaseConsumer
  sclCATechniqueDeployment : CaseConsumer
  epsteinBannonActualWorkProduct : CaseConsumer
  maxwellPROMISBackdoor : CaseConsumer
  aquinoSCLTransfer : CaseConsumer
  coordinatedIntelligenceCommand : CaseConsumer

record CaseDependencyCut : Set where
  constructor case-dependency-cut
  field
    consumer : CaseConsumer
    sourceOrRoute : String
    needsIndependentProducer : Bool
    needsExactArtifactOrSubjectJoin : Bool
    needsEventTimeContinuity : Bool
    sourceEvidenceSufficient : Bool
    consumerConclusionPaid : Bool
    firstUnpaidConsumerObligation : String
open CaseDependencyCut public

cambridgeLegalEntityCut : CaseDependencyCut
cambridgeLegalEntityCut = case-dependency-cut
  cambridgeAnalyticaLegalEntityIdentity
  "Indexed 2014 parliamentary counsel memorandum and FEC corporate chronology"
  true true true false false
  "Resolve Delaware entity number, the exact LLC/LLP/UK subsidiary, formation versus incorporation date and cited filing. Similar CA names or indexed PDF excerpts do not pay same legal object."

sclTransferCut : CaseDependencyCut
sclTransferCut = case-dependency-cut
  sclCATechniqueDeployment
  "Original SCL/CA contract, personnel and dated system deployment"
  true true true false false
  "Join source-specific method to an actual executed personnel/technical transfer; Wylie testimony and FTC finding alone cannot identify Aquino as the source."

bannonWorkProductCut : CaseDependencyCut
bannonWorkProductCut = case-dependency-cut
  epsteinBannonActualWorkProduct
  "DOJ indexed communications -> produced film/edit/contract/payment objects"
  true true true false false
  "Recover specific deliverable, responsible editor, custody and date, then compare with any CA technical artefact; correspondence alone cannot establish method reuse."

promisExecutableCut : CaseDependencyCut
promisExecutableCut = case-dependency-cut
  maxwellPROMISBackdoor
  "House/Bua claims -> named version, installation, procurement and executable"
  true true true false false
  "Obtain same-build software + contract/installation identity and a demonstrated backdoor; disputed reports are evidence of disagreement, not an executable."

aquinoHistoricalTransferCut : CaseDependencyCut
aquinoHistoricalTransferCut = case-dependency-cut
  aquinoSCLTransfer
  "MindWar 1980 discussion proposal -> SCL operational artefact"
  true true true false false
  "Require dated operational citation, handoff, deployment or code with attributable lineage; no generic shared-psyops promotion."

commandHierarchyCut : CaseDependencyCut
commandHierarchyCut = case-dependency-cut
  coordinatedIntelligenceCommand
  "Claim-specific sponsor, tasking, instruction, deliverable and payment chain"
  true true true false false
  "Trace one actual common source of control across cases; network paths and repeated buzzwords do not fill the gap."

canonicalCaseCuts : List CaseDependencyCut
canonicalCaseCuts =
  cambridgeLegalEntityCut ∷ sclTransferCut ∷ bannonWorkProductCut ∷ promisExecutableCut
  ∷ aquinoHistoricalTransferCut ∷ commandHierarchyCut ∷ []

-- The only instantiated Pareto routes are proposals about where to search;
-- numeric axes are scenario/routing calibration, NEVER truth/guilt scores.
-- Keep the mixed five-dimensional ITIR order, not a scalar leaderboard.
sclCAOriginalContractRoute : ITIR.InvestigationCandidate
sclCAOriginalContractRoute = ITIR.investigation-candidate
  "case:SCL-CA-executed-contract" "obligation:direct-transfer"
  "route:company-registries-parliamentary-production" "access:lawful-public"
  "genealogy:corporate-original-not-Wylie-reprint" "axes:illustrative-calibration"
  5 5 4 5 3
  true refl false refl false refl

bannonActualFilmRoute : ITIR.InvestigationCandidate
bannonActualFilmRoute = ITIR.investigation-candidate
  "case:Bannon-Epstein-work-product" "obligation:same-work-product"
  "route:DOJ-Bates-raw-attachments" "access:lawful-public-redacted"
  "genealogy:direct-correspondence-distinct-from-media-recaps" "axes:illustrative-calibration"
  5 4 5 4 3
  true refl false refl false refl

candidateRoutes : List ITIR.InvestigationCandidate
candidateRoutes = sclCAOriginalContractRoute ∷ bannonActualFilmRoute ∷ []

caseFiveAxisAuthority : ITIR.DirectMixedParetoView
caseFiveAxisAuthority = ITIR.investigationParetoView

caseMissingSourceIsNotAbsence :
  ITIR.notLocatedMeansKnownAbsent ITIR.canonicalInvestigationAcquisitionBoundary
    ≡ false
caseMissingSourceIsNotAbsence = refl

caseUIIsNotEvidence :
  Workbench.uiMayConstructAcquisitionResult
    Workbench.canonicalInvestigationWorkbenchBoundary ≡ false
caseUIIsNotEvidence = refl

caseReprintsNotIndependent :
  Provenance.multipleReceiptsAutomaticallyIndependent
    Provenance.canonicalProvenanceDagBoundary ≡ false
caseReprintsNotIndependent = refl

caseIdentityNeedsFullReconstruction :
  Multipart.localPartIdentityAloneCreatesWholeIdentity
    Multipart.canonicalMultipartReconstructionBoundary ≡ false
caseIdentityNeedsFullReconstruction = refl

-- No construction of an external historical fact from route visibility,
-- discovery, a candidate score, analogous legal structures, or missing text.
data DiscoveredRouteImpliesInspectedPrimary : Set where
data OfficialProceduralFindingImpliesUnderlyingScientificFinding : Set where
data EventTimeOverlapImpliesOperationalControl : Set where
data TechnicalAnalogyImpliesSameProgramme : Set where

discoveryDoesNotPayInspection : DiscoveredRouteImpliesInspectedPrimary → ⊥
discoveryDoesNotPayInspection ()

proceduralFindingDoesNotPaySubstantiveFact :
  OfficialProceduralFindingImpliesUnderlyingScientificFinding → ⊥
proceduralFindingDoesNotPaySubstantiveFact ()

eventTimeOverlapDoesNotPayCommand : EventTimeOverlapImpliesOperationalControl → ⊥
eventTimeOverlapDoesNotPayCommand ()

analogyDoesNotPayProgramme : TechnicalAnalogyImpliesSameProgramme → ⊥
analogyDoesNotPayProgramme ()
