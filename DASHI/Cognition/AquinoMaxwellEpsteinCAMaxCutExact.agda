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
import DASHI.Core.MultipartSameObjectReconstructionExact as Multipart
import DASHI.Culture.MissingDeceasedCommonObjectProgrammeDiscriminatorExact as Common
import DASHI.Culture.MissingDeceasedCommonProgrammePromotionParetoExact as ProgrammeFrontier
import DASHI.Culture.MissingDeceasedTwentyScientistRound48AntiEchoChamberMethodologyExact as AntiEcho
import DASHI.Culture.MissingDeceasedTwentyScientistRound50ProfessionalEvidenceRoomExact as EvidenceRoom
import DASHI.Culture.MissingDeceasedTwentyScientistRound43NarrativeEvidenceStrataExact as Narrative
import DASHI.Core.EventTimeCapabilityAlignmentBidiExact as EventTime
import DASHI.Core.CapabilityFragilityConfoundersBidiExact as Fragility
import DASHI.Culture.MissingDeceasedCustodyEventTimeMatrixExact as Custody
import DASHI.Cognition.TrumpMarALagoBannonBridgeExact as BannonBridge

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
  estateScheduleCarrier : SourceRole
  preliminaryElectionEnforcement : SourceRole
  electionMatterClosure : SourceRole

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
  epsteinEstateScheduleRoot : OriginRoot
  fecEnforcementRoot : OriginRoot

data CaseClaim : Set where
  sclCAOperatingContinuity : CaseClaim
  mindWarAuthored : CaseClaim
  presidioAdministrativeDisposition : CaseClaim
  deceptiveFacebookCollection : CaseClaim
  inslawCongressionalFinding : CaseClaim
  inslawSpecialCounselCounterFinding : CaseClaim
  dojFBI2025ReviewPosition : CaseClaim
  bannonEpsteinMediaContact : CaseClaim
  sclCALicensingOralEvidence : CaseClaim
  delaware2013FTCEntityFinding : CaseClaim
  caVersusCIAWitnessClarification : CaseClaim
  bannonScheduledBreakfast2019 : CaseClaim
  bannonOctober2018Messages : CaseClaim
  ftcServicesAndLicencesDescribed : CaseClaim
  fecDecember2013LLCStatement : CaseClaim
  fecForeignNationalReasonToBelieve : CaseClaim
  fecCaseClosedWithoutFinalLiability : CaseClaim
  wylieKompromatStatement2018 : CaseClaim
  wylieProjectRiponStatement2018 : CaseClaim

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
  ∷ bounded-source sclCALicensingOralEvidence wylieRoot
    attributedFirstPersonTestimony
    "https://committees.parliament.uk/oralevidence/7803/html/ ; Q1273"
    "2018-03-27" "2013-2014"
    "In oral evidence Wylie said SCL assigned IP to CA, CA licensed back to SCL Elections and granted an exclusive service arrangement. Witness testimony supports this attributed description, not verified signatures, exact licensed versions, or Aquino provenance; same author root as written FKN0079."
    true false false false
  ∷ bounded-source delaware2013FTCEntityFinding ftcRoot
    regulatoryFinding
    "https://www.ftc.gov/system/files/documents/cases/d09389_comm_final_opinionpublic.pdf ; printed p3 / PDF page index 2"
    "2019-12-06" "December 2013 and conduct 2014 onward"
    "The Commission's unopposed administrative opinion says the Delaware Cambridge Analytica company was formed in December 2013, shared functions, owners, officers and employees with SCL Elections. This resolves the bounded regulator position only, not the full original 2014 legal-counsel memo or a specific charter/entity-identifier clash."
    true false false false
  ∷ bounded-source caVersusCIAWitnessClarification wylieRoot
    attributedFirstPersonTestimony
    "https://committees.parliament.uk/oralevidence/7803/html/ ; Q1458-Q1459"
    "2018-03-27" "2018-03-27"
    "Asked if Cambridge Analytica shorthand was CIA rather than CA, Wylie clarified CA, not CIA. An initial perceived acronym is explicitly corrected in its originating source and cannot pay an intelligence-service identity."
    true false false false
  ∷ bounded-source bannonScheduledBreakfast2019 epsteinEstateScheduleRoot
    estateScheduleCarrier
    "https://oversightdemocrats.house.gov/imo/media/doc/epstein-production-3rd-tranch_456.pdf ; PDF page 2 (index 1)"
    "email timestamp 2019-02-14; publicly released 2025" "2019-02-16 07:00"
    "A redacted contemporaneous schedule emailed to Epstein lists a 7:00 a.m. breakfast with Steve Bannon on Saturday February 16, 2019. The listed appointment is an original-document datum; it does not establish attendance, conversation, production work, intelligence tasking or criminal conduct."
    true false false false
  ∷ bounded-source bannonOctober2018Messages epsteinCorrespondenceRoot
    releasedCorrespondence
    "https://static.poder360.com.br/2026/01/conversa-divulgada-doj-eua-epstein-steve-bannon.pdf ; EFTA01615409-01615412"
    "iMessage date 2018-10-12; copy hosted 2026" "2018-10-12"
    "A journalist-hosted four-page reproduction bearing DOJ EFTA identifiers depicts messages labelled Steve Bannon discussing Bolsonaro, other political actors and contacts. The reproduced images were visually inspected, but exact DOJ-native custody and complete surrounding thread were not checked. These messages are not independent corroboration of earlier summaries of the same underlying correspondence and do not establish Cambridge Analytica product reuse, covert tasking or criminal participation."
    true false false false
  ∷ bounded-source ftcServicesAndLicencesDescribed ftcRoot
    regulatoryFinding
    "https://www.ftc.gov/system/files/documents/cases/d09389_comm_final_opinionpublic.pdf ; PDF page index 4 / printed page 5, CCCSUF 17-22"
    "2019-12-06" "2014-06 and contemporaneous 2014 SCL/CA arrangements"
    "FTC default-case opinion reports a June 4 2014 GSR-SCL data agreement, an SCL-to-CA services agreement, and a SEPARATE SCL-to-CA IP licence. The opinion describes these agreements but is not their original signed artifact. These agreements do not pay Aquino methodological origin or later Epstein use."
    true false false false
  ∷ bounded-source fecDecember2013LLCStatement fecEnforcementRoot
    preliminaryElectionEnforcement
    "https://www.fec.gov/files/legal/murs/7382/7382_33.pdf ; PDF page index 5 / FEC factual/legal analysis p2 line 3 note 3"
    "2019-07-24" "2013-12-31"
    "FEC background cites the Delaware Division of Corporations as recording CA LLC organized December 31 2013. This is a separate official report but the underlying entity fact derives from the same state registry, not an independent second company charter."
    true false false false
  ∷ bounded-source fecForeignNationalReasonToBelieve fecEnforcementRoot
    preliminaryElectionEnforcement
    "https://www.fec.gov/data/legal/matter-under-review/7351/ ; case disposition and 2019 Commission determinations"
    "2019-07-24" "2014 election cycle"
    "FEC voted reason to believe 4-0 concerning Cambridge Analytica and certain participants under foreign-national election participation rules. This is preliminary regulatory investigation threshold, NOT a final adjudication or conviction."
    true false false false
  ∷ bounded-source fecCaseClosedWithoutFinalLiability fecEnforcementRoot
    electionMatterClosure
    "https://www.fec.gov/data/legal/matter-under-review/7351/ ; Commission voted 5-0 to close file (2021)"
    "2021-09/10" "2014 election-cycle allegations"
    "The Commission later voted to close the file after the 2019 reason-to-believe determination. Closure and the disposition records must be assessed at named allegation/respondent granularity. No inference of a final FEC liability decision follows from the earlier reason-to-believe vote."
    true false false false
  ∷ bounded-source wylieKompromatStatement2018 wylieRoot
    attributedFirstPersonTestimony
    "https://nsarchive.gwu.edu/sites/default/files/documents/5686049/Christopher-Wylie-Statement-for-the-Record-for.pdf ; printed p4 paragraph 15 / PDF page index 3"
    "2018-05-16" "during Wylie SCL/CA association, ca. 2013-2014"
    "Wylie testified he had heard of and seen documents relating to SCL/CA procurement of hacked material and kompromat, sometimes described internally as special intelligence services; he said Bannon was vice president at the time of some events. This is witness allegation, not independent proof of hacking, Bannon tasking, Epstein contact or intelligence command. Same author root as March 2018 oral and FKN0079 written evidence."
    true false false false
  ∷ bounded-source wylieProjectRiponStatement2018 wylieRoot
    attributedFirstPersonTestimony
    "https://nsarchive.gwu.edu/sites/default/files/documents/5686049/Christopher-Wylie-Statement-for-the-Record-for.pdf ; printed p5 paragraph 19 / PDF page index 4"
    "2018-05-16" "2013-2015"
    "Wylie testified that Bannon oversaw Project Ripon, which aimed to scale psychological profiling for campaigns using earlier Cambridge psychology research. Original project implementation/approval and individual role receipts are separate acquisitions; this does not prove Aquino or Epstein operational links."
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


------------------------------------------------------------------------
-- MISSING/DECEASED-SCIENTIST INVESTIGATION SPINE (PRIMARY RESEARCH INDEX)
--
-- These are *methodological* imports, not evidence that the scientists'
-- events share a cause with the historical Epstein network. H0/H1/H2/H3
-- describe claim promotion relative to the exact tested question, not a
-- globally transferable ordinal truth or culpability scale.
------------------------------------------------------------------------

-- The original programme-discriminator owns the essential negative gates.
caseCommonObjectMethodDoesNotPayCoordination :
  Common.programmeIdentityPaysTargeting ≡ false
caseCommonObjectMethodDoesNotPayCoordination = refl

caseTechnicalAdjacencyDoesNotPaySameObject :
  Common.technicalAdjacencyPaysCommonProgramme ≡ false
caseTechnicalAdjacencyDoesNotPaySameObject = refl

caseSourceRepetitionDoesNotPayIndependence :
  Common.sourceRepetitionPaysIndependentCorroboration ≡ false
caseSourceRepetitionDoesNotPayIndependence = refl

caseRequiresActualOperationalEvidence :
  Common.coordinatedTargetingRequiresOperationalEvidence ≡ true
caseRequiresActualOperationalEvidence = refl

-- Case-local status: the SCL/CA firm relationship and Bannon media contact
-- are real *bounded* bridges under their existing owner. This is NOT a
-- universal common-programme inference joining Aquino, the Maxwells, etc.
bannonFilmContactPriorOwner : BannonBridge.BridgeReceipt
bannonFilmContactPriorOwner = BannonBridge.bannonMediaRehabReceipt

bannonEpsteinContactLocatedInOwner :
  BannonBridge.relationshipOrInstitutionalEdgePaid
    bannonFilmContactPriorOwner ≡ true
bannonEpsteinContactLocatedInOwner = refl

bannonEpsteinToCommonProgrammeUnpaid :
  BannonBridge.sameObjectWithOtherInvestigationEstablished
    bannonFilmContactPriorOwner ≡ false
bannonEpsteinToCommonProgrammeUnpaid = refl

-- The programme hypothesis ladder remains indexed by scope. A pair-level
-- filmed interview does not identify the alleged programme extending back
-- through Robert Maxwell and Aquino and forward into political microtargeting.
data InvestigationScope : Set where
  boundedDirectMediaWork : InvestigationScope
  boundedSCLCorporateContinuity : InvestigationScope
  proposedCrossGenerationalIntelligenceCommand : InvestigationScope

record ProgrammeHypothesisCut : Set where
  constructor programme-hypothesis-cut
  field
    scope : InvestigationScope
    donorHypothesis : Common.HypothesisClass
    currentPaidRelationship : String
    literalWholeProgrammeIdentifierPaid : Bool
    operationalDirectionPaid : Bool
    firstUnpaid : String
open ProgrammeHypothesisCut public

historicalCommonCommandCut : ProgrammeHypothesisCut
historicalCommonCommandCut = programme-hypothesis-cut
  proposedCrossGenerationalIntelligenceCommand Common.H1
  "Bounded interpersonal, corporate and media relationships; these are different objects with different source roots"
  false false
  "One literal historical common-command/programme object, joined across relevant actors and event periods; then tasking/control records paying the claimed operation"

-- Original programme-search distance/cost fields are *hypothesis-specific*.
-- Do not invent scores or convert ranking into evidence; all paid flags are
-- false for these speculative cross-network programme transfers.
aquinoToSCLObjectSearch : ProgrammeFrontier.PromotionSearchCandidate
aquinoToSCLObjectSearch = ProgrammeFrontier.promotion-search-candidate
  "Michael Aquino / Paul Vallely MindWar authorship"
  "SCL / Cambridge Analytica"
  ProgrammeFrontier.institutionalWorkPackageSearch
  "1980 authored proposal and later SCL informational-operations work, separately supported"
  "Specific contemporaneous named implementation/manual/contract/product ID"
  "Dated literal cross-institution same-work-package/implementation artefact"
  "Tasking/control/operation receipt if a concrete common object is found"
  1 1 false false

maxwellPROMISNetworkSearch : ProgrammeFrontier.PromotionSearchCandidate
maxwellPROMISNetworkSearch = ProgrammeFrontier.promotion-search-candidate
  "Robert Maxwell alleged PROMIS distribution"
  "Later Epstein-linked institutional infrastructure"
  ProgrammeFrontier.programmeIdentifierSecondPersonSearch
  "House/Bua contested official claims and named historical PROMIS software"
  "Exact distributable PROMIS build, installation, procurement and customer ID"
  "A verified same-build/custody/contract link; allegations of a backdoor do not establish an installation"
  "Authenticated tasking/control bridge into Epstein-era activities"
  2 2 false false

bannonEpsteinWorkProductSearch : ProgrammeFrontier.PromotionSearchCandidate
bannonEpsteinWorkProductSearch = ProgrammeFrontier.promotion-search-candidate
  "Steve Bannon"
  "Jeffrey Epstein"
  ProgrammeFrontier.institutionalWorkPackageSearch
  "Existing BannonBridge pays sustained contact and attributed film-interview work at a bounded level"
  "Exact 2018-2019 filmed session, Bates correspondence, edits, production or payment ID"
  "Join one original primary message to the same primary audiovisual or production work product"
  "Distinct authenticated agency/tasking or control evidence, not just media strategy"
  0 1 false false

caseProgrammeSearchFront : List ProgrammeFrontier.PromotionSearchCandidate
caseProgrammeSearchFront =
  bannonEpsteinWorkProductSearch ∷ aquinoToSCLObjectSearch
  ∷ maxwellPROMISNetworkSearch ∷ []

-- Event-time employment/control is not inherited across the 1980/1990s
-- to 2014--19 timeline. This receipt explicitly marks the unsourced
-- later implementation of a *specific* method as temporally unresolved.
aquinoLaterSCLControl : EventTime.EventTimeCapabilityReceipt
aquinoLaterSCLControl = EventTime.event-time-capability-receipt
  "Michael Aquino and named 1980 MindWar proposal"
  "A specific SCL or Cambridge Analytica deployed influence system"
  EventTime.unresolvedTime
  "MindWar 1980; existing SCL/CA owner; no common implementation ID paid"
  "Temporal proximity and shared vocabulary do not provide an event-time role, authorship or access receipt"

bannonCAMethodLaterUse : EventTime.EventTimeCapabilityReceipt
bannonCAMethodLaterUse = EventTime.event-time-capability-receipt
  "Steve Bannon, Cambridge Analytica executive relationship"
  "Actual methods and datasets in the 2018-2019 Epstein documentary/media work"
  EventTime.unresolvedTime
  "Existing BannonBridge and Cambridge Analytica source carriers"
  "Earlier CA role and later media collaboration are supported independently; exact technique reuse, specific object and custody remain unlocated"

eventTimeNonPromotion :
  EventTime.historicalExpertiseImpliesEventTimePossession
    EventTime.canonicalEventTimeAlignmentBoundary ≡ false
eventTimeNonPromotion = refl

-- Test ordinary competing explanations before construing hidden transfer.
-- Licensing is not equivalent to Aquino intellectual lineage or a covert
-- state command. A partially evidenced transition must retain its limits.
sclIPLicensingAlternative : Fragility.FragilityReceipt
sclIPLicensingAlternative = Fragility.fragility-receipt
  "SCL / Cambridge Analytica operating and intellectual-property structures"
  Fragility.contractOrIPTransition Fragility.partial
  "Wylie DCMS attributed testimony (2018), FTC 2019 distinct finding"
  "Ordinary corporate licensing/personnel/service arrangements can explain common techniques and coordination without requiring the specific MindWar paper; executed licence and identical deployed artefact are still acquisition debt"

mundaneExplanationsFirst :
  Fragility.mundaneTransitionMustBeTestedBeforeTargetingPromotion
    Fragility.canonicalFragilityBoundary ≡ true
mundaneExplanationsFirst = refl

custodyNonPromotion :
  Custody.organisationalContinuityImpliesSameCarrierTransfer
    Custody.canonicalMatrixBoundary ≡ false
custodyNonPromotion = refl

-- Claim-indexed anti-echo-chamber discipline. No new source sweep is
-- asserted; missing contrary records and inaccessible originals are explicit.
caseAdversarialSearch : AntiEcho.ClaimSearchBoundary
caseAdversarialSearch = AntiEcho.claim-search-boundary
  "Aquino-to-SCL specific method transfer"
  "Original 1980 MindWar paper and original SCL/CA contract/manual"
  "Ordinary SCL service/licensing origins and independently developed influence methods"
  "Any dated contradiction of explicit programme or person identity"
  "1980 author root distinct from 2014 corporate root and 2018 Wylie testimony"
  "Public programme/contract records and counter-institutional explanations"
  "Original cross-institution implementation and transfer records not inspected"
  false true false

caseHypothesisTest : AntiEcho.HypothesisTestBoundary
caseHypothesisTest = AntiEcho.hypothesis-test-boundary
  AntiEcho.oneCommonProgramme
  "One verified pre-event work product identifying shared control, access and participants"
  "Different executed methods; disjoint company roles; alternative origins"
  "An original same-object common-programme receipt is missing"
  "Inspect dated signed source-specific contracts, product versions and tasking"
  "Search for contrary company provenance, mundane licensing and different programme identity"

------------------------------------------------------------------------
-- Four discriminating models; none is dismissed simply for lacking a
-- positive source in a narrow search window. These records specify planned
-- tests, NOT executed source sweeps or observations of wrongdoing.
------------------------------------------------------------------------

caseIndependentNetworksTest : AntiEcho.HypothesisTestBoundary
caseIndependentNetworksTest = AntiEcho.hypothesis-test-boundary
  AntiEcho.distributedIndependentProgrammes
  "Distinct ordinary corporate influence, media brokerage, historical PsyOps and disputed software procurement"
  "A shared dated operational tasking/custody record joining all relevant objects would disfavor independence"
  "Explicit cross-network same-object receipt unlocated"
  "Compare original contracts, methods, actual participants and dates without presumed inheritance"
  "Search for original same-build or same-task IDs contradicting independent organisational development"

caseLocalSubclustersTest : AntiEcho.HypothesisTestBoundary
caseLocalSubclustersTest = AntiEcho.hypothesis-test-boundary
  AntiEcho.linkedSubclusters
  "Bannon-CA corporate relationship and Bannon-Epstein media contact; separately Aquino-Vallely coauthorship"
  "A document proves local links do not imply no broader chain, but isolated independent lineages limit the inference"
  "Specific cross-cluster same-object transfer remains unpaid"
  "Reconcile released 2018-2019 correspondence against contracts and film objects"
  "Search for disjoint rights/custody, incompatible method/version and unconnected decision authority"

caseOneCrossGenerationalProgrammeTest : AntiEcho.HypothesisTestBoundary
caseOneCrossGenerationalProgrammeTest = AntiEcho.hypothesis-test-boundary
  AntiEcho.oneCommonProgramme
  "An exact common programme, work package, product or named governing agreement spanning relevant participants"
  "Distinct original objects with independently verified causes, custodians and timetables pressure this model"
  "No single exact object connecting Aquino, Robert Maxwell and Epstein to SCL/CA is inspected"
  "Obtain programme identifiers, original archived papers, licenses, binaries and role/date receipts"
  "Test mistaken entity joins (Robert Maxwell/Robert Mercer), posthumous attribution and unbroken custody assumptions"

caseOperationalDirectionTest : AntiEcho.HypothesisTestBoundary
caseOperationalDirectionTest = AntiEcho.hypothesis-test-boundary
  AntiEcho.coordinatedTargeting
  "For this different case the proposed operation is common covert exploitation/tasking, NOT scientist targeting"
  "Separate financial/contract paths, ordinary media production and contrary official findings"
  "Authenticated sponsor, instruction, recipient, specific coercive act and outcome receipt all missing"
  "Require independently sourced tasking, payment, artefact handling and recorded use on one common programme"
  "Test falsifiable timelines against documented ordinary activity and contrary agency reviews"

caseCompetingHypotheses : List AntiEcho.HypothesisTestBoundary
caseCompetingHypotheses =
  caseIndependentNetworksTest ∷ caseLocalSubclustersTest ∷
  caseOneCrossGenerationalProgrammeTest ∷ caseOperationalDirectionTest ∷ []

caseWholeH2Unpaid :
  literalWholeProgrammeIdentifierPaid historicalCommonCommandCut ≡ false
caseWholeH2Unpaid = refl

caseCovertH3Unpaid :
  operationalDirectionPaid historicalCommonCommandCut ≡ false
caseCovertH3Unpaid = refl

caseCounterEvidenceRequired :
  AntiEcho.counterSourceSearchRequired ≡ true
caseCounterEvidenceRequired = refl

caseSearchAbsenceNotHistoricalAbsence :
  AntiEcho.searchEngineNoHitDoesNotEqualHistoricalAbsence ≡ true
caseSearchAbsenceNotHistoricalAbsence = refl

caseAntiPanopticon :
  AntiEcho.bystanderCollectionMustRemainOutOfScope ≡ true
caseAntiPanopticon = refl

caseNarrativeNotAuthority :
  AntiEcho.narrativeSummaryCannotCreateSourceAuthority ≡ true
caseNarrativeNotAuthority = refl


------------------------------------------------------------------------
-- PROFESSIONAL EVIDENCE ROOM: ONE SOURCE, THREE DISTINCT USES
--
-- FKN0079 is a discoverable, attributable public submission but this case
-- cut has no retained native HTML snapshot, cryptographic digest or exact
-- signed corporate agreement. Those absent receipts stay explicitly open.
------------------------------------------------------------------------

wylieEvidenceRoomItem : EvidenceRoom.SharedEvidenceRoomItem
wylieEvidenceRoomItem = EvidenceRoom.shared-evidence-room-item
  "WYLIE-DCMS-FKN0079"
  "https://committees.parliament.uk/writtenevidence/89475/html/"
  "not acquired: independent archived native artifact"
  "public HTML original indexed and cited; no durable native bytes in this PR"
  "exact preservation/retrieval timestamp not retained"
  "attributed first-person parliamentary written evidence, not corporate finding"
  "UK Parliament evidence submission FKN0079"
  "Christopher Wylie author root; Parliamentary publication is not a second eyewitness"
  "Wylie asserts SCL-to-CA intellectual property and staffing relationship"
  "assertion about 2013-2014 organisations, NOT a signed implemented contract"
  "UNCOMPUTED: no native bytes in case branch"
  "source date 2018; underlying claimed event period 2013-2014"
  "other published repetitions of Wylie share the same source origin"
  "scope limited to what Wylie asserts; independent corporate instrument open"
  "does not by itself prove Aquino-specific technique or unified covert tasking"
  "public parliamentary HTML; only lawful, nonintrusive source acquisition"
  "native capture, revision and digest unresolved"
  "avoid victim/bystander data, false association and reputational harm"
  "corrections must preserve original wording and cite a specific later revision"

wylieInvestigatorGate : EvidenceRoom.InvestigatorGate
wylieInvestigatorGate = EvidenceRoom.investigator-gate
  "WYLIE-DCMS-FKN0079"
  "Exact SCL/CA executed method transfer and participant event-time control"
  "Acquire original dated 2014 contract, corporate register, full memo and implementation"
  true true false false
  "Wylie testimony supports attributed statements; signed operational handoff is still unpaid"
  "counter-source search scope not completely executed for the specific CA version"
  "inspect source-specific license, authors, source lineage and versioned work product"
  false

unverifiedMasterPlanPublicationGate : EvidenceRoom.JournalistGate
unverifiedMasterPlanPublicationGate = EvidenceRoom.journalist-gate
  "PROPOSED-UNIFIED-AQUINO-MAXWELL-EPSTEIN-CA"
  "Claim that all named parties participated in one directed intelligence exploitation programme"
  false
  "no independently authenticated programme/tasking chain acquired"
  "multiple narrators, conflicting interests and source-copying risk"
  "distinct programme eras and legal entities; no whole-network same-object"
  "right-of-reply status unresolved; no adverse-person publication action authorised"
  "historical accountability only within source-bounded, verifiable evidence"
  "avoid imputing child abuse/intelligence employment from association or faith"
  "victim confidentiality and relevant survivor privacy protected"
  "clearly attribute speculation to proponents; distinguish disputes and findings"
  "publish corrections and attach original claim revision"
  "NOT READY: unsupported causal allegation"

investigationNotPublication :
  EvidenceRoom.investigativeLeadDoesNotAutomaticallyBecomePublishable ≡ true
investigationNotPublication = refl

admissibilityNotHistory :
  EvidenceRoom.legalAdmissibilityDoesNotEqualHistoricalTruth ≡ true
admissibilityNotHistory = refl

publishedClaimNotAdmissible :
  EvidenceRoom.publishableClaimDoesNotAutomaticallyBecomeAdmissibleEvidence
    ≡ true
publishedClaimNotAdmissible = refl

sameItemDifferentGates :
  EvidenceRoom.sameNativeItemMayHaveDifferentConsumerStatuses ≡ true
sameItemDifferentGates = refl

-- Explicitly render case-level narrative status rather than rewarding
-- stylistic cohesion. This is DASHI synthesis using cited prior-owner facts.
caseObservedLocalLink : Narrative.NarrativeProposition
caseObservedLocalLink = Narrative.narrative-proposition
  Narrative.directlyEvidenced
  "Existing DASHI source-bounded receipts record Bannon/Epstein media collaboration and SCL/CA corporate relationships as separate local edges."
  "TrumpMarALagoBannonBridgeExact and BannonCambridgeAnalyticaInfluenceInfrastructureExact"
  "Direct existence of local relationships is not direct whole-network intelligence control."

caseBoundedMethodInference : Narrative.NarrativeProposition
caseBoundedMethodInference = Narrative.narrative-proposition
  Narrative.boundedInference
  "Some institutional practices recur across military psychological operations, commercial political marketing and reputation management."
  "Across-source methodological comparison in this case; not authored as an external-source finding"
  "Similarity does not identify an exact transferred method, common programme, sponsor or custodian."

caseUnsupportedUnifiedCommand : Narrative.NarrativeProposition
caseUnsupportedUnifiedCommand = Narrative.narrative-proposition
  Narrative.unsupported
  "Aquino, Robert Maxwell, Jeffrey Epstein and Bannon followed one continuous intelligence command."
  "No inspected exact whole-network tasking/payment/programme/custody chain"
  "The theory remains a proposition to test, not an adjudicated historical fact."

caseNarrativeStrata : List Narrative.NarrativeProposition
caseNarrativeStrata =
  caseObservedLocalLink ∷ caseBoundedMethodInference ∷
  caseUnsupportedUnifiedCommand ∷ []

caseStrataDoNotPromoteProgramme :
  Narrative.narrativeCannotSkipPromotionGate ≡ true
caseStrataDoNotPromoteProgramme = refl


------------------------------------------------------------------------
-- SOURCE-SPECIFIC MAX-CUT UPDATE: 2018 ORAL EVIDENCE / 2019 FTC / 2019
-- EPSTEIN ESTATE SCHEDULE. These are actual source observations at narrow
-- propositions, not whole-network H2/H3 identification or certification
-- of source integrity, signatures, attendance or any further misconduct.
------------------------------------------------------------------------

oralLicensingSource : BoundedSource
oralLicensingSource = bounded-source sclCALicensingOralEvidence wylieRoot
  attributedFirstPersonTestimony
  "https://committees.parliament.uk/oralevidence/7803/html/ ; Q1273"
  "2018-03-27" "2013-2014"
  "Wylie describes SCL IP assignment to CA and CA reciprocal licensing to SCL."
  true false false false

ftcDelawareEntitySource : BoundedSource
ftcDelawareEntitySource = bounded-source delaware2013FTCEntityFinding ftcRoot
  regulatoryFinding
  "https://www.ftc.gov/system/files/documents/cases/d09389_comm_final_opinionpublic.pdf ; p3"
  "2019-12-06" "2013-12"
  "FTC opinion records Delaware CA formed December 2013, within an administrative default proceeding."
  true false false false

bannonOctober2018MirrorSource : BoundedSource
bannonOctober2018MirrorSource = bounded-source bannonOctober2018Messages
  epsteinCorrespondenceRoot releasedCorrespondence
  "https://static.poder360.com.br/2026/01/conversa-divulgada-doj-eua-epstein-steve-bannon.pdf ; EFTA01615409-EFTA01615412"
  "2018-10-12; hosted 2026" "2018-10-12"
  "Four-page EFTA-labelled press-hosted reproduction inspected; political messages, not independent evidence of CAs operational tech transfer or intelligence command."
  true false false false

estateBannonScheduleSource : BoundedSource
estateBannonScheduleSource = bounded-source bannonScheduledBreakfast2019
  epsteinEstateScheduleRoot estateScheduleCarrier
  "https://oversightdemocrats.house.gov/imo/media/doc/epstein-production-3rd-tranch_456.pdf ; page 2"
  "2019-02-14; public release 2025" "2019-02-16"
  "7:00 a.m. breakfast entry with Steve Bannon; meeting held and object-level filmed work remain unverified."
  true false false false

-- The *bounded documentary* fact of a planned appointment is paid in the
-- original calendar artifact. The downstream real-world meeting and activity
-- must not be inferred from the date appearing on that artifact.
data ScheduleItem : Set where
  february2019PlannedBreakfast : ScheduleItem

data ScheduleOutcome : Set where
  listedOnly : ScheduleOutcome
  independentlyConfirmedOccurred : ScheduleOutcome

observedScheduleOutcome : ScheduleOutcome
observedScheduleOutcome = listedOnly

listedAppointmentNotConfirmedMeeting :
  observedScheduleOutcome ≡ listedOnly
listedAppointmentNotConfirmedMeeting = refl

data SourceStatementClass : Set where
  wylieWritten2018 : SourceStatementClass
  wylieOral2018 : SourceStatementClass
  ftcDelawareFinding2019 : SourceStatementClass
  counselMemoIndexed2014 : SourceStatementClass
  wylieSenateMay2018 : SourceStatementClass

-- Wylie's written and oral testimony are two distinct statements with
-- one author root, *not* two independent firsthand attestations.
data SourceStatementOrigin : SourceStatementClass → OriginRoot → Set where
  wylieWrittenOrigin :
    SourceStatementOrigin wylieWritten2018 wylieRoot
  wylieOralOrigin :
    SourceStatementOrigin wylieOral2018 wylieRoot
  ftcEntityOrigin :
    SourceStatementOrigin ftcDelawareFinding2019 ftcRoot
  wylieSenateOrigin :
    SourceStatementOrigin wylieSenateMay2018 wylieRoot

-- The counsel memo is only indexed in this cut. Its complete 22MB PDF
-- has NOT been inspected. Therefore no author-root or signed agreement
-- constructor is provided for it here.
data ContractDirection : Set where
  sclIPAssignedToCAAndLicensedBack : ContractDirection
  sclIPLicensedDirectlyToCA : ContractDirection

oralAttributedDirection : ContractDirection
oralAttributedDirection = sclIPAssignedToCAAndLicensedBack

indexedMemoReportedDirection : ContractDirection
indexedMemoReportedDirection = sclIPLicensedDirectlyToCA

differentDescriptionsRequireOriginalAgreements :
  oralAttributedDirection ≡ indexedMemoReportedDirection → ⊥
differentDescriptionsRequireOriginalAgreements ()

-- Distinct *descriptions* do not mean distinct historical contracts.
-- Full execution history might contain both stages; this cut does not
-- assert they are logically mutually exclusive in the real world.
data DescriptionsProveContradictoryHistoricalContracts : Set where

descriptionsDoNotResolveContractIdentity :
  DescriptionsProveContradictoryHistoricalContracts → ⊥
descriptionsDoNotResolveContractIdentity ()

data AcronymInQuestion : Set where
  caAbbreviation : AcronymInQuestion
  ciaAbbreviation : AcronymInQuestion

record TranscriptCorrection : Set where
  constructor transcript-correction
  field
    spokenCorrection : AcronymInQuestion
    locatedSource : String
open TranscriptCorrection public

oralCorrection : TranscriptCorrection
oralCorrection = transcript-correction caAbbreviation
  "Q1458-Q1459; 27 March 2018, UK Commons DCMS"

correctedAcronymIsCA : spokenCorrection oralCorrection ≡ caAbbreviation
correctedAcronymIsCA = refl

correctedAcronymIsNotCIA :
  spokenCorrection oralCorrection ≡ ciaAbbreviation → ⊥
correctedAcronymIsNotCIA ()


------------------------------------------------------------------------
-- EXACT 2014 CONTRACT STACK, BY DISTINCT SOURCE OBJECT (NOT ONE
-- PSYCHOLOGICAL-WARFARE TECHNOLOGY OR A CLAIM OF ORIGINAL SIGNED CUSTODY).
------------------------------------------------------------------------

data CorporateInstrument : Set where
  gsrSCLDataSubscription : CorporateInstrument
  sclCAOperatingServices : CorporateInstrument
  sclCAIPLicence : CorporateInstrument

record InstrumentSourceReceipt : Set where
  constructor instrument-source-receipt
  field
    instrument : CorporateInstrument
    parties : String
    datedInstrument : String
    source : String
    opinionDescribesAgreement : Bool
    originalSignedInstrumentInCustody : Bool
    aquinoTechniqueOriginPaid : Bool
    usedInBannonEpstein2018MediaPaid : Bool
open InstrumentSourceReceipt public

gsr2014Agreement : InstrumentSourceReceipt
gsr2014Agreement = instrument-source-receipt
  gsrSCLDataSubscription
  "Global Science Research Ltd and SCL Elections Ltd, signed for SCL by Alexander Nix"
  "2014-06-04; GSR creates scores and matches Facebook users and US voter records"
  "FTC opinion p5, CCCSUF 17-21 / complaint 14-15"
  true false false false

sclCAServiceAgreement : InstrumentSourceReceipt
sclCAServiceAgreement = instrument-source-receipt
  sclCAOperatingServices
  "SCL Elections and Cambridge Analytica LLC"
  "2014-era, exact execution date not in inspected FTC text"
  "FTC opinion p5, CCCSUF 21 / complaint 15"
  true false false false

sclCAIPAgreement : InstrumentSourceReceipt
sclCAIPAgreement = instrument-source-receipt
  sclCAIPLicence
  "SCL Elections agreed to license all of its IP to Cambridge Analytica LLC"
  "2014-era, exact executed copy/date not inspected"
  "FTC opinion p5, CCCSUF 21 / complaint 15"
  true false false false

canonicalInstrumentStack : List InstrumentSourceReceipt
canonicalInstrumentStack =
  gsr2014Agreement ∷ sclCAServiceAgreement ∷ sclCAIPAgreement ∷ []

ftcAgreementNotOriginalSignedInstrument :
  originalSignedInstrumentInCustody sclCAIPAgreement ≡ false
ftcAgreementNotOriginalSignedInstrument = refl

sclCAOperatingAgreementNotAquinoMethod :
  aquinoTechniqueOriginPaid sclCAServiceAgreement ≡ false
sclCAOperatingAgreementNotAquinoMethod = refl

sclCAIPLicenceNotEpsteinDataset :
  usedInBannonEpstein2018MediaPaid sclCAIPAgreement ≡ false
sclCAIPLicenceNotEpsteinDataset = refl

-- FTC independently characterises company/legal acts, but its December
-- 2013 date and the FEC citation of the Delaware registry may share that
-- original *state register* upstream; agency count != root independence
-- for the underlying incorporation record.
data IncorporationClaim : Set where
  caDelawareDecember2013 : IncorporationClaim
  counselMemoJune2014Description : IncorporationClaim

record DateAndSourceRole : Set where
  constructor date-and-source-role
  field
    formationClaim : IncorporationClaim
    carrier : String
    completePrimaryCharterInspected : Bool
    legalActSameObjectWeldPaid : Bool
open DateAndSourceRole public

fecCorporateDate : DateAndSourceRole
fecCorporateDate = date-and-source-role
  caDelawareDecember2013
  "FEC July 2019 factual/legal analysis p2 n3: Delaware registry viewed 2018-07-19"
  false false

ftcCorporateDate : DateAndSourceRole
ftcCorporateDate = date-and-source-role
  caDelawareDecember2013
  "FTC Commission Opinion December 2019 p3: original registry not itself retained"
  false false

counselMemoDate : DateAndSourceRole
counselMemoDate = date-and-source-role
  counselMemoJune2014Description
  "2014-07-22 legal memo index excerpt p6, full 22MB original uninspected"
  false false

uninspectedCharterCannotSettleDifferentLegalActs :
  legalActSameObjectWeldPaid counselMemoDate ≡ false
uninspectedCharterCannotSettleDifferentLegalActs = refl

-- Separate FEC stages: 'reason to believe' allowed investigation but
-- does not assert final liability. Later closing the file must not be
-- retroactively rewritten as a guilty verdict (or a blanket acquittal).
data FECProceduralStage : Set where
  reasonToBelieve2019 : FECProceduralStage
  fileClosed2021 : FECProceduralStage
  finalAdjudication : FECProceduralStage

record FECStageReceipt : Set where
  constructor fec-stage-receipt
  field
    stage : FECProceduralStage
    stageLocator : String
    sourceDates : String
    provesFinalLiability : Bool
open FECStageReceipt public

fecReasonToBelieveReceipt : FECStageReceipt
fecReasonToBelieveReceipt = fec-stage-receipt
  reasonToBelieve2019
  "FEC MUR 7351/7357 July 2019 reason-to-believe votes"
  "2019-07-24" false

fecClosureReceipt : FECStageReceipt
fecClosureReceipt = fec-stage-receipt
  fileClosed2021
  "FEC MUR 7351/7357 5-0 closure vote, 2021 record"
  "2021-09" false

fecReasonToBelieveNotFinalGuilt :
  provesFinalLiability fecReasonToBelieveReceipt ≡ false
fecReasonToBelieveNotFinalGuilt = refl

fecClosureDoesNotRewriteOriginalFindings :
  provesFinalLiability fecClosureReceipt ≡ false
fecClosureDoesNotRewriteOriginalFindings = refl


------------------------------------------------------------------------
-- WYLIE'S MAY 2018 SENATE STATEMENT IS EVIDENCE OF HIS ASSERTIONS,
-- NOT INDEPENDENT EVIDENCE OF THE ALLEGED OPERATIONS OR BANNON'S
-- KNOWLEDGE/RESPONSIBILITY. 'KomproMAT' vocabulary alone cannot
-- join CA's alleged services to the separate Epstein network.
------------------------------------------------------------------------

wylieAllegedSCLBlackOps : BoundedSource
wylieAllegedSCLBlackOps = bounded-source wylieKompromatStatement2018 wylieRoot
  attributedFirstPersonTestimony
  "Wylie Senate Judiciary prepared statement 2018-05-16, paragraph 15, PDF p4"
  "2018-05-16" "2013-2014"
  "Witness says he saw relevant documents and was informed of hacking/kompromat, with Bannon as VP during some events. Original incident case IDs, victims, records, actual commission and direction are not acquired."
  true false false false

wylieRiponStatement : BoundedSource
wylieRiponStatement = bounded-source wylieProjectRiponStatement2018 wylieRoot
  attributedFirstPersonTestimony
  "Wylie Senate Judiciary prepared statement 2018-05-16, paragraph 19, PDF p5"
  "2018-05-16" "2013-2015"
  "Witness states Bannon oversaw Project Ripon; independent signed original tasking, source code and delivery logs uninspected."
  true false false false

record AllegedKompromatProgrammeCut : Set where
  constructor alleged-kompromat-programme-cut
  field
    firstPersonStatementLocated : Bool
    independentlyAuthenticatedHackedArtifactLocated : Bool
    namedBannonOrderOrKnowledgeEstablished : Bool
    sameObjectEpsteinTaskingPaid : Bool
    operationalIntelligenceCommandPaid : Bool
open AllegedKompromatProgrammeCut public

canonicalKompromatCut : AllegedKompromatProgrammeCut
canonicalKompromatCut = alleged-kompromat-programme-cut
  true false false false false

testimonyDoesNotProveBannonHackingDirection :
  namedBannonOrderOrKnowledgeEstablished canonicalKompromatCut ≡ false
testimonyDoesNotProveBannonHackingDirection = refl

kompromatMethodDoesNotJoinEpsteinNetwork :
  sameObjectEpsteinTaskingPaid canonicalKompromatCut ≡ false
kompromatMethodDoesNotJoinEpsteinNetwork = refl

witnessReportingDoesNotPayIntelligenceCommand :
  operationalIntelligenceCommandPaid canonicalKompromatCut ≡ false
witnessReportingDoesNotPayIntelligenceCommand = refl
