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
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.CapabilityFragilityConfoundersBidiExact as Fragility
import DASHI.Culture.MissingDeceasedCustodyEventTimeMatrixExact as Custody
import DASHI.Cognition.TrumpMarALagoBannonBridgeExact as BannonBridge
import DASHI.Cognition.EpsteinBlackAgreementInvoiceWorkJoin20261015Exact as BlackWork
import DASHI.Cognition.EpsteinBlackInvoiceWireSettlement20261015Exact as BlackWire
import DASHI.Cognition.EpsteinBlackApolloSameObjectReceiptRound20261014Exact as BlackApollo
import DASHI.Cognition.EpsteinBankingInfrastructureAcquisitionExact as Banking
import DASHI.Cognition.AustraliaPoliticalEconomySameObjectCrosswalk20261026Exact as Auspol
import DASHI.Cognition.EpsteinBlackPaymentScopeReconciliation20261014Exact as BlackScope

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
  parliamentaryCommitteeFinding : SourceRole
  disputedAgencyReview : SourceRole
  releasedCorrespondence : SourceRole
  crossSourceHypothesis : SourceRole
  estateScheduleCarrier : SourceRole
  preliminaryElectionEnforcement : SourceRole
  electionMatterClosure : SourceRole
  sourceCodeDiscoveryReport : SourceRole
  reportingAboutReleasedFilm : SourceRole
  reviewOfInvestigativeRecords : SourceRole

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
  silvesterTestimonyRoot : OriginRoot
  dcmsCommitteeFinalReportRoot : OriginRoot
  nixWitnessRoot : OriginRoot
  koganWitnessRoot : OriginRoot
  upguardVickeryResearchRoot : OriginRoot
  guardianInterviewReportingRoot : OriginRoot
  apInvestigativeReviewRoot : OriginRoot

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
  silvesterAIQRiponDevelopment2018 : CaseClaim
  silvesterAIQBoltonDeployment2018 : CaseClaim
  dcmsRiponRepositoryReview2019 : CaseClaim
  dcmsICOBrexitCounterFinding2019 : CaseClaim
  nixAIQHistoricalRiponConfirmation : CaseClaim
  koganSeparateStatisticalDelivery : CaseClaim
  riponSourceCodePublicExposure2018 : CaseClaim
  bannonEpsteinVideoPublished2026 : CaseClaim
  associatedPressBlackmailCounterReview2026 : CaseClaim

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
  ∷ bounded-source silvesterAIQRiponDevelopment2018 silvesterTestimonyRoot
    attributedFirstPersonTestimony
    "https://committees.parliament.uk/oralevidence/7969/html/ ; Q2776-Q2783 Q2949-Q2955"
    "2018-05-16" "2014-2015"
    "Jeff Silvester testified AIQ built Ripon political CRM for SCL, under conditional code-transfer/ownership terms. He said AIQ had not contracted directly with CA and disclaimed authentication of an unsigned proposed AIQ-CA agreement. His testimony is independent witness-origin from Wylie's statements; signed contract/code remain separate artifacts."
    true false false false
  ∷ bounded-source silvesterAIQBoltonDeployment2018 silvesterTestimonyRoot
    attributedFirstPersonTestimony
    "https://committees.parliament.uk/oralevidence/7969/html/ ; Q2783-Q2784"
    "2018-05-16" "2014"
    "Silvester stated SCL asked AIQ to deploy the Ripon CRM to the John Bolton Super PAC's servers, and AIQ helped load client data. This pays the specific first-person claim about deployment, not unauthorized influence, CA contractual privity, or independently inspected server logs."
    true false false false
  ∷ bounded-source dcmsRiponRepositoryReview2019 dcmsCommitteeFinalReportRoot
    parliamentaryCommitteeFinding
    "https://publications.parliament.uk/pa/cm201719/cmselect/cmcumeds/1791/179107.htm ; paragraphs 149-162"
    "2019" "2013-2016"
    "UK Commons DCMS report describes original AIQ repository material supplied by Chris Vickery, Ripon source location scl.ripon.us, SCL/CA/AIQ code and data interplay, including OCEAN scores. The committee inspected/analyzed the materials, but repository bytes were not acquired here. Parliamentary analysis partly rests on separate Vickery, AIQ and ICO sources: avoid treating it as independent evidence of every constituent statement."
    true false false false
  ∷ bounded-source dcmsICOBrexitCounterFinding2019 dcmsCommitteeFinalReportRoot
    parliamentaryCommitteeFinding
    "https://publications.parliament.uk/pa/cm201719/cmselect/cmcumeds/1791/179107.htm ; paragraph 157 quoting ICO"
    "2019" "2016 referendum"
    "UK Commons DCMS report quotes the ICO as finding no evidence at that time of SCL Elections/CA data analytics work for EU referendum campaigns and no unlawful UK-citizen data activity in the stated AIQ-SCL relationship. Here the ICO text is a committee-reported counterfinding, not a separately inspected original ICO report."
    true false false false
  ∷ bounded-source nixAIQHistoricalRiponConfirmation nixWitnessRoot
    attributedFirstPersonTestimony
    "https://committees.parliament.uk/oralevidence/8065/html/ ; Q3259-Q3266"
    "2018-06-06" "2014"
    "Former CA chief Alexander Nix told Parliament AIQ built Ripon for them, a voter-engagement platform for audience targeting. He said he could not describe its technical implementation. His testimony is an independent speaker origin, though both Silvester/Nix may describe the same project and no original signed IP transfer is inspected."
    true false false false
  ∷ bounded-source koganSeparateStatisticalDelivery koganWitnessRoot
    attributedFirstPersonTestimony
    "https://committees.parliament.uk/oralevidence/7853/html/ ; Q2012-Q2018"
    "2018-04-24" "2014-2015"
    "Kogan says his team produced predictions using R, delivered password-protected spreadsheet-like files to SCL, and that he did not know AIQ or how Ripon used them downstream. A Kogan->AIQ direct personal relationship and identical dataset import are not paid by his own testimony."
    true false false false
  ∷ bounded-source riponSourceCodePublicExposure2018 upguardVickeryResearchRoot
    sourceCodeDiscoveryReport
    "https://www.upguard.com/breaches/aggregate-iq-part-one ; published 2018-03-26"
    "2018-03-26" "UpGuard reported discovery 2018-03-20"
    "Firsthand security researchers describe the exposed AIQ GitLab and project names Ripon_canvas and Ripon_dialer, campaign configuration and messaging integrations. The private repository, hashes, personal data and credentials are not acquired in this branch. UK Parliament's later description substantially relies on Vickery/UpGuard upstream and cannot independently multiply this particular discovery."
    true false false false
  ∷ bounded-source bannonEpsteinVideoPublished2026 guardianInterviewReportingRoot
    reportingAboutReleasedFilm
    "https://www.theguardian.com/us-news/2026/feb/05/steve-bannon-jeffrey-epstein-files-interview ; Guardian 2026-02-05"
    "2026-02-05" "film recorded circa 2019; public release 2026-01/02"
    "Guardian reports and describes an actual roughly two-hour filmed Bannon-Epstein interview seen after DOJ disclosure. CBS 2026-02-10 reports DOJ Data Set 10 and Free Press compilation of 14 hours of different Epstein video objects; 14 hours is NOT an authenticated duration of one Bannon interview. This branch has not inspected DOJ-native video bytes, timestamps, edit history or a same-object join to the February 2019 scheduled breakfast."
    true false false false
  ∷ bounded-source associatedPressBlackmailCounterReview2026 apInvestigativeReviewRoot
    reviewOfInvestigativeRecords
    "https://www.pbs.org/newshour/nation/ap-review-on-what-the-epstein-files-show-about-the-fbi-investigation-of-possible-sex-trafficking ; AP via PBS 2026-02-08"
    "2026-02-08" "underlying FBI/DOJ investigations 2005-2025"
    "AP reviewed DOJ/FBI records and reported scant investigative evidence for a wider operation trafficking victims to powerful men. This is a reported review and important contrary evidence, NOT proof that no blackmail or exploitation ever occurred, and not a denial of Epstein and Maxwell's established sexual-abuse crimes. Syndications of the same AP piece are one AP journalist/root family."
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
  "EFTA01600824 timecoded transcript accepted for research; film existence, identifier and transcript located in parent; original counsel agreement execution remains separate"
  "April 3 2019 EFTA00809863-Indyke letter located; July 2019 HOUSE_OVERSIGHT_027794-027848 shoot planning located. Verify actual signed acceptance, compute a hash for exact DOJ EFTA01600824.mov without vendoring and join filming session/terms"
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
  "Prior owner pays filmed interview + located Apr 3 2019 Indyke/EFTA engagement text + dated Jun-Jul 2019 House shoot messages; exact released reel join still unpaid"
  true true true false false
  "Film and timecoded transcript already indexed. For legal ownership or actual service claims, match signed/assented Indyke engagement to production records and completed shoot; hash optional and not required for transcript research; no automatic CA method reuse."

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
-- The actual interview/video was ALREADY paid in the canonical owner
-- before this case-specific max-cut. Work continues only on exact-object
-- source/custody and contractual disposition of individual reels.
bannonTranscriptResearchPolicy : BannonBridge.TranscriptResearchAcceptance
bannonTranscriptResearchPolicy = BannonBridge.canonicalTranscriptResearchAcceptance

bannonTranscriptNowAdequateForResearch :
  BannonBridge.existingExternalTimecodedASRIsSufficient
    bannonTranscriptResearchPolicy ≡ true
bannonTranscriptNowAdequateForResearch = refl

bannonFilmSHAIsNotBlocking :
  BannonBridge.researchRequiresVideoSHA256
    bannonTranscriptResearchPolicy ≡ false
bannonFilmSHAIsNotBlocking = refl

bannonTranscriptNotBlackPaymentEvidence :
  BannonBridge.transcriptProvesBlackTransactions
    bannonTranscriptResearchPolicy ≡ false
bannonTranscriptNotBlackPaymentEvidence = refl

bannonOriginalContractStillSeparate :
  BannonBridge.exactSceneConnectedToIndykeAgreement
    bannonTranscriptResearchPolicy ≡ false
bannonOriginalContractStillSeparate = refl

bannonTranscriptContentPriorOwner : List BannonBridge.TimecodedTranscriptReceipt
bannonTranscriptContentPriorOwner = BannonBridge.canonicalTranscriptContentCuts

bannonIdentifiedDOJReelIndex : BannonBridge.LocatedVideoTranscriptIndex
bannonIdentifiedDOJReelIndex = BannonBridge.bannonOriginalReelIndex

bannonDOJIdentifierNowLocated :
  BannonBridge.originalDOJReelIdentifierLocated
    bannonIdentifiedDOJReelIndex ≡ true
bannonDOJIdentifierNowLocated = refl

bannonTimecodedTranscriptNowLocated :
  BannonBridge.thirdPartyTimecodedTranscriptLocated
    bannonIdentifiedDOJReelIndex ≡ true
bannonTimecodedTranscriptNowLocated = refl

bannonDOJHashStillUnverified :
  BannonBridge.sourceVideoContentDigestVerified
    bannonIdentifiedDOJReelIndex ≡ false
bannonDOJHashStillUnverified = refl

bannonExistingProductionChain : BannonBridge.BannonMediaProductionFrontier
bannonExistingProductionChain = BannonBridge.canonicalBannonMediaProductionFrontier

preExistingFilmedInterviewIsPaid :
  BannonBridge.releasedInterviewExistencePaid
    bannonExistingProductionChain ≡ true
preExistingFilmedInterviewIsPaid = refl

preExistingAprilCounselLetterLocated :
  BannonBridge.engagementLetterTextLocated
    bannonExistingProductionChain ≡ true
preExistingAprilCounselLetterLocated = refl

preExistingJulyShootingMessagesLocated :
  BannonBridge.july6ProductionPlanningMessagesLocated
    bannonExistingProductionChain ≡ true
preExistingJulyShootingMessagesLocated = refl

actualSignedAgreementStillUnverified :
  BannonBridge.originalCounselLetterSignatureVerified
    bannonExistingProductionChain ≡ false
actualSignedAgreementStillUnverified = refl

reelBytesHashStillUnverified :
  BannonBridge.specificVideoReelFileIdAndHashVerified
    bannonExistingProductionChain ≡ false
reelBytesHashStillUnverified = refl

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
  "Existing BannonBridge pays sustained contact; Guardian/CBS February 2026 describe actual released 2019 filmed interview from DOJ Data Set 10, video object exists but film bytes not inspected here"
  "DOJ letter EFTA00809863-866, House shoot messages and EFTA01600824 indexed timecoded transcript now known. Interview-content research paid without video hash; signed Indyke terms and same-shoot legal chain remain open"
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
  "Bannon-CA corporate relationship and Bannon-Epstein actual film object reported in February 2026; separately Aquino-Vallely coauthorship; no same dataset crossing paid"
  "A document proves local links do not imply no broader chain, but isolated independent lineages limit the inference"
  "Specific cross-cluster same-object transfer remains unpaid"
  "Prior owner holds April 3 counsel terms, June-July plans and EFTA01600824 transcript: enough for research. Original film hash only optional for integrity; if claiming legal ownership still verify signed terms, actual filming date and completed shoot."
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
  "Separate financial/contract paths, ordinary media production, DOJ/FBI July 2025 no-credible-blackmail-evidence review position and AP Feb 2026 investigative contrary analysis"
  "Authenticated sponsor, instruction, recipient, specific coercive act and outcome receipt all missing"
  "Require independently sourced tasking, payment, artefact handling and recorded use on one common programme"
  "Test claimed intelligence tasking against exact dates, ordinary activity, actual DOJ/FBI memo scope and AP's bounded February 2026 review, not against mere contact or a theoretically impossible universal negative"

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


------------------------------------------------------------------------
-- LOCAL LITERAL RIPON OBJECT: A DOCUMENTED TECHNICAL / CONTRACTUAL
-- SUBCLUSTER, NOT THE AQUINO-MAXWELL-EPSTEIN COMMON PROGRAMME.
--
-- Two distinct witness roots + DCMS source-object report. The DCMS report
-- depends in part on the same witness, an ICO conclusion and the Vickery
-- acquired repository, so its full assertions are NOT independent third
-- producer receipts until lineage is resolved per proposition.
------------------------------------------------------------------------

silvesterRiponEvidence : BoundedSource
silvesterRiponEvidence = bounded-source silvesterAIQRiponDevelopment2018
  silvesterTestimonyRoot attributedFirstPersonTestimony
  "UK Commons Q2776-Q2783 and Q2949-Q2955, 2018-05-16"
  "2018-05-16" "2014-2015"
  "AIQ built and conditionally transferred Ripon CRM software to SCL; asserted non-privity with CA"
  true false false false

dcmsRiponProjectReport : BoundedSource
dcmsRiponProjectReport = bounded-source dcmsRiponRepositoryReview2019
  dcmsCommitteeFinalReportRoot parliamentaryCommitteeFinding
  "UK Commons Final Report 2019 HC 1791 chapter 4, paragraphs 149-162"
  "2019" "2014 onward"
  "Committee reported Ripon repository inspection, scl.ripon.us linkage and OCEAN-related data; original code bytes not personally preserved in this case branch"
  true false false false

record ScopedRiponObjectPayment : Set where
  constructor scoped-ripon-object-payment
  field
    namedRiponProductPaid : Bool
    contractorSCLRelationPaid : Bool
    clientSpecificDeploymentTestimonyLocated : Bool
    committeeReviewedCodeLineageLocated : Bool
    actualSourceTreeBytesRetainedHere : Bool
    fullCodeTransferSignaturesRetainedHere : Bool
    personalBannonSourceCodeControlPaid : Bool
    riponSameProgrammeAsAquinoPaid : Bool
    riponSameProgrammeAsEpsteinPaid : Bool
    commonIntelligenceOperationPaid : Bool
open ScopedRiponObjectPayment public

localRiponObject : ScopedRiponObjectPayment
localRiponObject = scoped-ripon-object-payment
  true true true true false false false false false false

localH2ProgrammeObjectPaid :
  namedRiponProductPaid localRiponObject ≡ true
localH2ProgrammeObjectPaid = refl

localRiponDeveloperToSCLRelationPaid :
  contractorSCLRelationPaid localRiponObject ≡ true
localRiponDeveloperToSCLRelationPaid = refl

riponSourceTreeNotInCaseCustody :
  actualSourceTreeBytesRetainedHere localRiponObject ≡ false
riponSourceTreeNotInCaseCustody = refl

riponPersonalBannonCodeControlUnpaid :
  personalBannonSourceCodeControlPaid localRiponObject ≡ false
riponPersonalBannonCodeControlUnpaid = refl

riponDoesNotPromoteAquinoLink :
  riponSameProgrammeAsAquinoPaid localRiponObject ≡ false
riponDoesNotPromoteAquinoLink = refl

riponDoesNotPromoteEpsteinLink :
  riponSameProgrammeAsEpsteinPaid localRiponObject ≡ false
riponDoesNotPromoteEpsteinLink = refl

localRiponH2NotGlobalH3 :
  commonIntelligenceOperationPaid localRiponObject ≡ false
localRiponH2NotGlobalH3 = refl

-- Test the same-object *scoping* on the specific part of the network.
-- 'H2' here means the admitted local Ripon software programme, not an
-- object identity spanning every historical actor in the user theory.
data RiponIdentityScope : Set where
  aiqSCLRiponSoftware : RiponIdentityScope
  aquinoMaxwellEpsteinCommonProgramme : RiponIdentityScope

record RiponSameObjectBoundary : Set where
  constructor ripon-same-object-boundary
  field
    scope : RiponIdentityScope
    sourceBackedLocalProgramme : Bool
    intergenerationalBridgePaid : Bool
open RiponSameObjectBoundary public

localRiponScope : RiponSameObjectBoundary
localRiponScope = ripon-same-object-boundary
  aiqSCLRiponSoftware true false

unifiedNetworkScope : RiponSameObjectBoundary
unifiedNetworkScope = ripon-same-object-boundary
  aquinoMaxwellEpsteinCommonProgramme false false

scopedH2DoesNotChangeWholeNetworkH2 :
  intergenerationalBridgePaid localRiponScope ≡ false
scopedH2DoesNotChangeWholeNetworkH2 = refl


------------------------------------------------------------------------
-- MULTI-WITNESS, SINGLE-SOFTWARE IDENTIFIER; THE DIRECT DEVELOPER
-- (SILVESTER), COMPANY EXECUTIVE (NIX) AND UPSTREAM MODELLER (KOGAN)
-- HAVE DIFFERENT FIRST-PERSON COVERAGE. CODE-CUSTODY / DATA-IDENTITY
-- REMAINS A SEPARATE BIDI CONSUMER.
------------------------------------------------------------------------

data RiponRole : Set where
  developerSilvester : RiponRole
  commissioningExecutiveNix : RiponRole
  upstreamModelProducerKogan : RiponRole

record RiponRoleStatement : Set where
  constructor ripon-role-statement
  field
    role : RiponRole
    root : OriginRoot
    locatedTranscript : String
    paysSpecificRiponSoftwareRole : Bool
    paysDirectKoganAIQCollaboration : Bool
    paysIdenticalDatasetFingerprint : Bool
open RiponRoleStatement public

silvesterRole : RiponRoleStatement
silvesterRole = ripon-role-statement
  developerSilvester silvesterTestimonyRoot
  "UK DCMS 2018-05-16 Q2776-Q2784"
  true false false

nixRole : RiponRoleStatement
nixRole = ripon-role-statement
  commissioningExecutiveNix nixWitnessRoot
  "UK DCMS 2018-06-06 Q3259-Q3266"
  true false false

koganRole : RiponRoleStatement
koganRole = ripon-role-statement
  upstreamModelProducerKogan koganWitnessRoot
  "UK DCMS 2018-04-24 Q2012-Q2018: R/statistical output sent to SCL"
  false false false

silvesterNamesRipon :
  paysSpecificRiponSoftwareRole silvesterRole ≡ true
silvesterNamesRipon = refl

nixNamesRipon :
  paysSpecificRiponSoftwareRole nixRole ≡ true
nixNamesRipon = refl

koganDeliveryDoesNotPayDirectAIQKnowledge :
  paysDirectKoganAIQCollaboration koganRole ≡ false
koganDeliveryDoesNotPayDirectAIQKnowledge = refl

originalDatasetFingerprintStillUnpaid :
  paysIdenticalDatasetFingerprint koganRole ≡ false
originalDatasetFingerprintStillUnpaid = refl


------------------------------------------------------------------------
-- 2026 REPORTING MAX-CUT: ORIGINAL-SOURCE ROOTS / REPRINTS / MOVING
-- OBJECT STATUS. Public reporting is not a transfer of private voter
-- records, victim media, raw keys, code credentials, or criminal guilt.
------------------------------------------------------------------------

record ExternalObjectEvidenceCut : Set where
  constructor external-object-evidence-cut
  field
    describedSourceRoot : String
    narrowSupportedDescription : String
    originalNativeObjectHeldByThisPR : Bool
    independentSecondWitnessToSameRoot : Bool
    historicalEventOccurrenceSupported : Bool
    broaderIntelligenceProgrammePaid : Bool
open ExternalObjectEvidenceCut public

upguardRiponCodeReportingCut : ExternalObjectEvidenceCut
upguardRiponCodeReportingCut = external-object-evidence-cut
  "Chris Vickery/UpGuard initial discovery 2018-03-20, report 2018-03-26"
  "Original investigator describes publicly exposed Ripon_canvas, Ripon_dialer, and campaign configuration; DCMS committee later reports on that same discovered repository."
  false false true false

bannonFilmedInterviewReportingCut : ExternalObjectEvidenceCut
bannonFilmedInterviewReportingCut = external-object-evidence-cut
  "Underlying released DOJ Data Set 10 filmed interview; journalists report and excerpt, underlying footage is one film origin"
  "Real filmed Bannon-Epstein interview described by journalists; source now identified as DOJ Data Set 10 EFTA01600824.mov, with publicly indexed timecoded ASR; native digest, production metadata and named camera date remain open"
  false false true false

associatedPressContraryReviewCut : ExternalObjectEvidenceCut
associatedPressContraryReviewCut = external-object-evidence-cut
  "AP reporters Sisak, Caruso and Neumeister, review published 2026-02-08"
  "AP reports FBI documentary review found scant evidence of systematic supply of victims to powerful people; memo contents not independently re-reviewed in this PR"
  false false true false

upguardBlogIsNotOriginalGitTree :
  originalNativeObjectHeldByThisPR upguardRiponCodeReportingCut ≡ false
upguardBlogIsNotOriginalGitTree = refl

newsOfFilmIsNotOriginalFootage :
  originalNativeObjectHeldByThisPR bannonFilmedInterviewReportingCut ≡ false
newsOfFilmIsNotOriginalFootage = refl

filmedInterviewNotCovertTasking :
  broaderIntelligenceProgrammePaid bannonFilmedInterviewReportingCut ≡ false
filmedInterviewNotCovertTasking = refl

pressReviewDoesNotProveUniversalAbsence :
  broaderIntelligenceProgrammePaid associatedPressContraryReviewCut ≡ false
pressReviewDoesNotProveUniversalAbsence = refl

-- Typed category separation: fourteen hours of mixed DOJ video material
-- is not the timestamp, reel identity or duration of the Bannon interview.
data ReleasedVideoUnit : Set where
  bannonInterviewSequence : ReleasedVideoUnit
  fullDataSet10VideoCompilation : ReleasedVideoUnit

videoCompilationIsNotBannonReel :
  bannonInterviewSequence ≡ fullDataSet10VideoCompilation → ⊥
videoCompilationIsNotBannonReel ()

-- Source-origin accounting: the committee and UpGuard may be different
-- publications yet both rely on Vickery's same repository acquisition.
data RiponDiscoveryCarrier : Set where
  upguardMarch2018Report : RiponDiscoveryCarrier
  ukCommittee2019Account : RiponDiscoveryCarrier

record RootDependency : Set where
  constructor root-dependency
  field
    carrier : RiponDiscoveryCarrier
    upstreamTechnicalProducer : String
open RootDependency public

originalDiscoveryRoot : RootDependency
originalDiscoveryRoot = root-dependency upguardMarch2018Report
  "Vickery/UpGuard 2018-03-20 AggregateIQ repository acquisition"

committeeTechnicalRoot : RootDependency
committeeTechnicalRoot = root-dependency ukCommittee2019Account
  "Vickery/UpGuard 2018-03-20 AggregateIQ repository acquisition"

-- These values exhibit declared common lineage, not proof that the
-- committee supplied no additional independent tests or conclusions.
riponTechnicalRootShared :
  upstreamTechnicalProducer originalDiscoveryRoot ≡
  upstreamTechnicalProducer committeeTechnicalRoot
riponTechnicalRootShared = refl


------------------------------------------------------------------------
-- LEON BLACK CONTROL CASE: a different *documented* Epstein workstream.
--
-- Prior Black/Epstein work is extensive: signed-vs-draft agreement versions,
-- EFTA00585292 USD20m 2014 invoice, EFTA01915809 settled-wire email,
-- estate planning EFTA00583490 and later legal-review artefacts. They set
-- an empirical standard for payer→agreement→invoice→wire→specific work.
--
-- They do NOT show that Bannon contracted under the Black arrangements,
-- received Black-financed video work, used CA analytics, or shared a covert
-- command. Those would require their own exact-object identifiers.
------------------------------------------------------------------------

blackPreExistingAgreementWork : BlackWork.WorkJoinBoundary
blackPreExistingAgreementWork = BlackWork.canonicalWorkJoinBoundary

blackPreExistingSettledWire : BlackWire.WireBoundary
blackPreExistingSettledWire = BlackWire.canonicalWireBoundary

blackPreExistingApolloNuance : BlackApollo.ApolloNuanceBoundary
blackPreExistingApolloNuance = BlackApollo.canonicalApolloNuanceBoundary

blackServicesDocumented :
  BlackWork.paidServiceAgreementSurface blackPreExistingAgreementWork ≡ true
blackServicesDocumented = refl

blackInvoiceDocumented :
  BlackWork.paidEstatePlanningInvoiceSurface blackPreExistingAgreementWork ≡ true
blackInvoiceDocumented = refl

black2014InvoiceAndReceiptMatched :
  BlackWire.july2014InvoiceAndReceiptJoinPaid blackPreExistingSettledWire ≡ true
black2014InvoiceAndReceiptMatched = refl

blackPaymentNotIdentifiedAsChecklistFee :
  BlackWork.exactInvoiceToChecklistItemPaid blackPreExistingAgreementWork ≡ false
blackPaymentNotIdentifiedAsChecklistFee = refl

blackInvoiceAndWireNotMeasuredTaxBenefit :
  BlackWire.settledWireImpliesMeasuredTaxBenefit blackPreExistingSettledWire ≡ false
blackInvoiceAndWireNotMeasuredTaxBenefit = refl

apolloNeverAutomaticallyBannonPayer :
  BlackApollo.apolloCorporationRetainedEpstein blackPreExistingApolloNuance ≡ false
apolloNeverAutomaticallyBannonPayer = refl

bannonFilmAlreadyEstablishedByDifferentOwner :
  BannonBridge.releasedInterviewExistencePaid
    BannonBridge.canonicalBannonMediaProductionFrontier ≡ true
bannonFilmAlreadyEstablishedByDifferentOwner = refl

bannonOriginalReelHashNotReplacedByBlackReceipts :
  BannonBridge.specificVideoReelFileIdAndHashVerified
    BannonBridge.canonicalBannonMediaProductionFrontier ≡ false
bannonOriginalReelHashNotReplacedByBlackReceipts = refl

-- Exact financial receipts within Black's *different* network do not fill
-- a missing Bannon-film contract, video hash or Aquino/CA reuse bridge.
data BlackPaymentImpliesBannonFilmFunding : Set where
data BlackPaymentImpliesBannonCAEpsteinCommonCommand : Set where

blackPaymentDoesNotCreateBannonFilmFunding :
  BlackPaymentImpliesBannonFilmFunding → ⊥
blackPaymentDoesNotCreateBannonFilmFunding ()

blackPaymentDoesNotCreateUnifiedProgramme :
  BlackPaymentImpliesBannonCAEpsteinCommonCommand → ⊥
blackPaymentDoesNotCreateUnifiedProgramme ()


------------------------------------------------------------------------
-- HOUSE 2026 CASE CONSUMER: reuse the Black source owner, not a new
-- payment/command model. Congressional procedure is a distinct object
-- from testimony, contractual bytes, or an operational intelligence chain.
------------------------------------------------------------------------

black2026OriginalCongressionalCase :
  BlackApollo.Black2026HouseBoundary
black2026OriginalCongressionalCase =
  BlackApollo.canonicalBlack2026HouseBoundary

originalBlackInterviewAndHouseDispositionLocated :
  BlackApollo.houseResolutionRecorded black2026OriginalCongressionalCase ≡ true
originalBlackInterviewAndHouseDispositionLocated = refl

house2026NDAContractBytesRemainUninspected :
  BlackApollo.executed2015NDABytesInspected black2026OriginalCongressionalCase ≡ false
house2026NDAContractBytesRemainUninspected = refl

house2026CommitteeIsNotTransactionReconciliation :
  BlackApollo.exactNDAtoBlackPaymentLedgerJoinPaid black2026OriginalCongressionalCase ≡ false
house2026CommitteeIsNotTransactionReconciliation = refl

house2026PastCIAOfficeNotPresentDirection :
  BlackApollo.corporateDirectorPastCIARoleIsCurrentTasking black2026OriginalCongressionalCase ≡ false
house2026PastCIAOfficeNotPresentDirection = refl

house2026DoesNotPayBannonProgrammeBridge :
  BlackApollo.blackCommitteeInquiryJoinsBannonFilm black2026OriginalCongressionalCase ≡ false
house2026DoesNotPayBannonProgrammeBridge = refl

house2026DoesNotPayCaseWideCommand :
  BlackApollo.caseWideCovertCommandEstablished black2026OriginalCongressionalCase ≡ false
house2026DoesNotPayCaseWideCommand = refl

------------------------------------------------------------------------
-- 2026 LEGAL-CASE IDENTITY: the SDNY October voluntary Doe dismissal is
-- NOT the DDC September challenge to House Oversight subpoenas.
------------------------------------------------------------------------

blackCivilCaseIdentityReceipt :
  BlackApollo.Black2026DistinctCourtCaseBoundary
blackCivilCaseIdentityReceipt =
  BlackApollo.canonicalBlack2026DistinctCourtCaseBoundary

blackDoeOrderNotHouseCaseDisposition :
  BlackApollo.sdnyOrderAdjudicatesHouseSubpoenaCase blackCivilCaseIdentityReceipt ≡ false
blackDoeOrderNotHouseCaseDisposition = refl

blackDoeDismissalNotMeritsTrialFinding :
  BlackApollo.sdnyDismissalIsTrialFactFinding blackCivilCaseIdentityReceipt ≡ false
blackDoeDismissalNotMeritsTrialFinding = refl

ddcHouseSubpoenaJudgmentNotYetVerified :
  BlackApollo.ddcFinalDispositionIndependentlyVerified blackCivilCaseIdentityReceipt ≡ false
ddcHouseSubpoenaJudgmentNotYetVerified = refl


------------------------------------------------------------------------
-- TRANSFER-CHAIN / LEAD-PRODUCT PARETO 2026-10-24
-- New original source roots folded into established case and bank owners.
------------------------------------------------------------------------

data Ripon2018SourceRoot : Set where
  silvesterWritten2018 : Ripon2018SourceRoot
  dcmsReport2019 : Ripon2018SourceRoot
  koganOral2018 : Ripon2018SourceRoot
  ftcAdministrative2019 : Ripon2018SourceRoot

record RiponIndependentChainEvidence : Set where
  constructor ripon-independent-chain-evidence
  field
    chainRoot : Ripon2018SourceRoot
    chainOriginalLocator : String
    chainNarrowAssertion : String
    chainSourceLocated : Bool
    chainNativeDataBytesAuditedHere : Bool
    chainDirectCAAIQContractExecutedPaid : Bool
open RiponIndependentChainEvidence public

silvesterWrittenOriginal2018 : RiponIndependentChainEvidence
silvesterWrittenOriginal2018 = ripon-independent-chain-evidence
  silvesterWritten2018
  "UK Commons FKN0086 https://committees.parliament.uk/writtenevidence/90210/html/"
  "Silvester says AIQ worked for SCL, SCL required IP transfer of the Ripon CRM, AIQ billed SCL; he disputes the unsigned purported direct CA-AIQ agreement and says he did not use Kogan Facebook source data. Same author as his oral testimony, not a second independent witness."
  true false false

dcmsRiponOCEANReview2019 : RiponIndependentChainEvidence
dcmsRiponOCEANReview2019 = ripon-independent-chain-evidence
  dcmsReport2019
  "UK DCMS HC1791 chapter4 paragraphs 157-160 https://publications.parliament.uk/pa/cm201719/cmselect/cmcumeds/1791/179107.htm"
  "Committee describes Vickery-origin repository debug logs importing OCEAN scores into Ripon and code from a CA-controlled domain. It also preserves the ICO's narrower contrary findings. Committee analysis is not independent native Git custody and is not proof of an executed direct AIQ-CA agreement."
  true false false

koganSeparateDelivery2018 : RiponIndependentChainEvidence
koganSeparateDelivery2018 = ripon-independent-chain-evidence
  koganOral2018
  "UK Commons Kogan 2018-04-24 Q2014 https://committees.parliament.uk/oralevidence/7853/html/"
  "Kogan describes R-generated scores sent as password-protected spreadsheet files to SCL and says he did not know how Ripon was used. His output-to-SCL statement does not identify the exact spreadsheet ingested by AIQ."
  true false false

ftcOriginalCorporateContracts2019 : RiponIndependentChainEvidence
ftcOriginalCorporateContracts2019 = ripon-independent-chain-evidence
  ftcAdministrative2019
  "FTC matter 182-3107, Docket 9383; https://www.ftc.gov/legal-library/browse/cases-proceedings/182-3107-cambridge-analytica-llc-matter"
  "FTC administrative finding against CA and source account of GSR-SCL data subscription, SCL-CA services and separate IP licence; these contracts cannot be collapsed into a signed direct AIQ-CA contract."
  true false false

-- This witness is deliberately only a *consistent evidence-state model*:
-- SCL contracts and downstream CA-origin data can coexist with the absence
-- of a verified DIRECT AIQ-CA signed contract. It is not a theorem that
-- source data did or did not pass through a particular chain in reality.
record RiponIntermediaryCountermodel : Set where
  constructor ripon-intermediary-countermodel
  field
    silvesterReportsSCLDirectContract : Bool
    dcmsReportsCAEcosystemDataFlow : Bool
    directAIQCAAgreementAuthenticated : Bool
    namedKoganOutputEqualsAIQImportProven : Bool
    namedRiponProvesAquinoMethodTransfer : Bool
    namedRiponProvesEpsteinMediaUse : Bool
open RiponIntermediaryCountermodel public

canonicalRiponIntermediaryCountermodel : RiponIntermediaryCountermodel
canonicalRiponIntermediaryCountermodel =
  ripon-intermediary-countermodel true true false false false false

riponSCLContractAndReportedCAEcosystemFlowCompatible :
  silvesterReportsSCLDirectContract canonicalRiponIntermediaryCountermodel ≡ true
riponSCLContractAndReportedCAEcosystemFlowCompatible = refl

riponCommitteeDataFlowIsNotSignedCAContract :
  directAIQCAAgreementAuthenticated canonicalRiponIntermediaryCountermodel ≡ false
riponCommitteeDataFlowIsNotSignedCAContract = refl

riponNamedKoganOutputToAIQImportStillUnpaid :
  namedKoganOutputEqualsAIQImportProven canonicalRiponIntermediaryCountermodel ≡ false
riponNamedKoganOutputToAIQImportStillUnpaid = refl

riponDoesNotCreateAquinoTransfer2026 :
  namedRiponProvesAquinoMethodTransfer canonicalRiponIntermediaryCountermodel ≡ false
riponDoesNotCreateAquinoTransfer2026 = refl

riponDoesNotCreateBannonEpsteinMediaUse2026 :
  namedRiponProvesEpsteinMediaUse canonicalRiponIntermediaryCountermodel ≡ false
riponDoesNotCreateBannonEpsteinMediaUse2026 = refl

-- The OCDETF 2015 identifier is owned by pre-existing banking acquisition,
-- not by a new Black/NDA or secret-hierarchy duplicate owner.
chainReactionFinanceOriginalOwner : Banking.ChainReactionPromotionBoundary
chainReactionFinanceOriginalOwner = Banking.canonicalChainReactionPromotionBoundary

chainReaction2015MemoSourceIdentified :
  Banking.namedOriginalMemoIndexed chainReactionFinanceOriginalOwner ≡ true
chainReaction2015MemoSourceIdentified = refl

chainReactionInvestigationNotAdjudication :
  Banking.independentlyAdjudicatedDrugOffence chainReactionFinanceOriginalOwner ≡ false
chainReactionInvestigationNotAdjudication = refl

chainReactionStillNeedsTransactionFingerprint :
  Banking.namedBankWireMatchedToExistingLedger chainReactionFinanceOriginalOwner ≡ false
chainReactionStillNeedsTransactionFingerprint = refl

chainReactionNoBlackNDAShortcut :
  Banking.epsteinBlackNdaSameTransactionPaid chainReactionFinanceOriginalOwner ≡ false
chainReactionNoBlackNDAShortcut = refl

chainReactionNoUnifiedCaseProgramme :
  Banking.aquinoSCLOrMaxwellPROMISSharedOperationPaid chainReactionFinanceOriginalOwner ≡ false
chainReactionNoUnifiedCaseProgramme = refl


------------------------------------------------------------------------
-- CANADIAN PARLIAMENT FIRST-PERSON RIPON PIPELINE DISCRIMINATOR.
-- ETHI-113 and ETHI-117 are independently spoken accounts of two AIQ
-- principals within one institution; not two independent dataset audits.
-- PDF text from Parliament was available; screenshot request was denied,
-- so original-page image authentication is NOT claimed.
------------------------------------------------------------------------

data RiponCanadianWitness : Set where
  jeffSilvesterUnderOath : RiponCanadianWitness
  zackMassinghamUnderOath : RiponCanadianWitness

record RiponPipelineTestimony : Set where
  constructor ripon-pipeline-testimony
  field
    riponSpeaker : RiponCanadianWitness
    riponParliamentarySource : String
    riponSpeakerClaim : String
    riponSourceTranscriptIndexed : Bool
    riponOriginalPageImageVerifiedHere : Bool
    riponExactScoreDatasetOriginVerified : Bool
open RiponPipelineTestimony public

riponSilvesterCanadian113 : RiponPipelineTestimony
riponSilvesterCanadian113 = ripon-pipeline-testimony
  jeffSilvesterUnderOath
  "Canada ETHI-113 2018-06-12 PDF pp 15 and 25; https://www.ourcommons.ca/Content/Committee/421/ETHI/Evidence/EV9968993/ETHIEV113-E.PDF"
  "Silvester says AIQ wrote Ripon code to display five SCL-supplied psychographic scoring columns with entries between zero and one; says AIQ did not calculate the scores. When asked whether the source was improperly obtained Facebook information he says it may be so, but he does not know."
  true false false

riponMassinghamCanadian117 : RiponPipelineTestimony
riponMassinghamCanadian117 = ripon-pipeline-testimony
  zackMassinghamUnderOath
  "Canada ETHI-117 2018-09-27 PDF pp 2 and 10; https://www.ourcommons.ca/Content/Committee/421/ETHI/Evidence/EV10046597/ETHIEV117-E.PDF"
  "Massingham says SCL defined the score values shown in the Ripon CRM, and modelling happened in SCL's data ecosystem, not inside the display product. Distinct speaker within same company, not an independent code fingerprint."
  true false false

record RiponScoreProducerDisplayBoundary : Set where
  constructor ripon-score-producer-display-boundary
  field
    displayedScoresAdmittedByAIQWitnesses : Bool
    valuesSuppliedBySCLAccordingToWitnesses : Bool
    AIQClaimsToHaveGeneratedSourceScores : Bool
    exactKoganRFileJoinedToRiponRow : Bool
    actualFacebookInputToSpecificScoreVerified : Bool
    directCAAIQContractRequiredForDisplay : Bool
    scoringInterfaceProvesInfluenceOnElection : Bool
open RiponScoreProducerDisplayBoundary public

canonicalRiponScoreProducerDisplayBoundary : RiponScoreProducerDisplayBoundary
canonicalRiponScoreProducerDisplayBoundary =
  ripon-score-producer-display-boundary true true false false false false false

riponScoreDisplayPaidAsWitnessStatement :
  displayedScoresAdmittedByAIQWitnesses canonicalRiponScoreProducerDisplayBoundary ≡ true
riponScoreDisplayPaidAsWitnessStatement = refl

riponSCLSupplierClaimPreserved :
  valuesSuppliedBySCLAccordingToWitnesses canonicalRiponScoreProducerDisplayBoundary ≡ true
riponSCLSupplierClaimPreserved = refl

riponNoProducerAttributionWithoutDataset :
  exactKoganRFileJoinedToRiponRow canonicalRiponScoreProducerDisplayBoundary ≡ false
riponNoProducerAttributionWithoutDataset = refl

riponScoreDisplayDoesNotCertifyFacebookOrigin :
  actualFacebookInputToSpecificScoreVerified canonicalRiponScoreProducerDisplayBoundary ≡ false
riponScoreDisplayDoesNotCertifyFacebookOrigin = refl

riponScoreDisplayNoElectionOutcomeProof :
  scoringInterfaceProvesInfluenceOnElection canonicalRiponScoreProducerDisplayBoundary ≡ false
riponScoreDisplayNoElectionOutcomeProof = refl


------------------------------------------------------------------------
-- CROSS-POLLINATION 2026-10-25: THE EXISTING SOURCE-ACQUISITION,
-- EVENT-TIME, COMMON-OBJECT AND FINANCIAL SCOPE OWNERS.
-- This is source-state model checking, not an external-world theorem.
------------------------------------------------------------------------

ftcGSRSCLCommissionSource : Acquisition.SourceAcquisitionTarget
ftcGSRSCLCommissionSource = Acquisition.sourceAcquisitionTarget
  "FTC Docket 9383 Commission Opinion, 2019, PDF original"
  "Printed opinion pp 5-6: June 4 2014 GSR/SCL agreement; SCL/CA service and IP licences"
  Acquisition.directDigitalArchive Acquisition.nationalCatalogue
  true true true

ocdetfOriginalDocumentAcquisition : Acquisition.SourceAcquisitionTarget
ocdetfOriginalDocumentAcquisition = Acquisition.sourceAcquisitionTarget
  "2015-05-18 OCDETF EFTA00173953, DOJ Data Set 9"
  "69-page memorandum; third-party extraction indexed; original DOJ scan age-gated in this investigation"
  Acquisition.directDigitalArchive Acquisition.nationalCatalogue
  false false true

ftcPrimaryInspectionPaid :
  Acquisition.primaryTextInspected ftcGSRSCLCommissionSource ≡ true
ftcPrimaryInspectionPaid = refl

ocdetfOriginalPageInspectionStillUnpaid :
  Acquisition.primaryTextInspected ocdetfOriginalDocumentAcquisition ≡ false
ocdetfOriginalPageInspectionStillUnpaid = refl

-- THE SCL BOTTLENECK: contracts on the GSR/SCL/CA side are regulator-
-- established; supplying scores to AIQ is recorded as witness testimony.
-- Contractual network reachability does NOT entail exact-data identity.
record SCLTwoArmExactObjectCut : Set where
  constructor scl-two-arm-exact-object-cut
  field
    ftcGSRSCLDataScoreContract : Bool
    ftcSCLCAServicesAgreement : Bool
    ftcSCLCAIPAgreement : Bool
    silvesterSCLScoreSupplyTestimony : Bool
    massinghamSCLScoreSupplyTestimony : Bool
    riponDisplayInterfaceWitnessed : Bool
    specificGSRScoreFileEqualsRiponInput : Bool
    versionedOriginalScoreParserInCustody : Bool
    campaignDeploymentSameRowMatched : Bool
    directSignedAIQCAAgreementLocated : Bool
    historicalTechniqueTransmittedFromAquino : Bool
    epsteinBannonUsedRiponOutput : Bool
open SCLTwoArmExactObjectCut public

canonicalSCLTwoArmExactObjectCut : SCLTwoArmExactObjectCut
canonicalSCLTwoArmExactObjectCut = scl-two-arm-exact-object-cut
  true true true true true true false false false false false false

ftcGSRContractAndRiponInterfaceBothLocated :
  ftcGSRSCLDataScoreContract canonicalSCLTwoArmExactObjectCut ≡ true
ftcGSRContractAndRiponInterfaceBothLocated = refl

sharedSCLHubDoesNotProveSpecificDataset :
  specificGSRScoreFileEqualsRiponInput canonicalSCLTwoArmExactObjectCut ≡ false
sharedSCLHubDoesNotProveSpecificDataset = refl

threeDifferentFTCContractsDoNotCreateDirectAIQCAContract :
  directSignedAIQCAAgreementLocated canonicalSCLTwoArmExactObjectCut ≡ false
threeDifferentFTCContractsDoNotCreateDirectAIQCAContract = refl

sclProgrammeDoesNotProveAquinoOriginalTechnique :
  historicalTechniqueTransmittedFromAquino canonicalSCLTwoArmExactObjectCut ≡ false
sclProgrammeDoesNotProveAquinoOriginalTechnique = refl

sclProgrammeDoesNotProveBannonEpsteinReuse :
  epsteinBannonUsedRiponOutput canonicalSCLTwoArmExactObjectCut ≡ false
sclProgrammeDoesNotProveBannonEpsteinReuse = refl

-- Import existing source-appropriate *witness* from the missing-scientists
-- common-programme discriminator, without borrowing its scientist facts.
localNamedRiponWitnesses : Common.CrossPersonProgrammeReceipt
localNamedRiponWitnesses = Common.cross-person-programme-receipt
  "AIQ/SCL Ripon software development programme (local only)"
  "Jeff Silvester" "Alexander Nix"
  "Named Ripon software described by independent company witnesses; not an identical score file"
  "UK Commons 2018 Silvester Q2776-84; Nix 2018 Q3259-66"
  Common.literalCrossPerson true
  "Supports named local software programme, not native code identity, specific GSR dataset, Epstein media usage, Aquino transfer or whole-network targeting."

bannonBlackProgrammeNonJoin : Common.CrossPersonProgrammeReceipt
bannonBlackProgrammeNonJoin = Common.cross-person-programme-receipt
  "Proposed Bannon/Black/Epstein all-purpose operational command"
  "Steve Bannon" "Leon Black"
  "No common original same-object payor or technical instruction is established by separate Epstein relationships"
  "DOJ EFTA01600824 media index; existing Black invoice-wire owners, distinct objects"
  Common.thematicAdjacency false
  "One shared acquaintance/counterparty cannot pay shared film financing or common clandestine tasking."

localRiponNamesDoNotPayWholeCommand :
  Common.literalCrossPersonPaid bannonBlackProgrammeNonJoin ≡ false
localRiponNamesDoNotPayWholeCommand = refl

-- Event-time positions are read as research questions, not evidence that
-- an individual had operational access in an otherwise unrelated event.
gsrSCL2014ContractTime : EventTime.EventTimeCapabilityReceipt
gsrSCL2014ContractTime = EventTime.event-time-capability-receipt
  "GSR/SCL contracting organisations"
  "GSR personality-score subscription June 2014"
  EventTime.eventTime
  "FTC 2019 Opinion at printed p5"
  "2014 signed agreement found by FTC; 2014 Ripon row/version identity still unverified."

bannonEpstein2019ProductionTime : EventTime.EventTimeCapabilityReceipt
bannonEpstein2019ProductionTime = EventTime.event-time-capability-receipt
  "Bannon/Epstein documentary production"
  "2019 lawyer letter and dated filming correspondence"
  EventTime.eventTime
  "DOJ EFTA00809863; House Oversight 027794-027848"
  "Different later production; no event-time technical transfer from the 2014 scores established."

-- Keep the financial denominator distinctions of the mature #1131 Black
-- ledger while routing OCDETF 2015 as an investigative lead, not a wire.
blackExistingScopeReconciliation : BlackScope.ScopeReconciliation
blackExistingScopeReconciliation = BlackScope.canonicalScopeReconciliation

blackScopeDifferenceDoesNotResolveOCDETF :
  BlackScope.differenceMeansHiddenFeeByDefinition blackExistingScopeReconciliation ≡ false
blackScopeDifferenceDoesNotResolveOCDETF = refl

black2016TransactionClassificationStillOpen :
  BlackScope.year2016ClassPaid blackExistingScopeReconciliation ≡ false
black2016TransactionClassificationStillOpen = refl

-- An original 2015 lead memo, its 2026 Senate rediscovery and the Black
-- annual wire ledger are different evidence products: join requires actual
-- identical dated payer/account/recipient/wire reference and source custody.
record FinanceInvestigationJoinBoundary : Set where
  constructor finance-investigation-join-boundary
  field
    ocdetf2015LeadProductIndexed : Bool
    black2015AnnualAggregateExists : Bool
    sameOriginalWireTransactionMatched : Bool
    originalOCDETFInvestigationDispositionVerified : Bool
    memoRedactionImpliesDeliberateCoverUp : Bool
    separateBlack2015NDAAutomaticallyConnected : Bool
open FinanceInvestigationJoinBoundary public

canonicalFinanceInvestigationJoinBoundary : FinanceInvestigationJoinBoundary
canonicalFinanceInvestigationJoinBoundary =
  finance-investigation-join-boundary true true false false false false

financialEventTimeOverlapNotTransactionIdentity :
  sameOriginalWireTransactionMatched canonicalFinanceInvestigationJoinBoundary ≡ false
financialEventTimeOverlapNotTransactionIdentity = refl

unverifiedOCDETFOutcomeIsNotSuppression :
  memoRedactionImpliesDeliberateCoverUp canonicalFinanceInvestigationJoinBoundary ≡ false
unverifiedOCDETFOutcomeIsNotSuppression = refl

two2015RecordsDoNotCreateNDAJoin :
  separateBlack2015NDAAutomaticallyConnected canonicalFinanceInvestigationJoinBoundary ≡ false
two2015RecordsDoNotCreateNDAJoin = refl


------------------------------------------------------------------------
-- FTC NOVEMBER 2019 FINAL ORDER / LAWFUL CUSTODY CROSS-POLLINATION
-- The order's existence and legal requirements are source-backed; whether
-- a particular sworn compliance response was furnished or all data
-- actually destroyed is NOT established by inspecting the order itself.
------------------------------------------------------------------------

record FTCDataCustodyOrderBoundary : Set where
  constructor ftc-data-custody-order-boundary
  field
    actualFTCOrderOriginalPageInspected : Bool
    recipientDisclosureSwornStatementRequired : Bool
    derivedDataAndWorkProductDeletionRequired : Bool
    completionAffidavitRequired : Bool
    regulatoryPreservationExceptionExplicit : Bool
    complianceStatementPersonallyInspectedHere : Bool
    dataDeletionCompletedAndIndependentlyVerified : Bool
    specifiedDownstreamRiponDatasetNamedByOrder : Bool
    orderProvesUnlawfulRetentionByAThirdParty : Bool
    lawfulRedactedComplianceMetadataAcquisitionAdmissible : Bool
open FTCDataCustodyOrderBoundary public

canonicalFTCDataCustodyOrderBoundary : FTCDataCustodyOrderBoundary
canonicalFTCDataCustodyOrderBoundary = ftc-data-custody-order-boundary
  true true true true true false false false false true

ftcCustodyOrderOfficiallyLocated :
  actualFTCOrderOriginalPageInspected canonicalFTCDataCustodyOrderBoundary ≡ true
ftcCustodyOrderOfficiallyLocated = refl

ftcRequiredDeletionNotProvedCompleted :
  dataDeletionCompletedAndIndependentlyVerified canonicalFTCDataCustodyOrderBoundary ≡ false
ftcRequiredDeletionNotProvedCompleted = refl

ftcOrderDoesNotIdentifyRiponRows :
  specifiedDownstreamRiponDatasetNamedByOrder canonicalFTCDataCustodyOrderBoundary ≡ false
ftcOrderDoesNotIdentifyRiponRows = refl

ftcOrderDoesNotConvictThirdPartyPossessor :
  orderProvesUnlawfulRetentionByAThirdParty canonicalFTCDataCustodyOrderBoundary ≡ false
ftcOrderDoesNotConvictThirdPartyPossessor = refl

ftcRedactedComplianceRouteAccepted :
  lawfulRedactedComplianceMetadataAcquisitionAdmissible canonicalFTCDataCustodyOrderBoundary ≡ true
ftcRedactedComplianceRouteAccepted = refl

ftc2019OriginalOrderSource : Acquisition.SourceAcquisitionTarget
ftc2019OriginalOrderSource = Acquisition.sourceAcquisitionTarget
  "FTC Cambridge Analytica Docket 9383 Final Order issued November 25 2019"
  "Order IV.A-C and V-VI, printed pp3-4; original PDF source page4 visually inspected"
  Acquisition.directDigitalArchive Acquisition.nationalCatalogue
  true true true


------------------------------------------------------------------------
-- 2019 CANADIAN FEDERAL+BC JOINT PRIVACY REGULATOR ORIGINAL FINDINGS
--
-- Stronger than the earlier two-arm *possibility*: the 2019 regulators
-- expressly FOUND aggregate delivery/use of OCEAN scores derived in part
-- from Aleksandr Kogan's Facebook source to AIQ for US campaign work.
-- The agencies issued ONE JOINT report; this is one investigative producer,
-- not two independent forensic audits. Underlying file/row identities and
-- any individual electoral causal effects are NOT publicly authenticated.
------------------------------------------------------------------------

canadianJointAIQOriginal2019 : Acquisition.SourceAcquisitionTarget
canadianJointAIQOriginal2019 = Acquisition.sourceAcquisitionTarget
  "Canada OPC/BC OIPC, Joint Investigation of AggregateIQ, PIPEDA Findings 2019-004 and P19-03, 2019-11-26"
  "https://www.priv.gc.ca/en/opc-actions-and-decisions/investigations/investigations-into-businesses/2019/pipeda-2019-004/ ; executive summary and findings paragraphs 25-32, 62, 68-70, 94, conclusion"
  Acquisition.directDigitalArchive Acquisition.nationalCatalogue
  true true true

record Canada2019AggregateScoreFinding : Set where
  constructor canada-2019-aggregate-score-finding
  field
    originalJointRegulatorReportInspected : Bool
    canadianAndBCBodiesAreSingleJointSourceRoot : Bool
    sourceStatesAIQReceivedMillionsOfUSVoterOCEANScores : Bool
    sourceStatesScoresAtLeastPartlyDerivedFromKoganFacebookData : Bool
    investigatorsFoundAIQKnewSCLUsedKoganData : Bool
    investigatorsFoundAIQAwareOfOCEANScores : Bool
    investigatorsFoundUSCampaignConsentFailures : Bool
    investigatorsFoundInadequateSafeguardsAffectingAbout35m : Bool
    agencyRecommendationsConditionallyResolved : Bool
    agencyFollowupConfirmedImplementedHere : Bool
    rawKoganFacebookAppRecordsAtAIQIndependentlyProved : Bool
    individualKoganGSRScoreFileToNamedRiponRowMatched : Bool
    oneCampaignElectionOutcomeCausedByScores : Bool
    paidCrossNetworkEpsteinAquinoDirection : Bool
open Canada2019AggregateScoreFinding public

canonicalCanada2019AggregateScoreFinding : Canada2019AggregateScoreFinding
canonicalCanada2019AggregateScoreFinding = canada-2019-aggregate-score-finding
  true true true true true true true true true false false false false false

canadaRegulatorsPayAggregateKoganDerivedAIQScores :
  sourceStatesScoresAtLeastPartlyDerivedFromKoganFacebookData
    canonicalCanada2019AggregateScoreFinding ≡ true
canadaRegulatorsPayAggregateKoganDerivedAIQScores = refl

canadaRegulatorsPayAIQAwareness :
  investigatorsFoundAIQKnewSCLUsedKoganData
    canonicalCanada2019AggregateScoreFinding ≡ true
canadaRegulatorsPayAIQAwareness = refl

canadaJointReportNotTwoIndependentRoots :
  canadianAndBCBodiesAreSingleJointSourceRoot
    canonicalCanada2019AggregateScoreFinding ≡ true
canadaJointReportNotTwoIndependentRoots = refl

canadaKoganRawAppBytesStillNotProvenAtAIQ :
  rawKoganFacebookAppRecordsAtAIQIndependentlyProved
    canonicalCanada2019AggregateScoreFinding ≡ false
canadaKoganRawAppBytesStillNotProvenAtAIQ = refl

canadaAggregateFindingDoesNotPaySpecificRiponRow :
  individualKoganGSRScoreFileToNamedRiponRowMatched
    canonicalCanada2019AggregateScoreFinding ≡ false
canadaAggregateFindingDoesNotPaySpecificRiponRow = refl

canadaConditionalResolutionIsNotVerifiedFollowup :
  agencyFollowupConfirmedImplementedHere
    canonicalCanada2019AggregateScoreFinding ≡ false
canadaConditionalResolutionIsNotVerifiedFollowup = refl

canadaScoreFindingDoesNotPayElectionCausality :
  oneCampaignElectionOutcomeCausedByScores
    canonicalCanada2019AggregateScoreFinding ≡ false
canadaScoreFindingDoesNotPayElectionCausality = refl

canadaScoreFindingDoesNotPayEpsteinAquinoProgramme :
  paidCrossNetworkEpsteinAquinoDirection
    canonicalCanada2019AggregateScoreFinding ≡ false
canadaScoreFindingDoesNotPayEpsteinAquinoProgramme = refl

-- UPDATE TO PRIOR TWO-ARM FRONTIER WITHOUT COLLAPSING SOURCE SCOPES:
-- The aggregate model-source provenance was found by regulators in 2019.
-- The row-level GSR model/file→Ripon parser/deployment proof is STILL open.
record TwoArmCanadianPromotionCut : Set where
  constructor two-arm-canadian-promotion-cut
  field
    gsrDerivedAggregateScoresAtAIQOfficiallyFound : Bool
    aiqUsedSensitivePsychographicDataWithoutVerifiedConsent : Bool
    namedVersionFileDigestInPublicRegulatorReport : Bool
    originatingSpecificModelOutputMappedToRiponImport : Bool
    specificDeploymentOrElectoralOutcomeCausallyProved : Bool
open TwoArmCanadianPromotionCut public

canonicalTwoArmCanadianPromotionCut : TwoArmCanadianPromotionCut
canonicalTwoArmCanadianPromotionCut =
  two-arm-canadian-promotion-cut true true false false false

aggregateSourceLineageNowPaid :
  gsrDerivedAggregateScoresAtAIQOfficiallyFound canonicalTwoArmCanadianPromotionCut ≡ true
aggregateSourceLineageNowPaid = refl

regulatoryAggregateFindingDoesNotProvideOriginalRowHash :
  namedVersionFileDigestInPublicRegulatorReport canonicalTwoArmCanadianPromotionCut ≡ false
regulatoryAggregateFindingDoesNotProvideOriginalRowHash = refl

aggregateProvenanceIsNotSpecificConsumerDataIdentity :
  originatingSpecificModelOutputMappedToRiponImport canonicalTwoArmCanadianPromotionCut ≡ false
aggregateProvenanceIsNotSpecificConsumerDataIdentity = refl


------------------------------------------------------------------------
-- ORIGINAL CANADIAN §4.5 SECURITY REMEDIATION SCOPE CORRECTION
-- At Nov 26 2019 publication the regulators already had an AIQ sworn
-- deletion affidavit and regarded the *security safeguards issue* as
-- resolved. Their broader consent/remediation programme was described
-- as conditionally resolved, with later follow-up planned. The exposed
-- GitLab repository could expose keys to 35m-person databases; the
-- researcher reported NOT downloading those external databases.
------------------------------------------------------------------------

canonicalCanadianAIQCAInfluenceOwner : CA.InfluenceReceipt
canonicalCanadianAIQCAInfluenceOwner = CA.canadianJointRegulatorAIQReceipt

canadianRegulatorFindingAlsoInCanonicalCAOwner :
  CA.relationPaid canonicalCanadianAIQCAInfluenceOwner ≡ true
canadianRegulatorFindingAlsoInCanonicalCAOwner = refl

canadianSpecificTechniqueTransferNotPaidByRegulator :
  CA.techniqueTransferPaid canonicalCanadianAIQCAInfluenceOwner ≡ false
canadianSpecificTechniqueTransferNotPaidByRegulator = refl

record Canadian2019RemediationEvidenceCut : Set where
  constructor canadian-2019-remediation-evidence-cut
  field
    regulatorsFoundGitLabExposedAccessKeys : Bool
    reportedExternalDatabasesHeldAbout35mPersons : Bool
    reportSaysResearcherDeniedDownloadingThoseExternalDatabases : Bool
    securitySafeguardsIssueDeclaredResolvedIn2019Report : Bool
    sourceReportsAIQSuppliedSwornDeletionAffidavit : Bool
    swornAffidavitIndependentlyVerifiesEveryPossibleDataCopyErased : Bool
    entireConsentAndRemediationInvestigationUnconditionallyClosed : Bool
    postSixMonthImplementationFollowupIndependentlyInspected : Bool
    everyOneOf35mPeopleProvedToBeKoganDerivedScore : Bool
open Canadian2019RemediationEvidenceCut public

canonicalCanadian2019RemediationEvidenceCut : Canadian2019RemediationEvidenceCut
canonicalCanadian2019RemediationEvidenceCut = canadian-2019-remediation-evidence-cut
  true true true true true false false false false

canadian2019SecurityIssueAlreadyReportedResolved :
  securitySafeguardsIssueDeclaredResolvedIn2019Report
    canonicalCanadian2019RemediationEvidenceCut ≡ true
canadian2019SecurityIssueAlreadyReportedResolved = refl

canadian2019SwornAffidavitActuallyReported :
  sourceReportsAIQSuppliedSwornDeletionAffidavit
    canonicalCanadian2019RemediationEvidenceCut ≡ true
canadian2019SwornAffidavitActuallyReported = refl

canadianAffidavitIsNotGlobalCopyErasureCertification :
  swornAffidavitIndependentlyVerifiesEveryPossibleDataCopyErased
    canonicalCanadian2019RemediationEvidenceCut ≡ false
canadianAffidavitIsNotGlobalCopyErasureCertification = refl

canadianSecurityResolutionIsNotEntireInvestigationClosure :
  entireConsentAndRemediationInvestigationUnconditionallyClosed
    canonicalCanadian2019RemediationEvidenceCut ≡ false
canadianSecurityResolutionIsNotEntireInvestigationClosure = refl

canadian35mDatabaseVulnerabilityNot35mKoganRecords :
  everyOneOf35mPeopleProvedToBeKoganDerivedScore
    canonicalCanadian2019RemediationEvidenceCut ≡ false
canadian35mDatabaseVulnerabilityNot35mKoganRecords = refl


------------------------------------------------------------------------
-- ORIGINAL-OBJECT PARETO 2026-10-25: UK CAMPAIGN FINANCE AND DISTINCT
-- US FTC PERSONAL CONSENT ORDERS. The CA-owner receipts above are reused.
-- All "true" values describe regulator/source assertions, not an
-- independent theorem of historical truth or a conviction of a person.
------------------------------------------------------------------------

ftcKoganNixConsentCanonicalOwner : CA.InfluenceReceipt
ftcKoganNixConsentCanonicalOwner = CA.ftcKoganNixIndividualConsentReceipt

ukAIQPaymentCanonicalOwner : CA.InfluenceReceipt
ukAIQPaymentCanonicalOwner = CA.ukElectoralAiqPaymentsReceipt

record OriginalElectionRegulatorySplit : Set where
  constructor original-election-regulatory-split
  field
    ftcCompanyCambridgeAnalyticaDefaultFindingPublished : Bool
    ftcKoganIndividualFinalConsentOrderPublished : Bool
    ftcNixIndividualFinalConsentOrderPublished : Bool
    personalFTCOrdersAreAdjudicatedAdmissionOfComplaint : Bool
    ftcIndividualOrdersRequireDerivativeDataDeletion : Bool
    executedComplianceDeclarationsExaminedHere : Bool
    ukRegulatorDocumentsFiveJune2016AIQPayments : Bool
    ukVoteLeaveAppealWithdrawnAndFinesPaid : Bool
    grimes2019AppealSucceeded : Bool
    grimesOriginalSanctionRemainedInForce : Bool
    ukLeaveEUDirectCambridgeAnalyticaContractFound : Bool
    uk2016AIQInvoicesIdentifyGSRScoreFile : Bool
    sourceGivesElectionCausalEffectOfScores : Bool
    sourcePaysEpsteinAquinoCommonCommand : Bool
open OriginalElectionRegulatorySplit public

canonicalOriginalElectionRegulatorySplit : OriginalElectionRegulatorySplit
canonicalOriginalElectionRegulatorySplit =
  original-election-regulatory-split
  true true true false true false true true true false false false false false

ukElectoralAiqPaymentsExistAtRegulatorScope :
  ukRegulatorDocumentsFiveJune2016AIQPayments
    canonicalOriginalElectionRegulatorySplit ≡ true
ukElectoralAiqPaymentsExistAtRegulatorScope = refl

koganFTCConsentDoesNotAdmitComplaintAllegations :
  personalFTCOrdersAreAdjudicatedAdmissionOfComplaint
    canonicalOriginalElectionRegulatorySplit ≡ false
koganFTCConsentDoesNotAdmitComplaintAllegations = refl

grimesSanctionNotStillInForce :
  grimesOriginalSanctionRemainedInForce
    canonicalOriginalElectionRegulatorySplit ≡ false
grimesSanctionNotStillInForce = refl

campaignPaymentsDoNotIdentifyGSRInputFile :
  uk2016AIQInvoicesIdentifyGSRScoreFile
    canonicalOriginalElectionRegulatorySplit ≡ false
campaignPaymentsDoNotIdentifyGSRInputFile = refl

ukLeaveEUNoProvenDirectCAContract :
  ukLeaveEUDirectCambridgeAnalyticaContractFound
    canonicalOriginalElectionRegulatorySplit ≡ false
ukLeaveEUNoProvenDirectCAContract = refl

campaignRecordsDoNotPayCaseWideCovertCommand :
  sourcePaysEpsteinAquinoCommonCommand
    canonicalOriginalElectionRegulatorySplit ≡ false
campaignRecordsDoNotPayCaseWideCovertCommand = refl


------------------------------------------------------------------------
-- FTC v BANNON 2020 PROCEDURAL DISCRIMINATOR
-- Use exact original CA receipts, not a duplicate investigation ontology.
-- Both the FTC and Bannon supplied opposing original legal pleadings.
-- Neither petition/response/reply is a court finding of personal
-- deceptive-data liability or a bridge to his later Epstein film.
------------------------------------------------------------------------

ftc2020BannonCourtPetitionOriginalOwner : CA.InfluenceReceipt
ftc2020BannonCourtPetitionOriginalOwner = CA.ftc2020BannonCIDPetitionReceipt

ftc2020BannonOppositionOriginalOwner : CA.InfluenceReceipt
ftc2020BannonOppositionOriginalOwner = CA.ftc2020BannonRespondentOppositionReceipt

ftc2020BannonJudicialShowCauseOriginalOwner : CA.InfluenceReceipt
ftc2020BannonJudicialShowCauseOriginalOwner = CA.ftc2020BannonJudicialShowCauseReceipt

ftc2020BannonReplyOriginalOwner : CA.InfluenceReceipt
ftc2020BannonReplyOriginalOwner = CA.ftc2020BannonReplyReceipt

record BannonFTCCIDAdversarialBoundary : Set where
  constructor bannon-ftc-cid-adversarial-boundary
  field
    ftc2019DemandAnd2020PetitionIdentified : Bool
    ftcOriginalPetitionAndReplyAreSameLitigantSourceRoot : Bool
    bannonOriginalOpposingDefenceLocated : Bool
    agencyReportsDocumentsAndInterrogatories : Bool
    bannonDisputesKnowledgeOfDataMisconduct : Bool
    agencyContestedHearingNonappearance : Bool
    proceduralShowCauseOrderIndexed : Bool
    underlyingInterrogatoryAnswersActuallyInspected : Bool
    finalCivilDemandEnforcementDispositionAuthenticated : Bool
    bannonPersonallyFoundLiableForCADataScheme : Bool
    bannonDenialJudiciallyProvesInnocence : Bool
    ftcPetitionJudiciallyProvesLiability : Bool
    caInvestigationProvesEpstein2019FilmMethodReuse : Bool
    collectiveAquinoPROMISHierarchyPaid : Bool
    federalPetitionSaysCIDIssuedSeptember25 : Bool
    signedCourtOrderSaysCIDIssuedSeptember24 : Bool
    petitionAnnexExhibit2CIDIndexedAtSeptember24 : Bool
    exactOriginalCIDIssueDateReconciledWithNativeCID : Bool
open BannonFTCCIDAdversarialBoundary public

canonicalBannonFTCCIDAdversarialBoundary : BannonFTCCIDAdversarialBoundary
canonicalBannonFTCCIDAdversarialBoundary =
  bannon-ftc-cid-adversarial-boundary
  true true true true true true true false false false false false false false
  true true true false

-- Date inconsistency is preserved as a source-to-source discrepancy, NOT
-- invented as proof of two separate civil demands.
ftcBannonOriginalDateDiscrepancyRecorded :
  federalPetitionSaysCIDIssuedSeptember25 canonicalBannonFTCCIDAdversarialBoundary ≡ true
ftcBannonOriginalDateDiscrepancyRecorded = refl

ftcBannonJudicialDateDiscrepancyRecorded :
  signedCourtOrderSaysCIDIssuedSeptember24 canonicalBannonFTCCIDAdversarialBoundary ≡ true
ftcBannonJudicialDateDiscrepancyRecorded = refl

ftcBannonCIDOriginalExhibitLocated :
  petitionAnnexExhibit2CIDIndexedAtSeptember24 canonicalBannonFTCCIDAdversarialBoundary ≡ true
ftcBannonCIDOriginalExhibitLocated = refl

ftcBannonCIDOriginalIssueDateUnpaid :
  exactOriginalCIDIssueDateReconciledWithNativeCID canonicalBannonFTCCIDAdversarialBoundary ≡ false
ftcBannonCIDOriginalIssueDateUnpaid = refl

ftcBannonDirectAgencyInvestigationSourcePaid :
  ftc2019DemandAnd2020PetitionIdentified
    canonicalBannonFTCCIDAdversarialBoundary ≡ true
ftcBannonDirectAgencyInvestigationSourcePaid = refl

ftcReplyIsNotIndependentNewAgencyProducer :
  ftcOriginalPetitionAndReplyAreSameLitigantSourceRoot
    canonicalBannonFTCCIDAdversarialBoundary ≡ true
ftcReplyIsNotIndependentNewAgencyProducer = refl

bannonContraryOriginalPleadingRetained :
  bannonOriginalOpposingDefenceLocated
    canonicalBannonFTCCIDAdversarialBoundary ≡ true
bannonContraryOriginalPleadingRetained = refl

ftcBannonActualCourtSchedulingOrderPaid :
  proceduralShowCauseOrderIndexed
    canonicalBannonFTCCIDAdversarialBoundary ≡ true
ftcBannonActualCourtSchedulingOrderPaid = refl

ftcBannonCivilCIDIsNotAdjudicatedGuilt :
  bannonPersonallyFoundLiableForCADataScheme
    canonicalBannonFTCCIDAdversarialBoundary ≡ false
ftcBannonCivilCIDIsNotAdjudicatedGuilt = refl

bannonResponseNotJudicialExoneration :
  bannonDenialJudiciallyProvesInnocence
    canonicalBannonFTCCIDAdversarialBoundary ≡ false
bannonResponseNotJudicialExoneration = refl

ftcBannonCaseOutcomeStillUnverified :
  finalCivilDemandEnforcementDispositionAuthenticated
    canonicalBannonFTCCIDAdversarialBoundary ≡ false
ftcBannonCaseOutcomeStillUnverified = refl

ftcBannonCIDDoesNotPayEpsteinMediaTransfer :
  caInvestigationProvesEpstein2019FilmMethodReuse
    canonicalBannonFTCCIDAdversarialBoundary ≡ false
ftcBannonCIDDoesNotPayEpsteinMediaTransfer = refl

ftcBannonCIDDoesNotPayWholeNetworkH3 :
  collectiveAquinoPROMISHierarchyPaid
    canonicalBannonFTCCIDAdversarialBoundary ≡ false
ftcBannonCIDDoesNotPayWholeNetworkH3 = refl


------------------------------------------------------------------------
-- BANKING OWNER REUSE: ORIGINAL FEDERAL "CHAIN REACTION" NAME COLLISION
-- Reuse the specific already-owned DEA/HSI attribution discriminator.
-- No imported HSI counterfeit action may automatically pay a DEA
-- narcotics outcome or 2015 Black/Epstein same-transaction identity.
------------------------------------------------------------------------

canonicalFederalChainReactionHomonymOwner : Banking.ChainReactionFederalNameCollisionCut
canonicalFederalChainReactionHomonymOwner =
  Banking.canonicalChainReactionFederalNameCollisionCut

chainReactionOriginalNameCollisionNotOneOperation :
  Banking.sameNameMeansSameInvestigation
    canonicalFederalChainReactionHomonymOwner ≡ false
chainReactionOriginalNameCollisionNotOneOperation = refl

hsiCounterfeitProceedingsNotEpsteinDrugDisposition :
  Banking.hsiCounterfeitCasesAreDEADrugOffenceDispositions
    canonicalFederalChainReactionHomonymOwner ≡ false
hsiCounterfeitProceedingsNotEpsteinDrugDisposition = refl

reported2023DEAClosureStillNeedsOriginalInstrument :
  Banking.reportedJune2023DEAClosureHasSignedNativeInstrumentHere
    canonicalFederalChainReactionHomonymOwner ≡ false
reported2023DEAClosureStillNeedsOriginalInstrument = refl


------------------------------------------------------------------------
-- 26 OCT: PROOF-RELEVANT NAME COLLISION CROSS-POLLINATION, REUSE-ONLY
-- Existing nonfactorability module owns the theorem. The banking owner
-- supplies this exact finite input carrier. Neither is a new historical
-- source; agency-case identities still need independent source custody.
------------------------------------------------------------------------

caseTitleAloneCannotRecoverFederalCase :
  Banking.casePublicHeadline Banking.deaOCDETFNYNYS0829 ≡
  Banking.casePublicHeadline Banking.hsiIPRCounterfeit2011
caseTitleAloneCannotRecoverFederalCase = refl

bankingNameOnlyCaseDecoderNoGo :
  NonFactor.FactorsThrough Banking.casePublicHeadline Banking.caseIsDEA → ⊥
bankingNameOnlyCaseDecoderNoGo = Banking.nameOnlyFederalCaseIdentityImpossible

bankingAgencyCaseKeyRestoresFiniteConsumer :
  NonFactor.FactorsThrough Banking.originalFederalCaseKey Banking.caseIsDEA
bankingAgencyCaseKeyRestoresFiniteConsumer = Banking.originalCaseKeyConsumerFactors


------------------------------------------------------------------------
-- AUSPOL EXPANSION: THIN CASE CONSUMER, NO IMPORT OF #1251 SIBLING.
-- Source: existing Rinehart/Hanson/QLD/Palmer/Mandelson/Australia owners,
-- official indexed Senate disclosure and published NSWSC document.
------------------------------------------------------------------------

canonicalAuspolSameObjectOwner : Auspol.AustralianPowerPipelineFrontier
canonicalAuspolSameObjectOwner = Auspol.canonicalAustralianPowerPipelineFrontier

auspolMaterialSupportActuallyPaidAtReportedScope :
  Auspol.materialSupportAndFirstPersonPolicyAdvicePresent
    canonicalAuspolSameObjectOwner ≡ true
auspolMaterialSupportActuallyPaidAtReportedScope = refl

auspolSpecificIPAEditorialOrderNotPaid :
  Auspol.specificIPAContentBoughtByCourtReportedPayments
    canonicalAuspolSameObjectOwner ≡ false
auspolSpecificIPAEditorialOrderNotPaid = refl

auspolRinehartEpsteinDirectEdgeNotPaid :
  Auspol.directRinehartEpsteinRelationProven
    canonicalAuspolSameObjectOwner ≡ false
auspolRinehartEpsteinDirectEdgeNotPaid = refl

auspolKoganUKUSScoresNotAssumedAustralianDeployment :
  Auspol.AustralianCampaignUsedKoganRiponScoresProven
    canonicalAuspolSameObjectOwner ≡ false
auspolKoganUKUSScoresNotAssumedAustralianDeployment = refl

auspolNoCommonGlobalCommand :
  Auspol.wholeAustraliaUSCovertCommandProven
    canonicalAuspolSameObjectOwner ≡ false
auspolNoCommonGlobalCommand = refl
