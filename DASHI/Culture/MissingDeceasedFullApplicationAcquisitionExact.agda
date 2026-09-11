module DASHI.Culture.MissingDeceasedFullApplicationAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.ChavezApplicationTransformationPossessionExact as Chavez
import DASHI.Culture.LeBlancApplicationTransformationPossessionExact as LeBlanc
import DASHI.Culture.RezaApplicationTransformationPossessionExact as Reza

------------------------------------------------------------------------
-- FULL APPLICATION-TRANSFORMATION ACQUISITION COMPILER
--
-- One parallel cohort surface.  Every retained person has an independent
-- evidence frontier; acquisition may proceed concurrently and out of dependency
-- order, while conclusion/payment may not skip identity, event-time, same-object,
-- provenance or relationship leaves.
--
-- Priority is discriminating value of the next missing application/event leaf,
-- never a probability of targeting, murder, common causation or wrongdoing.
------------------------------------------------------------------------

data AcquisitionPriority : Set where
  priorityHighest : AcquisitionPriority
  priorityHigh : AcquisitionPriority
  priorityMedium : AcquisitionPriority
  priorityControl : AcquisitionPriority

record ApplicationAcquisitionTarget : Set where
  constructor application-acquisition-target
  field
    person : String
    priority : AcquisitionPriority
    applicationCarrier : String
    requestedEvidence : String
    promotes : String
    doesNotPromote : String

open ApplicationAcquisitionTarget public

amyEskridgeAcquisition : ApplicationAcquisitionTarget
amyEskridgeAcquisition = application-acquisition-target
  "Amy Eskridge" priorityHighest
  "NASA-review / POAMS release object plus Institute-derived anomalous-force application stack"
  "recover the POAMS-specific Marshall EDAA/NF-1676B record and associated STI version; same-object crosswalk to M-1531/NTRS 20205010911; Amy-linked review/release correspondence; exact Institute derivative object; apparatus/data/notebook/repository custody; successor/handover"
  "exact review-object identity, derivative identity, reconstructive application depth and post-death same-carrier continuity"
  "Amy authorship of M-1531, physical validity of anomalous-force claims, targeting, homicide, actor identity or motive"

anthonyChavezAcquisition : ApplicationAcquisitionTarget
anthonyChavezAcquisition = application-acquisition-target
  "Anthony Chavez, missing Los Alamos resident born 1947-01-07" priorityHigh
  "candidate DARHT/Scorpius application-engineering carrier"
  "first recover a same-person identity receipt connecting the missing Anthony Chavez to the LANL Summer-2025 Anthony Chavez engineering profile and/or Mark Anthony Chavez publication identity; only then recover exact Scorpius/DARHT assignments, calibration/configuration ownership, successor/handover and rework"
  "same-person event-time application capability and downstream responsibility-transfer/replacement effects"
  "technical authorship or Scorpius possession from name/institution/topic similarity; disappearance causation or targeting"

chavezFirstReverseTarget : Chavez.ChavezApplicationReverseTarget
chavezFirstReverseTarget = Chavez.acquireSamePersonIdentityReceipt

joshuaLeBlancAcquisition : ApplicationAcquisitionTarget
joshuaLeBlancAcquisition = application-acquisition-target
  "Joshua Kyle LeBlanc" priorityHigh
  "NASA SNP/FSP instrumentation-and-controls technology-maturation work"
  "recover the internal freeze/authorship date of the August-2025 recognition carrier; first exact post-loss SNP I&C TechMat roster; dated TechMat work breakdown; qualification/failure/calibration ownership; successor/handover and any same-carrier requalification or rework"
  "person-specific responsibility and local transfer/replacement effects within the distributed FSP I&C structure"
  "sole ownership, programme paralysis, successor identity from broader FSP continuity, targeting or death causation"

leblancResponsibilityTransferTarget : LeBlanc.LeBlancApplicationReverseTarget
leblancResponsibilityTransferTarget = LeBlanc.acquireExactPostLossTechMatRoleRoster

monicaRezaAcquisition : ApplicationAcquisitionTarget
monicaRezaAcquisition = application-acquisition-target
  "Monica Jacinto Reza / Monica Andrea Jacinto / Monica A. Jacinto" priorityHigh
  "event-time JPL materials-processing role plus Mondaloy / advanced nickel-alloy process-window carrier"
  "recover a primary JPL/Caltech personnel or organisation carrier for the event-time Materials Processing role; then heat-treatment/microstructure/process-window ownership, qualification/failure history, manufacturing handover, successor and requalification"
  "event-time institutional role followed by same-object process possession and transfer difficulty"
  "JPL directorship from repeated downstream reporting alone; sole ownership from co-inventorship; targeting or disappearance causation"

rezaResponsibilityTransferTarget : Reza.RezaApplicationReverseTarget
rezaResponsibilityTransferTarget = Reza.acquirePrimaryJPLEventTimeRoleRecord

frankMaiwaldAcquisition : ApplicationAcquisitionTarget
frankMaiwaldAcquisition = application-acquisition-target
  "Frank W. Maiwald" priorityHigh
  "action-spectroscopy experiment/data/calibration carrier and JPL project succession"
  "crosswalk the experimental spectra already visible in the 2023 JPL poster to exact raw/reduced datasets, calculations, figure versions, ChemRxiv/NTRS/ACS manifestations, apparatus/calibration state, named custodian/successor and post-loss changes"
  "which scientific/application carrier pre-existed loss and which later versions were continued, revised or newly produced"
  "final 2025 dataset identity merely from the 2023 spectra; calibration/tacit transfer from publication continuation; targeting or death causation"

williamMcCaslandAcquisition : ApplicationAcquisitionTarget
williamMcCaslandAcquisition = application-acquisition-target
  "William Neil McCasland" priorityHigh
  "2025-2026 work-mode/client/programme carrier"
  "date and validate DBE Consulting LLC corporate role/status; identify 2025-2026 employer/client/project responsibility; then configuration/integration role, access, technical-decision records, handover/successor and observer surfaces"
  "event-time work mode and a same-object application capability proposition instead of broad career adjacency"
  "current technical programme from stale ATA prose, UAP belief, restricted-technology possession, targeting or disappearance causation"

nunoLoureiroAcquisition : ApplicationAcquisitionTarget
nunoLoureiroAcquisition = application-acquisition-target
  "Nuno F. G. Loureiro" priorityHigh
  "student/grant/repository/simulation-state continuation below PSFC-center succession"
  "recover student/advisor reassignment, grant/PI reassignment, Viriato/KREHM repository ownership and commit history, exact target-regime configurations, validation notebooks and named same-carrier handover"
  "scientific-carrier succession distinct from already-paid center leadership and pedagogical continuation"
  "same-carrier handover from Steve Wukitch becoming interim PSFC director or from public memorial teaching continuity"

michaelHicksAcquisition : ApplicationAcquisitionTarget
michaelHicksAcquisition = application-acquisition-target
  "Michael David Hicks" priorityControl
  "historical JPL small-body science workflow, with JPL departure preceding death"
  "recover the exact 2022 JPL departure/retirement state and any unfinished mission/data obligations; identify whether DART/NEAT/small-body workflows had already been transferred before his 2023 death; retain continuation only as a control"
  "whether technical responsibility had already been transferred before death, providing a negative control for death-disruption claims"
  "event-time JPL programme possession after the independently reported 2022 departure; foul play or common targeting from planetary-defence adjacency"

carlGrillmairAcquisition : ApplicationAcquisitionTarget
carlGrillmairAcquisition = application-acquisition-target
  "Carl J. Grillmair" priorityControl
  "stellar-stream/exoplanet scientific workflow and three manuscripts reported in preparation"
  "recover same-work/manuscript continuation only as a control; preserve the LA County DA's charged local-crime sequence and the IPAC record of three papers in preparation as separate evidence fibres"
  "a strong ordinary-event / continuity control capable of weakening a unified work-targeting hypothesis"
  "conviction from charges; scientific motive for the homicide; technical causation from the existence of unfinished papers"

jasonThomasAcquisition : ApplicationAcquisitionTarget
jasonThomasAcquisition = application-acquisition-target
  "Jason R. Thomas" priorityControl
  "Novartis chemical-biology assay / target-deconvolution workflow"
  "recover official cause/manner and recovery record where available, plus same-workflow/team continuation as a public-science control"
  "a control separating deep technical work from event causation and testing whether application knowledge was distributed"
  "foul play, common targeting or programme motive from research depth alone"

melissaCasiasAcquisition : ApplicationAcquisitionTarget
melissaCasiasAcquisition = application-acquisition-target
  "Melissa Casias" priorityControl
  "administrative LANL role plus event-forensic carrier"
  "obtain the primary New Mexico OMI autopsy/toxicology and law-enforcement records; current reporting says cause was gunshot wound to the head while manner remained undetermined; preserve exact role/custody evidence separately"
  "event chronology and bounded forensic state, including uncertainty between possible manners of death"
  "scientist status from LANL affiliation; homicide or suicide from an undetermined manner; common targeting from workplace alone"

stevenGarciaAcquisition : ApplicationAcquisitionTarget
stevenGarciaAcquisition = application-acquisition-target
  "Steven Garcia" priorityMedium
  "KCNSC property/asset-custody role plus missing-person event carrier"
  "recover primary APD/NamUs missing-person record, exact employer/contractor identity, property-custodian scope, asset/accountability responsibility and any handover after disappearance"
  "event-time custody responsibility and whether any operational asset-control function required reassignment"
  "scientific research, nuclear-secret access, clearance scope or targeting from the property-custodian label alone"

matthewSullivanAcquisition : ApplicationAcquisitionTarget
matthewSullivanAcquisition = application-acquisition-target
  "Matthew Sullivan" priorityControl
  "former USAF intelligence role and 2024 death-event carrier"
  "recover primary service identity, official death/cause/manner record and any independently documented event-time programme or testimony obligation before considering later crash-retrieval/UAP reporting"
  "identity, event chronology and—only if independently paid—event-time programme relationship"
  "scientific-work status, crash-retrieval possession, congressional-testimony plan or targeting from secondary anonymous-source reporting"

record FullAcquisitionBoundary : Set where
  constructor full-acquisition-boundary
  field
    amyIncludedOutsideHouseDenominator : Bool
    amyIncludedOutsideHouseDenominatorIsTrue : amyIncludedOutsideHouseDenominator ≡ true
    priorityIsNotCausalProbability : Bool
    priorityIsNotCausalProbabilityIsTrue : priorityIsNotCausalProbability ≡ true
    controlsCanWeakenCommonTargetingHypothesis : Bool
    controlsCanWeakenCommonTargetingHypothesisIsTrue : controlsCanWeakenCommonTargetingHypothesis ≡ true
    sameCarrierEvidenceRequiredBeforeCriticality : Bool
    sameCarrierEvidenceRequiredBeforeCriticalityIsTrue : sameCarrierEvidenceRequiredBeforeCriticality ≡ true
    entireRetainedCohortHasAcquisitionRow : Bool
    entireRetainedCohortHasAcquisitionRowIsTrue : entireRetainedCohortHasAcquisitionRow ≡ true
    acquisitionMayProceedInParallel : Bool
    acquisitionMayProceedInParallelIsTrue : acquisitionMayProceedInParallel ≡ true
    paymentMaySkipUnpaidDependency : Bool
    paymentMaySkipUnpaidDependencyIsFalse : paymentMaySkipUnpaidDependency ≡ false

canonicalFullAcquisitionBoundary : FullAcquisitionBoundary
canonicalFullAcquisitionBoundary = full-acquisition-boundary
  true refl true refl true refl true refl true refl true refl false refl
