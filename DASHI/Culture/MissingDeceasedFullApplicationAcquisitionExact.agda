module DASHI.Culture.MissingDeceasedFullApplicationAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.ChavezApplicationTransformationPossessionExact as Chavez
import DASHI.Culture.LeBlancApplicationTransformationPossessionExact as LeBlanc
import DASHI.Culture.RezaApplicationTransformationPossessionExact as Reza

------------------------------------------------------------------------
-- FULL APPLICATION-TRANSFORMATION ACQUISITION COMPILER
--
-- Converts the memorial atlas into exact evidence leaves. Priorities reflect
-- current discriminating value of the missing application transformation, not
-- a probability of targeting, murder, or common causation.
--
-- The compiler consumes person-specific reverse targets where they already
-- exist.  It must not silently drop a roster member merely because the detailed
-- possession owner lives elsewhere in the aggregate.
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
  "Institute-derived anomalous-force experimental application stack"
  "recover the exact Institute derivative object; apparatus drawings/photos/BOM; calibration procedure; raw and reduced data; null/failure runs; analysis code/notebooks; validation protocol; NASA review correspondence; handover/successor records"
  "identity and reconstructive depth of the application transformation, plus whether it persisted after her death"
  "physical validity of anomalous-force claims, targeting, homicide, actor identity or motive"

------------------------------------------------------------------------
-- Restored Tier-2 rows.  These already had detailed possession/reverse-target
-- owners but were missing from this nominally full compiler.
------------------------------------------------------------------------

anthonyChavezAcquisition : ApplicationAcquisitionTarget
anthonyChavezAcquisition = application-acquisition-target
  "Anthony Chavez, missing Los Alamos resident born 1947-01-07" priorityHigh
  "candidate DARHT/Scorpius application-engineering carrier"
  "first recover the same-person identity receipt connecting the missing Anthony Chavez to any LANL technical identity; only then recover exact Scorpius design assignments, diagnostic calibration ownership, configuration-management history, successor/handover, inverse-model role and replacement delay/rework"
  "same-person event-time application capability and, downstream, local responsibility-transfer/replacement difficulty"
  "Mark Anthony Chavez technical capability by name similarity; disappearance causation, targeting or actor identity"

chavezFirstReverseTarget : Chavez.ChavezApplicationReverseTarget
chavezFirstReverseTarget = Chavez.acquireSamePersonIdentityReceipt

joshuaLeBlancAcquisition : ApplicationAcquisitionTarget
joshuaLeBlancAcquisition = application-acquisition-target
  "Joshua Kyle LeBlanc" priorityHigh
  "NASA SNP/FSP instrumentation-and-controls technology-maturation work"
  "recover the TechMat work breakdown and dated task ownership; qualification-test, failure-envelope and calibration-drift ownership; then identify the post-loss successor/handover and any requalification delay or rework on the same I&C carrier"
  "person-specific responsibility and local transfer/replacement effects within the already-distributed FSP I&C structure"
  "sole ownership of FSP I&C, programme paralysis, targeting or death causation"

leblancResponsibilityTransferTarget : LeBlanc.LeBlancApplicationReverseTarget
leblancResponsibilityTransferTarget = LeBlanc.acquireSuccessorOrHandover

monicaRezaAcquisition : ApplicationAcquisitionTarget
monicaRezaAcquisition = application-acquisition-target
  "Monica Jacinto Reza / Monica A. Jacinto" priorityHigh
  "Mondaloy / advanced nickel-alloy process-window and materials-processing application stack"
  "recover primary event-time JPL Materials Processing role evidence; heat-treatment development records, microstructure acceptance window, process tolerance/failure history, engine-qualification ownership, manufacturing handover, successor role and any requalification after departure"
  "same-object process-window possession, tacit manufacturing concentration and responsibility-transfer/replacement difficulty"
  "sole ownership from co-inventorship, complete manufacturing capability from the patent, targeting or disappearance causation"

rezaResponsibilityTransferTarget : Reza.RezaApplicationReverseTarget
rezaResponsibilityTransferTarget = Reza.acquireSuccessorRole

frankMaiwaldAcquisition : ApplicationAcquisitionTarget
frankMaiwaldAcquisition = application-acquisition-target
  "Frank W. Maiwald" priorityHigh
  "instrument calibration / qualification / integration state"
  "recover JPL task assignments, calibration databases, qualification procedures, acceptance/rejection history, AMR-C/SBG-VSWIR process records, action-spectroscopy apparatus transfer notes, named successor and post-departure requalification effort"
  "same-carrier possession, distribution and replacement difficulty"
  "dual-use motive, targeting or death causation"

williamMcCaslandAcquisition : ApplicationAcquisitionTarget
williamMcCaslandAcquisition = application-acquisition-target
  "William Neil McCasland" priorityHigh
  "one event-time operational technology/programme transformation"
  "identify a specific 2025-2026 application object or programme under his responsibility; recover configuration/integration role, access, technical-decision records, handover/successor and observer surfaces"
  "a same-object application-capability proposition instead of broad career adjacency"
  "UAP belief, restricted-technology possession, targeting or disappearance causation merely from prior roles"

nunoLoureiroAcquisition : ApplicationAcquisitionTarget
nunoLoureiroAcquisition = application-acquisition-target
  "Nuno F. G. Loureiro" priorityMedium
  "target-specific reduced-kinetic plasma configuration and validation workflow"
  "recover source repository/artifact history, exact closure/dissipation and resolution settings, unpublished target-regime configurations, validation notebooks, group handover, successor ownership and post-death continuation of the same artifacts"
  "whether a materially reconstructive application residual existed beyond public equations/methods"
  "criticality, targeting or causal linkage from mathematical sophistication alone"

michaelHicksAcquisition : ApplicationAcquisitionTarget
michaelHicksAcquisition = application-acquisition-target
  "Michael David Hicks" priorityMedium
  "mission-specific small-body calibration/data-reduction/inference workflow"
  "recover DART/NEAT/other event-time pipeline assignments, calibration/configuration ownership, successor/handover, data products and whether work continued without reconstruction cost"
  "replacement/disruption assessment for a specific application carrier"
  "foul play or common targeting from planetary-defence adjacency"

carlGrillmairAcquisition : ApplicationAcquisitionTarget
carlGrillmairAcquisition = application-acquisition-target
  "Carl J. Grillmair" priorityControl
  "survey QA / matched-filter / NEO Surveyor validation workflow"
  "recover same-carrier succession and continuity only as a control for how deep application capability is distributed after loss"
  "a matched disruption-control profile"
  "scientific motive for the homicide; public evidence presently supports a charged local-crime sequence instead"

jasonThomasAcquisition : ApplicationAcquisitionTarget
jasonThomasAcquisition = application-acquisition-target
  "Jason R. Thomas" priorityControl
  "assay / target-deconvolution / chemical-biology workflow"
  "recover same-workflow continuation, team distribution and successor only as a public-science/application control"
  "a matched control for technically deep but distributed/public application science"
  "foul play or common targeting; public recovery reporting said no foul play was suspected"

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
    chavezLeBlancRezaIncludedInFullCompiler : Bool
    chavezLeBlancRezaIncludedInFullCompilerIsTrue : chavezLeBlancRezaIncludedInFullCompiler ≡ true

canonicalFullAcquisitionBoundary : FullAcquisitionBoundary
canonicalFullAcquisitionBoundary = full-acquisition-boundary
  true refl true refl true refl true refl true refl
