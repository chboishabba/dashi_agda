module DASHI.Law.SensibLawWoogarooPopulationConnectivityAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Ibrahim
import DASHI.Law.SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact as S102
import DASHI.Law.SensibLawWoogarooS13EssentialityStressTestExact as S13
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooKoalaScienceSnowballExact as Science

------------------------------------------------------------------------
-- WOOGAROO POPULATION / CONNECTIVITY ACQUISITION LEAVES
--
-- Consumer-first Snowball over the live s 102 and s 13 residuals.  General
-- literature, QIDs, DOIs and Dewey coordinates navigate the search space; they
-- do not substitute for same-object local evidence.
------------------------------------------------------------------------

data AcquisitionLeaf : Set where
  currentIndependentEcologicalOpinion : AcquisitionLeaf
  localPopulationIdentity : AcquisitionLeaf
  localFunctionalConnectivityEvidence : AcquisitionLeaf
  currentHabitatCondition : AcquisitionLeaf
  currentMovementRisk : AcquisitionLeaf
  mitigationEffectivenessEvidence : AcquisitionLeaf
  withoutSiteCounterfactual : AcquisitionLeaf
  executionChronology : AcquisitionLeaf

data LeafState : Set where
  methodPaid : LeafState
  regionalContextPaid : LeafState
  sameObjectOpen : LeafState
  conditional : LeafState

record AcquisitionLeafReceipt : Set where
  constructor acquisition-leaf-receipt
  field
    leaf : AcquisitionLeaf
    state : LeafState
    legalConsumer : String
    existingSupport : String
    sameObjectNeeded : String
    bestAcquisition : String
    whyHigherAlphaThanMoreLiterature : String

open AcquisitionLeafReceipt public

s102ExpertOpinionLeaf : AcquisitionLeafReceipt
s102ExpertOpinionLeaf = acquisition-leaf-receipt
  currentIndependentEcologicalOpinion
  sameObjectOpen
  "Nature Conservation Act ss 12, 102-103: likely significant detrimental effect"
  "The statute, Queensland Koala status, same-project SHG ecology, approved 9281 clearing/earthworks process and current connectivity/fragmentation science are already source-paid."
  "An independent current ecological opinion applying the actual Queensland statutory wording to the approved/current project state, including mitigation and uncertainty."
  "Commission or obtain a short expert memorandum that identifies the qualifying wildlife/habitat, causal pathway, likely magnitude/duration/reversibility, fragmentation/connectivity effect, mitigation effectiveness and material data limitations."
  "The missing proposition is a current same-object expert application, not another general mechanism paper."

s13PopulationLeaf : AcquisitionLeafReceipt
s13PopulationLeaf = acquisition-leaf-receipt
  localPopulationIdentity
  sameObjectOpen
  "Nature Conservation Act s 13: habitat essential to conservation of a viable protected-wildlife population/community"
  "McLennan et al. supplies regional genomic structure context; the national recovery plan and connectivity literature supply population/connectivity methodology."
  "A defensible identification of the biologically relevant Koala population/community connected to Springview/Woogaroo, independent of the development boundary."
  "Locate local/regional telemetry, genetics, mark-recapture, health/clinical, density or government monitoring data that can delimit the relevant population and its connection to the site."
  "Regional SEQ/N-NSW genomics does not identify the Springview population; another regional paper would not close that identity join."

functionalConnectivityLeaf : AcquisitionLeafReceipt
functionalConnectivityLeaf = acquisition-leaf-receipt
  localFunctionalConnectivityEvidence
  sameObjectOpen
  "s 102 causal effect and s 13 essentiality/substitutability"
  "Brunton et al. 2026 shows that koala connectivity mapping often lacks realised functional connectivity and local validation; SHG supplies a structural >500 ha connectivity surface."
  "Evidence that Koalas actually move through, depend on, or are functionally connected by the Opossum/Woogaroo/Springview landscape."
  "Prioritise GPS/telemetry, genetic connectivity, repeated field detections, validated local occurrence, road-crossing/mortality and expert interpretation before treating desktop corridor maps as realised connectivity."
  "The state-of-the-art review says map availability can create false confidence where local validation is missing."

currentHabitatLeaf : AcquisitionLeafReceipt
currentHabitatLeaf = acquisition-leaf-receipt
  currentHabitatCondition
  sameObjectOpen
  "s 102 likely effect; s 13 current essentiality; EPBC final-state comparison"
  "2019 project ecology strongly pays historical habitat function and condition."
  "Current 2026 condition of the retained/affected habitat, including material degradation, clearing, regrowth or increased scarcity since 2019."
  "Use current imagery/field ecology and later LiDAR/SLATS where useful, keeping historical and current states distinct."
  "The live consumers concern current/future effect; repeating the 2019 baseline does not pay temporal persistence."

movementRiskLeaf : AcquisitionLeafReceipt
movementRiskLeaf = acquisition-leaf-receipt
  currentMovementRisk
  regionalContextPaid
  "s 102 indirect/cumulative detrimental-effect pathway; s 13 without-site counterfactual"
  "Dexter et al. 2024 and Tacla et al. 2025 provide SEQ urban movement/vehicle-risk mechanisms."
  "Local roads, crossings, mortality/near-miss records and movement pathways that would plausibly change if the approved habitat is cleared or severed."
  "Acquire local rescue/strike records, road geometry, barriers/crossings and any telemetry/field evidence; distinguish historic hotspots from current population persistence."
  "Regional mechanism is paid; magnitude at Springview is not."

mitigationLeaf : AcquisitionLeafReceipt
mitigationLeaf = acquisition-leaf-receipt
  mitigationEffectivenessEvidence
  sameObjectOpen
  "s 102 likely effect after mitigation; s 13 substitutability"
  "Approval conditions and SHG mitigation proposals are source-paid; Frere et al. and connectivity literature supply methods for testing realised movement/gene-flow effectiveness."
  "Evidence that the actual retained strips, crossings, fauna controls, rehabilitation and other mitigation maintain the ecological function relied on."
  "Ask for design/performance criteria, monitoring results, post-construction data where available, and expert evidence on whether proposed measures maintain current function through the relevant time horizon."
  "Mitigation existence is not mitigation effectiveness."

counterfactualLeaf : AcquisitionLeafReceipt
counterfactualLeaf = acquisition-leaf-receipt
  withoutSiteCounterfactual
  sameObjectOpen
  "s 13 essentiality core; also informs s 102 seriousness"
  "Site function, fragmentation mechanism and regional population/connectivity context are paid as separate inputs."
  "A quantified or at least explicit ecological counterfactual comparing persistence, movement, breeding/dispersal and resource access with versus without the Springview/Woogaroo habitat."
  "Have the expert compare current function with removal/severance, test nearby-habitat substitutability now, and state uncertainty and time lag for restoration/offset alternatives."
  "Essentiality is a counterfactual relation, not a synonym for occupancy, high habitat score or mapped connectivity."

executionLeaf : AcquisitionLeafReceipt
executionLeaf = acquisition-leaf-receipt
  executionChronology
  sameObjectOpen
  "s 102 urgency / timing and any compliance-enforcement route"
  "A12705838 and the negotiated decision pay approved geometry and conditions."
  "Condition 6(a) satisfaction, prestart, current fauna/arborist records and commencement/clearing chronology joined to the exact approval."
  "Obtain Council compliance/prestart records and dated site evidence."
  "Approval authorisation does not establish execution or imminence."

------------------------------------------------------------------------
-- Legal-atom bindings: these leaves are required evidence tasks, not newly
-- satisfied atoms.
------------------------------------------------------------------------

record LeafAtomBinding : Set where
  constructor leaf-atom-binding
  field
    leaf : AcquisitionLeaf
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    methodOrContextAvailable : Bool
    sameObjectPaymentComplete : Bool
    note : String

open LeafAtomBinding public

expertToS102Effect : LeafAtomBinding
expertToS102Effect = leaf-atom-binding
  currentIndependentEcologicalOpinion
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  true false
  "Method, law and supporting facts are available; the independent same-object expert application remains open."

populationToS13 : LeafAtomBinding
populationToS13 = leaf-atom-binding
  localPopulationIdentity
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  true false
  "Regional population-genomic context is available; exact local population identity remains open."

connectivityToS13 : LeafAtomBinding
connectivityToS13 = leaf-atom-binding
  localFunctionalConnectivityEvidence
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  true false
  "Structural connectivity is paid; realised local functional connectivity remains open."

counterfactualToS13 : LeafAtomBinding
counterfactualToS13 = leaf-atom-binding
  withoutSiteCounterfactual
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  true false
  "This is the final ecological bridge from population+function to statutory essentiality; it is not yet paid."

executionToS102 : LeafAtomBinding
executionToS102 = leaf-atom-binding
  executionChronology
  Atom.worksCommencementTimingAtom
  Atom.nca102InterimOrderConsumer
  true false
  "Approval and conditions are paid; current commencement/urgency state remains open."

------------------------------------------------------------------------
-- Reuse the indexed science / legal states rather than recounting them.
------------------------------------------------------------------------

s102CaseState : S102.S102CaseState
s102CaseState = S102.currentS102CaseState

s13StressTest : S13.S13StressTest
s13StressTest = S13.currentS13StressTest

ibrahimCoverage : Ibrahim.WoogarooIbrahimCoverage
ibrahimCoverage = Ibrahim.currentWoogarooIbrahimCoverage

scienceState : Science.ConsumerScienceState
scienceState = Science.currentConsumerScienceState

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data StructuralConnectivityEqualsFunctionalConnectivity : Set where
data RegionalGenomicClusterEqualsLocalViablePopulation : Set where
data OccurrencePointEqualsPopulationIdentity : Set where
data MitigationPlanEqualsMitigationPerformance : Set where
data MorePapersEqualsSameObjectPayment : Set where
data HistoricalEcologyEqualsCurrentCondition : Set where

data ExpertOpinionEqualsMinisterialOpinion : Set where

structuralMapDoesNotBecomeFunctionalConnectivity : StructuralConnectivityEqualsFunctionalConnectivity → ⊥
structuralMapDoesNotBecomeFunctionalConnectivity ()

regionalClusterDoesNotBecomeLocalPopulation : RegionalGenomicClusterEqualsLocalViablePopulation → ⊥
regionalClusterDoesNotBecomeLocalPopulation ()

occurrenceDoesNotIdentifyPopulation : OccurrencePointEqualsPopulationIdentity → ⊥
occurrenceDoesNotIdentifyPopulation ()

mitigationPlanDoesNotProvePerformance : MitigationPlanEqualsMitigationPerformance → ⊥
mitigationPlanDoesNotProvePerformance ()

morePapersDoNotPaySameObject : MorePapersEqualsSameObjectPayment → ⊥
morePapersDoNotPaySameObject ()

historicalEcologyDoesNotBecomeCurrentCondition : HistoricalEcologyEqualsCurrentCondition → ⊥
historicalEcologyDoesNotBecomeCurrentCondition ()

expertDoesNotBecomeMinister : ExpertOpinionEqualsMinisterialOpinion → ⊥
expertDoesNotBecomeMinister ()
