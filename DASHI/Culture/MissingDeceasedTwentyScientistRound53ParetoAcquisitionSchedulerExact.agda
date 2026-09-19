module DASHI.Culture.MissingDeceasedTwentyScientistRound53ParetoAcquisitionSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.MissingDeceasedTwentyScientistRound52TwentyPersonOperationalFrontierExact as R52
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Core.BoundAcquisitionDemandExact as Bound

------------------------------------------------------------------------
-- ROUND 53: PARETO ACQUISITION SCHEDULER
--
-- Pareto is the scheduler over live residuals, not a narrative ranker.
-- Hard gates decide which tasks are admissible/currently decision-relevant.
-- Only then do declared cost axes compare surviving tasks.  No weighted sum,
-- hidden scalar utility, newsworthiness score, strategic-importance score or
-- truth score is introduced.
------------------------------------------------------------------------

data AcquisitionTask : Set where
  rezaMcCaslandTask : AcquisitionTask
  ningPrimaryBytesTask : AcquisitionTask
  amyReferentWeldTask : AcquisitionTask
  chavezScorpiusCrossingTask : AcquisitionTask
  leblancSubordinateWBSTask : AcquisitionTask
  chineseClusterOriginTask : AcquisitionTask
  garciaRoleWeldTask : AcquisitionTask
  broadBiographySweep : AcquisitionTask

record TaskBinding : Set where
  constructor task-binding
  field
    task : AcquisitionTask
    residualReference : String
    producerReference : String
    acquisitionReference : String
    affectedConsumer : String

open TaskBinding public

taskBinding : AcquisitionTask → TaskBinding
taskBinding rezaMcCaslandTask = task-binding rezaMcCaslandTask
  "R52 Reza/McCasland exact same HCB/Mondaloy object residual"
  "contemporaneous HCB contract/task/review/roster primary-source producer"
  "2011-2013 identity-bearing FA9300-07-C-0001 / Mondaloy / HBTD record naming McCasland"
  "H2 shared-object consumer"
taskBinding ningPrimaryBytesTask = task-binding ningPrimaryBytesTask
  "R52 Ning DAAH01-01-9-R001 primary-bytes residual"
  "primary award/SOW/closeout record producer"
  "primary SOW/award/closeout bytes with personnel, facilities, subcontractors and apparatus"
  "exact-object then H2-crossing consumer"
taskBinding amyReferentWeldTask = task-binding amyReferentWeldTask
  "R52 Amy same-object referent identity residual"
  "authenticated original/release-review metadata producer"
  "Amy original or NASA review/release carrier welding statement to exact object/referent"
  "referent identity consumer"
taskBinding chavezScorpiusCrossingTask = task-binding chavezScorpiusCrossingTask
  "R52 Chavez retained-person Scorpius/DARHT crossing residual"
  "exact engineering artefact/team producer"
  "Scorpius/DARHT task, drawing, design review or work-package carrier with personnel"
  "H2 shared-object consumer"
taskBinding leblancSubordinateWBSTask = task-binding leblancSubordinateWBSTask
  "R52 LeBlanc subordinate FSP object crossing residual"
  "WBS-child/component/review/vendor producer"
  "WBS 658133.04.01.22.01.06 subordinate object/team record"
  "H2 shared-object consumer"
taskBinding chineseClusterOriginTask = task-binding chineseClusterOriginTask
  "R49/R52 Chinese cluster source-origin independence residual"
  "first-publication/source-of-source provenance producer"
  "earliest cluster publication and derivation/syndication graph"
  "investigator + journalist provenance consumer"
taskBinding garciaRoleWeldTask = task-binding garciaRoleWeldTask
  "R44/R51 Garcia primary employment/security-role weld residual"
  "employer/facility/contract/personnel primary-role producer"
  "same-person primary carrier for KCNSC/employment/property/security role"
  "investigator + lawyer + journalist role consumer"
taskBinding broadBiographySweep = task-binding broadBiographySweep
  "no exact promotion residual"
  "generic biography/search-engine producer"
  "collect additional broad biographies and thematic context"
  "no current discriminator"

------------------------------------------------------------------------
-- Hard gates before Pareto comparison.
------------------------------------------------------------------------

taskLawfulAndPurposeBound : AcquisitionTask → Bool
taskLawfulAndPurposeBound broadBiographySweep = true
taskLawfulAndPurposeBound _ = true

taskAttacksVisibleResidual : AcquisitionTask → Bool
taskAttacksVisibleResidual broadBiographySweep = false
taskAttacksVisibleResidual _ = true

taskConsumerRelevant : AcquisitionTask → Bool
taskConsumerRelevant broadBiographySweep = false
taskConsumerRelevant _ = true

taskSourceRoleAdmissible : AcquisitionTask → Bool
taskSourceRoleAdmissible broadBiographySweep = true
taskSourceRoleAdmissible _ = true

schedulerProblem : Pareto.ConsumerMDLProblem
schedulerProblem = Pareto.consumerMDLProblem
  AcquisitionTask
  (λ t → taskLawfulAndPurposeBound t ≡ true × taskSourceRoleAdmissible t ≡ true)
  (λ t → taskAttacksVisibleResidual t ≡ true × taskConsumerRelevant t ≡ true)
  acquisitionBurden
  (λ _ _ → ⊤)
  taskReference
  "ordinal acquisition-burden code local to Round 53; not dollars/time/probability/truth"
  "live residual closure for the scientist professional evidence room"
  where
    acquisitionBurden : AcquisitionTask → Nat
    acquisitionBurden rezaMcCaslandTask = 3
    acquisitionBurden ningPrimaryBytesTask = 4
    acquisitionBurden amyReferentWeldTask = 4
    acquisitionBurden chavezScorpiusCrossingTask = 2
    acquisitionBurden leblancSubordinateWBSTask = 2
    acquisitionBurden chineseClusterOriginTask = 1
    acquisitionBurden garciaRoleWeldTask = 2
    acquisitionBurden broadBiographySweep = 3

    taskReference : AcquisitionTask → String
    taskReference t = acquisitionReference (taskBinding t)

------------------------------------------------------------------------
-- Four declared Pareto axes.  Every score is a residual/burden penalty:
-- lower is better.  Values are repository-local scheduling codes only.
------------------------------------------------------------------------

data SchedulerAxis : Set where
  promotionResidualAxis : SchedulerAxis
  sourceOriginClosureAxis : SchedulerAxis
  professionalGateClosureAxis : SchedulerAxis
  acquisitionBurdenAxis : SchedulerAxis

schedulerScore : SchedulerAxis → AcquisitionTask → Nat
-- H2-sensitive acquisitions get lowest remaining promotion-residual penalties.
schedulerScore promotionResidualAxis rezaMcCaslandTask = 0
schedulerScore promotionResidualAxis ningPrimaryBytesTask = 1
schedulerScore promotionResidualAxis amyReferentWeldTask = 1
schedulerScore promotionResidualAxis chavezScorpiusCrossingTask = 1
schedulerScore promotionResidualAxis leblancSubordinateWBSTask = 1
schedulerScore promotionResidualAxis chineseClusterOriginTask = 3
schedulerScore promotionResidualAxis garciaRoleWeldTask = 3
schedulerScore promotionResidualAxis broadBiographySweep = 5

-- Provenance work wins this axis; exact-object searches retain some origin debt.
schedulerScore sourceOriginClosureAxis rezaMcCaslandTask = 2
schedulerScore sourceOriginClosureAxis ningPrimaryBytesTask = 1
schedulerScore sourceOriginClosureAxis amyReferentWeldTask = 1
schedulerScore sourceOriginClosureAxis chavezScorpiusCrossingTask = 1
schedulerScore sourceOriginClosureAxis leblancSubordinateWBSTask = 1
schedulerScore sourceOriginClosureAxis chineseClusterOriginTask = 0
schedulerScore sourceOriginClosureAxis garciaRoleWeldTask = 1
schedulerScore sourceOriginClosureAxis broadBiographySweep = 4

-- Role/authentication/referent tasks close professional gates most directly.
schedulerScore professionalGateClosureAxis rezaMcCaslandTask = 1
schedulerScore professionalGateClosureAxis ningPrimaryBytesTask = 1
schedulerScore professionalGateClosureAxis amyReferentWeldTask = 0
schedulerScore professionalGateClosureAxis chavezScorpiusCrossingTask = 2
schedulerScore professionalGateClosureAxis leblancSubordinateWBSTask = 2
schedulerScore professionalGateClosureAxis chineseClusterOriginTask = 1
schedulerScore professionalGateClosureAxis garciaRoleWeldTask = 0
schedulerScore professionalGateClosureAxis broadBiographySweep = 4

schedulerScore acquisitionBurdenAxis rezaMcCaslandTask = 3
schedulerScore acquisitionBurdenAxis ningPrimaryBytesTask = 4
schedulerScore acquisitionBurdenAxis amyReferentWeldTask = 4
schedulerScore acquisitionBurdenAxis chavezScorpiusCrossingTask = 2
schedulerScore acquisitionBurdenAxis leblancSubordinateWBSTask = 2
schedulerScore acquisitionBurdenAxis chineseClusterOriginTask = 1
schedulerScore acquisitionBurdenAxis garciaRoleWeldTask = 2
schedulerScore acquisitionBurdenAxis broadBiographySweep = 3

schedulerAxisReference : SchedulerAxis → String
schedulerAxisReference promotionResidualAxis = "remaining promotion-critical residual penalty"
schedulerAxisReference sourceOriginClosureAxis = "remaining source-origin/provenance uncertainty"
schedulerAxisReference professionalGateClosureAxis = "remaining investigator/lawyer/journalist gate debt"
schedulerAxisReference acquisitionBurdenAxis = "declared acquisition burden; ordinal only"

schedulerCosts : Pareto.CostHyperfabric schedulerProblem
schedulerCosts = Pareto.costHyperfabric SchedulerAxis schedulerScore schedulerAxisReference

schedulerNDimView : NDim.NDimParetoView schedulerCosts
schedulerNDimView = NDim.ndimParetoView
  4
  "four explicitly declared Round-53 scheduling axes"
  schedulerAxisReference
  true
  "no scalar projection is authoritative; inspect full four-axis task coordinates"

------------------------------------------------------------------------
-- Exact hard-gate fixtures.
------------------------------------------------------------------------

rezaMcCaslandEligible : Pareto.Eligible schedulerProblem rezaMcCaslandTask
rezaMcCaslandEligible = (refl , refl) , (refl , refl)

ningPrimaryBytesEligible : Pareto.Eligible schedulerProblem ningPrimaryBytesTask
ningPrimaryBytesEligible = (refl , refl) , (refl , refl)

amyReferentWeldEligible : Pareto.Eligible schedulerProblem amyReferentWeldTask
amyReferentWeldEligible = (refl , refl) , (refl , refl)

chavezScorpiusCrossingEligible : Pareto.Eligible schedulerProblem chavezScorpiusCrossingTask
chavezScorpiusCrossingEligible = (refl , refl) , (refl , refl)

leblancSubordinateWBSEligible : Pareto.Eligible schedulerProblem leblancSubordinateWBSTask
leblancSubordinateWBSEligible = (refl , refl) , (refl , refl)

chineseClusterOriginEligible : Pareto.Eligible schedulerProblem chineseClusterOriginTask
chineseClusterOriginEligible = (refl , refl) , (refl , refl)

garciaRoleWeldEligible : Pareto.Eligible schedulerProblem garciaRoleWeldTask
garciaRoleWeldEligible = (refl , refl) , (refl , refl)

broadBiographySweepNotEligible : Pareto.Eligible schedulerProblem broadBiographySweep → ⊥
broadBiographySweepNotEligible (_ , (() , _))

------------------------------------------------------------------------
-- Pareto trade-off fixtures: Tier A promotion attack versus cheaper provenance
-- closure are intentionally incomparable.  This is why Pareto is a frontier,
-- not a total ranking.
------------------------------------------------------------------------

rezaDoesNotDominateChineseOrigin :
  Pareto.WeaklyDominates schedulerCosts rezaMcCaslandTask chineseClusterOriginTask → ⊥
rezaDoesNotDominateChineseOrigin dominates = threeNotLeOne (dominates acquisitionBurdenAxis)
  where
    threeNotLeOne : 3 ≤ 1 → ⊥
    threeNotLeOne ()

chineseOriginDoesNotDominateReza :
  Pareto.WeaklyDominates schedulerCosts chineseClusterOriginTask rezaMcCaslandTask → ⊥
chineseOriginDoesNotDominateReza dominates = threeNotLeZero (dominates promotionResidualAxis)
  where
    threeNotLeZero : 3 ≤ 0 → ⊥
    threeNotLeZero ()

amyDoesNotDominateReza :
  Pareto.WeaklyDominates schedulerCosts amyReferentWeldTask rezaMcCaslandTask → ⊥
amyDoesNotDominateReza dominates = oneNotLeZero (dominates promotionResidualAxis)
  where
    oneNotLeZero : 1 ≤ 0 → ⊥
    oneNotLeZero ()

rezaDoesNotDominateAmy :
  Pareto.WeaklyDominates schedulerCosts rezaMcCaslandTask amyReferentWeldTask → ⊥
rezaDoesNotDominateAmy dominates = oneNotLeZero (dominates professionalGateClosureAxis)
  where
    oneNotLeZero : 1 ≤ 0 → ⊥
    oneNotLeZero ()

------------------------------------------------------------------------
-- Bound acquisition seam.  A scheduled task is progress-sensitive only when
-- the concrete acquisition is bound to the exact selected residual/producer.
------------------------------------------------------------------------

data SchedulerResidual : Set where
  hcbSameObjectResidual : SchedulerResidual
  ningPrimaryBytesResidual : SchedulerResidual
  amyReferentResidual : SchedulerResidual
  scorpiusCrossingResidual : SchedulerResidual
  leblancWBSResidual : SchedulerResidual
  chineseOriginResidual : SchedulerResidual
  garciaRoleResidual : SchedulerResidual
  noPromotionResidual : SchedulerResidual

data SchedulerProducer : Set where
  exactProgrammeRecordProducer : SchedulerProducer
  primaryAwardBytesProducer : SchedulerProducer
  identityWeldProducer : SchedulerProducer
  engineeringArtefactProducer : SchedulerProducer
  subordinateWBSProducer : SchedulerProducer
  provenanceGraphProducer : SchedulerProducer
  primaryRoleRecordProducer : SchedulerProducer
  genericBiographyProducer : SchedulerProducer

residualForTask : AcquisitionTask → SchedulerResidual
residualForTask rezaMcCaslandTask = hcbSameObjectResidual
residualForTask ningPrimaryBytesTask = ningPrimaryBytesResidual
residualForTask amyReferentWeldTask = amyReferentResidual
residualForTask chavezScorpiusCrossingTask = scorpiusCrossingResidual
residualForTask leblancSubordinateWBSTask = leblancWBSResidual
residualForTask chineseClusterOriginTask = chineseOriginResidual
residualForTask garciaRoleWeldTask = garciaRoleResidual
residualForTask broadBiographySweep = noPromotionResidual

producerForTask : AcquisitionTask → SchedulerProducer
producerForTask rezaMcCaslandTask = exactProgrammeRecordProducer
producerForTask ningPrimaryBytesTask = primaryAwardBytesProducer
producerForTask amyReferentWeldTask = identityWeldProducer
producerForTask chavezScorpiusCrossingTask = engineeringArtefactProducer
producerForTask leblancSubordinateWBSTask = subordinateWBSProducer
producerForTask chineseClusterOriginTask = provenanceGraphProducer
producerForTask garciaRoleWeldTask = primaryRoleRecordProducer
producerForTask broadBiographySweep = genericBiographyProducer

record ScheduledAcquisition : Set where
  constructor scheduled-acquisition
  field
    selectedTask : AcquisitionTask
    attackedResidual : SchedulerResidual
    producer : SchedulerProducer
    directiveReference : String

open ScheduledAcquisition public

schedulerAlignment : Bound.AcquisitionAlignment AcquisitionTask SchedulerResidual SchedulerProducer ScheduledAcquisition
schedulerAlignment = Bound.acquisition-alignment
  residualForTask
  producerForTask
  attackedResidual
  producer

rezaBoundAcquisition : Bound.BoundAcquisitionDemand schedulerAlignment rezaMcCaslandTask hcbSameObjectResidual
rezaBoundAcquisition = Bound.bound-acquisition-demand
  (scheduled-acquisition rezaMcCaslandTask hcbSameObjectResidual exactProgrammeRecordProducer
    "search exact contemporaneous HCB/Mondaloy programme records naming McCasland")
  refl refl refl

scheduledAcquisitionMustBindToSelectedResidual : Bool
scheduledAcquisitionMustBindToSelectedResidual = true

------------------------------------------------------------------------
-- Scheduler firewalls.
------------------------------------------------------------------------

paretoFrontierDoesNotCreateTruth : Bool
paretoFrontierDoesNotCreateTruth = true

dominatedInterestingResearchStaysOffCriticalPath : Bool
dominatedInterestingResearchStaysOffCriticalPath = true

cheapestTaskDoesNotAutomaticallyWin : Bool
cheapestTaskDoesNotAutomaticallyWin = true

highestPromotionGainDoesNotAutomaticallyWin : Bool
highestPromotionGainDoesNotAutomaticallyWin = true

paretoSchedulerDoesNotDeleteOffFrontierResiduals : Bool
paretoSchedulerDoesNotDeleteOffFrontierResiduals = true

schedulerCostsAreNotEmpiricalProbabilities : Bool
schedulerCostsAreNotEmpiricalProbabilities = true

schedulerCostsAreNotDollarOrTimeEstimates : Bool
schedulerCostsAreNotDollarOrTimeEstimates = true

professionalGateClosureCannotPayH2 : Bool
professionalGateClosureCannotPayH2 = true

sourceOriginClosureCannotPayH2 : Bool
sourceOriginClosureCannotPayH2 = true

boundDemandDoesNotPayRequirement : Bound.BoundDemandAutomaticallyPaysRequirement → ⊥
boundDemandDoesNotPayRequirement = Bound.bindingDoesNotPayRequirement

round53H2PaidCount : Nat
round53H2PaidCount = 0

round53H3PaidCount : Nat
round53H3PaidCount = 0

round53Reading : String
round53Reading = "Pareto now performs the scheduling job: hard-gate tasks by lawful/purpose-bounded acquisition, source-role admissibility, live-residual attack and consumer relevance; compare only surviving tasks on promotion-residual, source-origin, professional-gate and acquisition-burden axes; retain incomparable trade-offs instead of inventing a weighted total score; and bind any scheduled acquisition back to the exact selected residual/producer. Broad biography gathering remains visible but off the current critical path because it does not split a live promotion or professional-consumer fibre."

round53ParetoFrontier : String
round53ParetoFrontier = "Current high-alpha frontier contains distinct trade-offs rather than one universal winner: Reza/McCasland attacks the nearest literal H2 seam; Amy directly closes an identity/professional gate; Ning can unlock unseen primary object structure; Chavez and LeBlanc provide lower-burden exact-object crossing searches; Chinese-cluster origin tracing cheaply closes provenance uncertainty; Garcia role welding closes a major professional source-role gate. The scheduler reruns whenever a residual is paid or reopened."
