module DASHI.Cognition.NickLandProvocationOverreactionPopulistTransferExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.BannonPlaybookBondiMobilisationCrossPollinationExact as Mobilisation
import DASHI.Cognition.PsychologicalInfluenceInfrastructureCrossPollinationExact as Psych
import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Incidence
import DASHI.Governance.HansonOneNationPoliticalEcologyExact as Hanson
import DASHI.Governance.HansonFailedMarxianTransformationAuditExact as HansonTransform

------------------------------------------------------------------------
-- ACCELERATION / PROVOCATION / OVERREACTION / LOCK-IN CROSS-POLLINATION
--
-- Distinct domains can instantiate a common recursive form:
--
--   perturbation / provocation
--      -> amplified response
--      -> erosion or reconfiguration of constraints
--      -> new durable capacity
--      -> changed conditions for the next perturbation.
--
-- Structural equivalence does not identify ideologies, actors, intentions or
-- coordination.  In particular:
--   Nick Land accelerationism != terrorist provocation strategy
--   terrorist provocation != Bannon information strategy
--   Bannon doctrine != One Nation/LNP method transfer
--   crisis mobilisation != fabrication of the precipitating event.
------------------------------------------------------------------------

data RecursiveMechanism : Set where
  acceleration : RecursiveMechanism
  provocation : RecursiveMechanism
  attentionSaturation : RecursiveMechanism
  threatAmplification : RecursiveMechanism
  counterReactionInduction : RecursiveMechanism
  constraintErosion : RecursiveMechanism
  institutionalLockIn : RecursiveMechanism
  recursiveCapacityGain : RecursiveMechanism
  backlashRecruitment : RecursiveMechanism

data ComparatorSurface : Set where
  nickLandTechnocapitalAcceleration : ComparatorSurface
  bannonFloodZoneDeconstruction : ComparatorSurface
  alQaedaProvocationWarOnTerror : ComparatorSurface
  bondiSecurityMobilisation : ComparatorSurface
  hansonAshbyDigitalPopulism : ComparatorSurface
  queenslandLNPSecurityCrisisMobilisation : ComparatorSurface

record ComparatorReceipt : Set where
  constructor comparator-receipt
  field
    surface : ComparatorSurface
    source : String
    boundedFinding : String
    doctrineOrPatternPaid : Bool
    deploymentPaid : Bool
    directTechniqueTransferPaid : Bool
    sharedRecursiveTopologyPaid : Bool
    outcomeCausationPaid : Bool
open ComparatorReceipt public

nickLandReceipt : ComparatorReceipt
nickLandReceipt = comparator-receipt
  nickLandTechnocapitalAcceleration
  "Nick Land, 'Meltdown', in Fanged Noumena; existing DASHI Land/accelerationism analysis"
  "Land's accelerationist writing treats technocapital as a recursive runaway process that erodes inherited social constraints as techno-economic interaction accelerates. DASHI uses this as a structural comparator, not as evidence that later political actors took instructions from Land."
  true false false true false

bannonReceipt : ComparatorReceipt
bannonReceipt = comparator-receipt
  bannonFloodZoneDeconstruction
  "Steve Bannon public statements; Cambridge disinformation scholarship; CPAC 2017 reporting"
  "Bannon's public playbook combines information saturation and adversarial-media framing with a stated project of deconstructing the administrative state."
  true true false true false

alQaedaProvocationReceipt : ComparatorReceipt
alQaedaProvocationReceipt = comparator-receipt
  alQaedaProvocationWarOnTerror
  "Kydd and Walter 2006 terrorism-strategy literature; subsequent provocation/overreaction scholarship"
  "Provocation is a recognised terrorist strategy in which violence is intended to induce a target government to overreact, increasing costs, grievance, polarisation or support for the attacker. The slogan that al-Qaeda 'already won' once the War on Terror began is an interpretive shorthand for this mechanism, not a literal theorem that every al-Qaeda objective was achieved."
  true true false true false

bondiReceipt : ComparatorReceipt
bondiReceipt = comparator-receipt
  bondiSecurityMobilisation
  "Australian post-Bondi legal/government/Herzog/Royal Commission source bundle"
  "A genuine attack was followed by threat/security framing, political mobilisation, exceptional protest/policing measures and institution-building. This pays fomentation/amplification and persistence questions without paying fabrication of the attack."
  true true false true false

hansonAshbyReceipt : ComparatorReceipt
hansonAshbyReceipt = comparator-receipt
  hansonAshbyDigitalPopulism
  "HansonOneNationPoliticalEcologyExact; 2026 Australian reporting on James Ashby's digital campaign operation"
  "One Nation's current political ecology includes deliberate mastery of fragmented/social media, controversy as attention, AI/social content, and reporting describing Ashby's campaign machine as borrowing aggressive US/Trump/Farage-style digital tactics. This pays explicit emulation at the communications-strategy level, not Bannon personnel control or common command."
  true true false true false

lnpSecurityReceipt : ComparatorReceipt
lnpSecurityReceipt = comparator-receipt
  queenslandLNPSecurityCrisisMobilisation
  "Queensland Government 2025-2026 youth-justice and policing releases; legislation; current LNP security rhetoric"
  "The Crisafulli government repeatedly frames a 'Youth Crime Crisis' and converts it into expanded Adult Crime Adult Time offences, permanent statewide youth electronic monitoring availability, stronger bail sanctions and other policing/security capacity. This pays a crisis-to-capacity structural comparator; direct Trump/Bannon method transfer is not established."
  true true false true false

------------------------------------------------------------------------
-- Target-self-harm / pyrrhic-response geometry.
------------------------------------------------------------------------

data ResponseEffect : Set where
  directDamage : ResponseEffect
  responseCost : ResponseEffect
  rightsOrConstraintLoss : ResponseEffect
  institutionalExpansion : ResponseEffect
  polarisation : ResponseEffect
  recruitmentOrLegitimation : ResponseEffect
  durablePathDependence : ResponseEffect

record ProvocationOverreactionGeometry : Set where
  constructor provocation-overreaction-geometry
  field
    attackerOrProvocateurCanBenefitFromTargetResponse : Bool
    responseCanCostTargetMoreThanInitialPerturbation : Bool
    responseCanExpandStateCapacity : Bool
    responseCanCreatePersistentPathDependence : Bool
    benefitRequiresAttackerControlOfResponse : Bool
    overreactionProvesInitialEventWasFabricated : Bool
open ProvocationOverreactionGeometry public

canonicalProvocationOverreactionGeometry : ProvocationOverreactionGeometry
canonicalProvocationOverreactionGeometry =
  provocation-overreaction-geometry true true true true false false

data BenefitFromResponseImpliesControl : Set where
data OverreactionImpliesFabrication : Set where
data SharedRecursiveFormImpliesSharedIdeology : Set where
data CrisisFramingImpliesFakeCrisis : Set where
data StructuralEmulationImpliesPersonnelTransfer : Set where

benefitFromResponseDoesNotRequireControl : BenefitFromResponseImpliesControl → ⊥
benefitFromResponseDoesNotRequireControl ()

overreactionDoesNotCreateFabrication : OverreactionImpliesFabrication → ⊥
overreactionDoesNotCreateFabrication ()

sharedFormDoesNotCreateIdeologicalIdentity : SharedRecursiveFormImpliesSharedIdeology → ⊥
sharedFormDoesNotCreateIdeologicalIdentity ()

crisisFramingDoesNotCreateFakeCrisis : CrisisFramingImpliesFakeCrisis → ⊥
crisisFramingDoesNotCreateFakeCrisis ()

structuralEmulationDoesNotCreatePersonnelTransfer : StructuralEmulationImpliesPersonnelTransfer → ⊥
structuralEmulationDoesNotCreatePersonnelTransfer ()

------------------------------------------------------------------------
-- Comparative pipelines.
------------------------------------------------------------------------

record RecursivePipeline : Set where
  constructor recursive-pipeline
  field
    label : String
    mechanisms : List RecursiveMechanism
    firstOrderReading : String
    secondOrderReading : String
    thirdOrderReading : String
    directCommonCommandPaid : Bool
open RecursivePipeline public

warOnTerrorPipeline : RecursivePipeline
warOnTerrorPipeline = recursive-pipeline
  "9/11 -> War on Terror overreaction / lock-in comparator"
  (provocation ∷ counterReactionInduction ∷ threatAmplification ∷ constraintErosion ∷ institutionalLockIn ∷ recursiveCapacityGain ∷ [])
  "Direct attack produces death, fear and immediate political demand for response."
  "Target response can impose larger fiscal, military, civil-liberty and geopolitical costs and can widen the constituency or grievance environment exploited by the attacker."
  "Emergency surveillance, military, legal and bureaucratic capacities can persist and alter the target state's future response function long after the precipitating attack."
  false

landBannonPipeline : RecursivePipeline
landBannonPipeline = recursive-pipeline
  "Land acceleration comparator <-> Bannon saturation/deconstruction"
  (acceleration ∷ attentionSaturation ∷ constraintErosion ∷ institutionalLockIn ∷ recursiveCapacityGain ∷ [])
  "Both can be represented as processes that intensify feedback rather than restoring equilibrium."
  "Destabilisation can weaken mediating institutions and make more radical intervention feasible."
  "The new institutional configuration can itself increase the capacity for later acceleration/deconstruction. This is a DASHI structural comparison, not a paid Land->Bannon intellectual-transfer edge."
  false

hansonPipeline : RecursivePipeline
hansonPipeline = recursive-pipeline
  "One Nation digital provocation / attention / mobilisation"
  (attentionSaturation ∷ threatAmplification ∷ backlashRecruitment ∷ recursiveCapacityGain ∷ [])
  "Provocative content earns attention and reach in a fragmented algorithmic media ecology."
  "Attention can be converted into audience capture, donations, candidates, polling strength and agenda pressure on larger parties."
  "Major parties may then adopt harder policy positions, shifting the political feasible set even where One Nation does not directly govern."
  false

lnpPipeline : RecursivePipeline
lnpPipeline = recursive-pipeline
  "Queensland LNP youth-crime/security mobilisation"
  (threatAmplification ∷ demandExceptionalEquivalent ∷ institutionalLockIn ∷ recursiveCapacityGain ∷ [])
  "Crime/safety framing supports immediate punitive legislative and policing responses."
  "Expanded offences, monitoring, bail sanctions and policing capacity alter institutional defaults and affected-population burdens."
  "Once normalised, exceptional or crisis-justified capacity becomes part of the baseline from which subsequent crises are governed."
  false
  where
    demandExceptionalEquivalent : RecursiveMechanism
    demandExceptionalEquivalent = counterReactionInduction

------------------------------------------------------------------------
-- Max-cut acquisition debts.
------------------------------------------------------------------------

data AccelerationDebt : Set where
  landToBannonActualLineage : AccelerationDebt
  bannonToHansonMethodTransfer : AccelerationDebt
  bannonTrumpToLNPMethodTransfer : AccelerationDebt
  post9_11PersistentCapacityIncidence : AccelerationDebt
  bondiPersistentCapacityAndBeneficiaries : AccelerationDebt
  oneNationPressureOnMajorPartyFeasibleSet : AccelerationDebt

record AccelerationAcquisition : Set where
  constructor acceleration-acquisition
  field
    debt : AccelerationDebt
    priority : Nat
    requiresSameObjectReceipt : Bool
    question : String
open AccelerationAcquisition public

canonicalAccelerationAcquisition : List AccelerationAcquisition
canonicalAccelerationAcquisition =
  acceleration-acquisition bannonToHansonMethodTransfer 100 true
    "Resolve the exact One Nation/Ashby US-strategy lineage: named consultants, training, vendors, shared campaign artefacts, Bannon/Farage/Trump contacts and actual method transfer beyond public emulation."
  ∷ acceleration-acquisition bannonTrumpToLNPMethodTransfer 99 true
    "Test whether Queensland LNP crisis/security campaigning has direct Trump/Bannon personnel, consultancy, vendor, messaging or training receipts; keep structural similarity separate until then."
  ∷ acceleration-acquisition post9_11PersistentCapacityIncidence 98 true
    "Trace which post-9/11 emergency powers, intelligence architectures, procurement systems and surveillance capacities persisted, who benefited, who bore burden, and how they feed current Five Eyes/Pine Gap/Palantir infrastructure."
  ∷ acceleration-acquisition bondiPersistentCapacityAndBeneficiaries 97 true
    "Trace post-Bondi mobilisation into durable law, policing, intelligence, media/speech governance and named organisational beneficiaries, including reversals and judicial constraints."
  ∷ acceleration-acquisition oneNationPressureOnMajorPartyFeasibleSet 96 true
    "Measure whether and where One Nation attention/electoral growth causally shifts Coalition/LNP policy positions rather than merely correlating with a shared voter environment."
  ∷ acceleration-acquisition landToBannonActualLineage 90 true
    "Separate conceptual convergence among Land/neoreaction/Thiel/Bannon/Trump-world from documented citation, personnel or organisational transmission."
  ∷ []
