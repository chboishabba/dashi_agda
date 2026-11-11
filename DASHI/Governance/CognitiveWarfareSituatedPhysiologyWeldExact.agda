module DASHI.Governance.CognitiveWarfareSituatedPhysiologyWeldExact where

-- Original DASHI cross-owner bridge; not an attribution of authorial
-- mathematics to Crenshaw, Satta, Alice Brown or John Anthony Brown.
-- Synthetic cases only. This module does NOT identify a real actor,
-- cognitive campaign, coercive intention, injury or physiological diagnosis.

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.CognitiveWarfareAdmissibleDetectionExact as Detection
import DASHI.Cognition.CognitiveWarfarePlatoTraumaDetectorWeldExact as Warfare
import DASHI.Governance.EpistemicPowerHistoryAndNonSubstitutionExact as Work
import DASHI.Governance.SituatedCortisolAggregateNonIdentificationExact as Cortisol
import DASHI.Governance.SituatedCortisolPNFAdmissibilityExact as Causal
import DASHI.Governance.SituatedBiomarkerObserverAgencyExact as Agency

-- Existing query-indexed detection result: present target-local traces
-- collide even though origin differs. The selected provenance inspection
-- is a separate admissible action, not inference from the victim's body.
samePresentTargetCannotEstablishOrigin :
  Detection.targetProject Detection.organicHidden
  ≡ Detection.targetProject Detection.influenceHidden
samePresentTargetCannotEstablishOrigin =
  Detection.targetLocalCollision

sameTargetSurfaceCannotAnswerOriginQuery :
  DASHI.Core.AdmissibleConsumerFutureAdequacyExact.AdmissibleAdequateNow
    Detection.detectionProblem Detection.originQuery → ⊥
sameTargetSurfaceCannotAnswerOriginQuery =
  Detection.targetSurfaceCannotDetermineOrigin

-- Content + action-cone contraction cannot by itself establish who
-- produced the observed situation or with what purpose.
sameContentAndConeCannotDetermineProvenance :
  NF.FactorsThrough Warfare.contentConeObserver Warfare.provenance → ⊥
sameContentAndConeCannotDetermineProvenance =
  Warfare.contentConeCannotDetermineProvenance

-- The work itself may be observed or logged without proving whether
-- an episode is legitimate quality review or intentional obstruction.
sameEpistemicTasksCannotIdentifyStrategicPurpose :
  NF.NonFactorabilityWitness Work.observedTasks Work.statedPurpose
sameEpistemicTasksCannotIdentifyStrategicPurpose =
  Work.sameTasksCannotIdentifyPurpose

-- One person can experience more or less work under the same publicly
-- observed disposition; this is a workload theorem, not a fatigue assay.
samePublicDispositionDifferentRetentionWork :
  NF.NonFactorabilityWitness
    Work.visibleDisposition Work.retentionDemand
samePublicDispositionDifferentRetentionWork =
  Work.sameOutcomeDifferentRetentionHistory

-- A cortisol value can be precise and yet fail to determine the
-- institutional source of the response. This precludes reverse inference.
cortisolDoesNotDetermineCausalAttribution :
  NF.FactorsThrough Causal.measurementValue Causal.causalAttribution → ⊥
cortisolDoesNotDetermineCausalAttribution =
  Causal.pointIdentifiedBiomarkerDoesNotIdentifyCause

-- Even aggregation of environmental demand with cohort biomarker total
-- cannot identify the selected individual response.
aggregateSocialAndEndocrineTotalsInsufficient :
  NF.FactorsThrough
    Cortisol.coarseEnvironmentAndAggregateTotal
    (Cortisol.individualResponse Cortisol.participantA) → ⊥
aggregateSocialAndEndocrineTotalsInsufficient =
  Cortisol.aggregateEnvironmentalExposureCannotDeterminePerson

-- Separate coordinate types prevent the common and harmful category
-- errors of equating a detector flag with a physiological or legal result.
data DetectorFinding : Set where
  sourceUnresolved sourceVerified : DetectorFinding

data PhysiologicalFinding : Set where
  noIndividualAssay validatedIndividualAssay : PhysiologicalFinding

data AuthorityFinding : Set where
  legalUndetermined legalDeterminedByAuthority : AuthorityFinding

sourceVerificationNotAnAssay :
  sourceVerified ≡ noIndividualAssay → ⊥
sourceVerificationNotAnAssay ()

legalAuthorityNotSourceVerification :
  legalDeterminedByAuthority ≡ legalUndetermined → ⊥
legalAuthorityNotSourceVerification ()

-- The meaningful source-paid K2/K3 path requires distinct originals.
-- Nothing is inhabited merely by detecting a potential influence event.
record CognitiveWarfareSituatedEvidence
  (Subject Event Institution : Set) : Set₁ where
  field
    originalProvenanceVerified : Event → Set
    actorControllerChainVerified : Event → Institution → Set
    intentionalCoordinationEvidence : Event → Set
    independentlyObservedTasks : Subject → Event → Set
    personTimeExposureLinked : Subject → Event → Set
    observedPhysiologyWithConsent : Subject → Set
    legitimateReviewAlternativeConsidered : Event → Set
    individualCausalComparator : Subject → Event → Set
    firstPersonAccountPreserved : Subject → Set
    legalClaimIndependentlyReviewed : Institution → Set

-- Optional biomarker refusal is not denial of the person's account.
refusalBlocksOptionalAssay :
  Agency.OptionalBiomarkerPermission Agency.refuses → ⊥
refusalBlocksOptionalAssay =
  Agency.refusalBlocksOptionalBiomarkerUse
