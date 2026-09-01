module DASHI.Governance.AnomalousResearchPriorityFromTemporalFibreExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal
import DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact as Trajectory
import DASHI.Governance.PhenomenonEvidenceLadderProjectionOverTimeExact as Ladder

------------------------------------------------------------------------
-- RESEARCH PRIORITY FROM TEMPORAL EVIDENCE FIBRE
--
-- Research priority is not a permanent rank attached to a phenomenon name.
-- It is a consumer-relative next move induced by the current fibre, the
-- coordinate still unresolved, and the path by which that fibre was reached.
------------------------------------------------------------------------

data ResearchQuestion : Set where
  reproduceClaimedSignal
  auditMethodAndSelection
  discriminateMechanism
  testOperationalUtility
  separateExpectancyAndDrugEffect
  testGeneralisationAndDurability
  timeLockedRealityTest
  characterizePhenomenology
  : ResearchQuestion

data ResearchDisposition : Set where
  highValueDecisiveTest
  highValueMechanismWork
  highValueClinicalGeneralisation
  mediumValueAdversarialReplication
  mediumValueMethodAudit
  lowValueRepeatSameParadigm
  : ResearchDisposition

record TemporalResearchMove : Set where
  constructor temporalResearchMove
  field
    phenomenon : Trajectory.Phenomenon
    atMoment : Trajectory.EvidenceMoment
    question : ResearchQuestion
    disposition : ResearchDisposition
    unresolvedCoordinate : Temporal.EvidenceCoordinate

open TemporalResearchMove public

------------------------------------------------------------------------
-- Current source-bounded moves.
------------------------------------------------------------------------

bemCurrentMove : TemporalResearchMove
bemCurrentMove = temporalResearchMove
  Trajectory.bemPrecognition
  Trajectory.transparentPsi2025
  auditMethodAndSelection
  mediumValueMethodAudit
  Temporal.mechanismDiscrimination

presentimentCurrentMove : TemporalResearchMove
presentimentCurrentMove = temporalResearchMove
  Trajectory.presentimentPhysiology
  Trajectory.presentimentUpdate2018
  reproduceClaimedSignal
  highValueDecisiveTest
  Temporal.independentReplication

ganzfeldCurrentMove : TemporalResearchMove
ganzfeldCurrentMove = temporalResearchMove
  Trajectory.ganzfeldPsi
  Trajectory.ganzfeldContestedCurrent
  reproduceClaimedSignal
  mediumValueAdversarialReplication
  Temporal.independentReplication

stargateCurrentMove : TemporalResearchMove
stargateCurrentMove = temporalResearchMove
  Trajectory.stargateRemoteViewing
  Trajectory.stargateOperationalReview1995
  auditMethodAndSelection
  mediumValueMethodAudit
  Temporal.controlStrength

psilocybinCurrentMove : TemporalResearchMove
psilocybinCurrentMove = temporalResearchMove
  Trajectory.psilocybinDepression
  Trajectory.psilocybinMeta2025_2026
  separateExpectancyAndDrugEffect
  highValueClinicalGeneralisation
  Temporal.controlStrength

ndeCurrentMove : TemporalResearchMove
ndeCurrentMove = temporalResearchMove
  Trajectory.ndeCardiacArrestConsciousness
  Trajectory.awareII2023
  timeLockedRealityTest
  highValueMechanismWork
  Temporal.mechanismDiscrimination

------------------------------------------------------------------------
-- Historical movement in research question: the same phenomenon can warrant a
-- different next experiment after its fibre changes.
------------------------------------------------------------------------

data BemResearchEpoch : Set where bemEarlyResearch bemCurrentResearch : BemResearchEpoch

data BemQuestionCode : Set where replicateOriginalBem auditTransparentPsiResidual : BemQuestionCode

data BemSummary : Set where bemPhenomenonName : BemSummary

bemSummary : BemResearchEpoch → BemSummary
bemSummary _ = bemPhenomenonName

bemQuestion : BemResearchEpoch → BemQuestionCode
bemQuestion bemEarlyResearch = replicateOriginalBem
bemQuestion bemCurrentResearch = auditTransparentPsiResidual

bemQuestionChanged :
  bemQuestion bemEarlyResearch ≡ bemQuestion bemCurrentResearch → ⊥
bemQuestionChanged ()

phenomenonNameCannotDetermineResearchQuestion :
  INF.FactorsThrough bemSummary bemQuestion → ⊥
phenomenonNameCannotDetermineResearchQuestion =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      bemEarlyResearch bemCurrentResearch refl bemQuestionChanged)

------------------------------------------------------------------------
-- Present evidence coordinates justify the move without promoting them into a
-- global value score.
------------------------------------------------------------------------

psilocybinControlStillContested :
  Ladder.standingAt Trajectory.psilocybinMeta2025_2026 Temporal.controlStrength
  ≡ Temporal.contested
psilocybinControlStillContested = refl

bemReplicationCurrentlyDowngraded :
  Ladder.standingAt Trajectory.transparentPsi2025 Temporal.independentReplication
  ≡ Temporal.downgraded
bemReplicationCurrentlyDowngraded = refl

ndeMechanismStillUnresolved :
  Ladder.standingAt Trajectory.awareII2023 Temporal.mechanismDiscrimination
  ≡ Temporal.unresolved
ndeMechanismStillUnresolved = refl

------------------------------------------------------------------------
-- Non-promotions.
------------------------------------------------------------------------

data HighResearchValuePromotesPositiveEffect : Set where

data LowRepeatValuePromotesImpossibility : Set where

data MechanismPriorityPromotesOntology : Set where

data ClinicalPriorityPromotesRegulatoryMandate : Set where

highResearchValueDoesNotPromotePositiveEffect : HighResearchValuePromotesPositiveEffect → ⊥
highResearchValueDoesNotPromotePositiveEffect ()

lowRepeatValueDoesNotPromoteImpossibility : LowRepeatValuePromotesImpossibility → ⊥
lowRepeatValueDoesNotPromoteImpossibility ()

mechanismPriorityDoesNotPromoteOntology : MechanismPriorityPromotesOntology → ⊥
mechanismPriorityDoesNotPromoteOntology ()

clinicalPriorityDoesNotPromoteRegulatoryMandate : ClinicalPriorityPromotesRegulatoryMandate → ⊥
clinicalPriorityDoesNotPromoteRegulatoryMandate ()

record AnomalousResearchPriorityTemporalBoundary : Set where
  constructor anomalousResearchPriorityTemporalBoundary
  field
    priorityDependsOnTemporalFibre : Bool
    priorityDependsOnTemporalFibreIsTrue : priorityDependsOnTemporalFibre ≡ true
    phenomenonNameFixesPermanentPriority : Bool
    phenomenonNameFixesPermanentPriorityIsFalse : phenomenonNameFixesPermanentPriority ≡ false
    highResearchValueMeansEffectTrue : Bool
    highResearchValueMeansEffectTrueIsFalse : highResearchValueMeansEffectTrue ≡ false
    lowRepeatValueMeansImpossible : Bool
    lowRepeatValueMeansImpossibleIsFalse : lowRepeatValueMeansImpossible ≡ false

canonicalAnomalousResearchPriorityTemporalBoundary :
  AnomalousResearchPriorityTemporalBoundary
canonicalAnomalousResearchPriorityTemporalBoundary =
  anomalousResearchPriorityTemporalBoundary true refl false refl false refl false refl
