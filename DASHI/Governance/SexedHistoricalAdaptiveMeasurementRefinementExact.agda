module DASHI.Governance.SexedHistoricalAdaptiveMeasurementRefinementExact where

------------------------------------------------------------------------
-- ADAPTIVE MEASUREMENT / REFINE-BEFORE-COLLAPSE FOR HISTORICAL PATH FIBRES
--
-- Cross-pollinates:
--   * sexed historical path-order non-factorability;
--   * ternary reject / suspend-and-refine / accept semantics;
--   * experiment-design logic: choose the next measurement because it
--     separates live hidden histories, not because a binary classifier demands
--     an immediate pole.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Governance.SexedHistoricalDialecticalOrderHolonomyAnalogueExact as Order
import DASHI.Governance.SexedHistoricalBinaryTernaryDialecticExact as BT
import DASHI.Governance.SexedHistoricalStatisticalExperimentHyperfabricExact as Stats

------------------------------------------------------------------------
-- Competing hidden histories share the same coarse present surface.
------------------------------------------------------------------------

data HiddenHistory : Set where
  institutionFirstHistory
  reinterpretationFirstHistory
  : HiddenHistory

coarsePresent : HiddenHistory → Order.CoarseHistoricalStratum
coarsePresent _ = Order.formallyCorrectedContested

truePath : HiddenHistory → Order.PathOrder
truePath institutionFirstHistory = Order.institutionThenReinterpret
truePath reinterpretationFirstHistory = Order.reinterpretThenInstitution

coarsePresentCannotRecoverHiddenHistory :
  INF.FactorsThrough coarsePresent truePath → ⊥
coarsePresentCannotRecoverHiddenHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      institutionFirstHistory
      reinterpretationFirstHistory
      refl
      (λ ()))

------------------------------------------------------------------------
-- Candidate measurements target distinct fibres.
------------------------------------------------------------------------

data MeasurementKind : Set where
  currentStatusOnly
  sequenceArchive
  symbolicTimingInterview
  institutionalTimingArchive
  powerHistoryMeasure
  networkMemoryMeasure
  : MeasurementKind

data MeasurementResult : Set where
  sameCurrentStatus
  institutionPrecedesReinterpretation
  reinterpretationPrecedesInstitution
  routeStillUnresolved
  : MeasurementResult

measure : MeasurementKind → HiddenHistory → MeasurementResult
measure currentStatusOnly _ = sameCurrentStatus
measure sequenceArchive institutionFirstHistory = institutionPrecedesReinterpretation
measure sequenceArchive reinterpretationFirstHistory = reinterpretationPrecedesInstitution
measure symbolicTimingInterview institutionFirstHistory = institutionPrecedesReinterpretation
measure symbolicTimingInterview reinterpretationFirstHistory = reinterpretationPrecedesInstitution
measure institutionalTimingArchive institutionFirstHistory = institutionPrecedesReinterpretation
measure institutionalTimingArchive reinterpretationFirstHistory = reinterpretationPrecedesInstitution
measure powerHistoryMeasure _ = routeStillUnresolved
measure networkMemoryMeasure _ = routeStillUnresolved

currentStatusMeasurementDoesNotSeparate :
  measure currentStatusOnly institutionFirstHistory
  ≡ measure currentStatusOnly reinterpretationFirstHistory
currentStatusMeasurementDoesNotSeparate = refl

sequenceArchiveSeparates :
  measure sequenceArchive institutionFirstHistory
  ≡ measure sequenceArchive reinterpretationFirstHistory → ⊥
sequenceArchiveSeparates ()

------------------------------------------------------------------------
-- Ternary measurement policy: do not force unresolved fibres into either pole.
------------------------------------------------------------------------

measurementDisposition : MeasurementKind → Suspension.EpistemicDisposition
measurementDisposition currentStatusOnly = Suspension.suspendAndRefine
measurementDisposition sequenceArchive = Suspension.acceptHere
measurementDisposition symbolicTimingInterview = Suspension.acceptHere
measurementDisposition institutionalTimingArchive = Suspension.acceptHere
measurementDisposition powerHistoryMeasure = Suspension.suspendAndRefine
measurementDisposition networkMemoryMeasure = Suspension.suspendAndRefine

coarseOnlyRequiresRefinement :
  measurementDisposition currentStatusOnly ≡ Suspension.suspendAndRefine
coarseOnlyRequiresRefinement = refl

powerOnlyRequiresRefinementForPathQuestion :
  measurementDisposition powerHistoryMeasure ≡ Suspension.suspendAndRefine
powerOnlyRequiresRefinementForPathQuestion = refl

sequenceMeasurementIsAdmissibleForPathSeparation :
  measurementDisposition sequenceArchive ≡ Suspension.acceptHere
sequenceMeasurementIsAdmissibleForPathSeparation = refl

------------------------------------------------------------------------
-- Diagnostic value is question-relative. A power measure may be useful for a
-- power question while remaining neutral for the path-order question.
------------------------------------------------------------------------

data ResearchQuestion : Set where
  recoverPathOrder
  estimatePowerContext
  estimateConstructionDirection
  : ResearchQuestion

data DiagnosticValue : Set where
  nonDiagnostic
  partiallyDiagnostic
  separatingDiagnostic
  : DiagnosticValue

diagnosticFor : ResearchQuestion → MeasurementKind → DiagnosticValue
diagnosticFor recoverPathOrder currentStatusOnly = nonDiagnostic
diagnosticFor recoverPathOrder sequenceArchive = separatingDiagnostic
diagnosticFor recoverPathOrder symbolicTimingInterview = separatingDiagnostic
diagnosticFor recoverPathOrder institutionalTimingArchive = separatingDiagnostic
diagnosticFor recoverPathOrder powerHistoryMeasure = nonDiagnostic
diagnosticFor recoverPathOrder networkMemoryMeasure = partiallyDiagnostic
diagnosticFor estimatePowerContext powerHistoryMeasure = separatingDiagnostic
diagnosticFor estimatePowerContext _ = partiallyDiagnostic
diagnosticFor estimateConstructionDirection symbolicTimingInterview = partiallyDiagnostic
diagnosticFor estimateConstructionDirection _ = nonDiagnostic

sameMeasurementNeedNotHaveSameDiagnosticRole :
  diagnosticFor recoverPathOrder powerHistoryMeasure
  ≡ diagnosticFor estimatePowerContext powerHistoryMeasure → ⊥
sameMeasurementNeedNotHaveSameDiagnosticRole ()

------------------------------------------------------------------------
-- A simple next-measurement selector chooses a separator for the unresolved
-- path question. This is a finite DASHI design fixture, not a universal
-- optimal-experiment theorem.
------------------------------------------------------------------------

nextMeasurement : ResearchQuestion → Suspension.EpistemicDisposition → MeasurementKind
nextMeasurement recoverPathOrder Suspension.suspendAndRefine = sequenceArchive
nextMeasurement recoverPathOrder Suspension.rejectHere = currentStatusOnly
nextMeasurement recoverPathOrder Suspension.acceptHere = currentStatusOnly
nextMeasurement estimatePowerContext Suspension.suspendAndRefine = powerHistoryMeasure
nextMeasurement estimatePowerContext Suspension.rejectHere = currentStatusOnly
nextMeasurement estimatePowerContext Suspension.acceptHere = currentStatusOnly
nextMeasurement estimateConstructionDirection Suspension.suspendAndRefine = symbolicTimingInterview
nextMeasurement estimateConstructionDirection Suspension.rejectHere = currentStatusOnly
nextMeasurement estimateConstructionDirection Suspension.acceptHere = currentStatusOnly

unresolvedPathSelectsSequenceMeasurement :
  nextMeasurement recoverPathOrder Suspension.suspendAndRefine ≡ sequenceArchive
unresolvedPathSelectsSequenceMeasurement = refl

selectedPathMeasurementSeparatesCanonicalHistories :
  measure (nextMeasurement recoverPathOrder Suspension.suspendAndRefine)
    institutionFirstHistory
  ≡ measure (nextMeasurement recoverPathOrder Suspension.suspendAndRefine)
    reinterpretationFirstHistory → ⊥
selectedPathMeasurementSeparatesCanonicalHistories = sequenceArchiveSeparates

------------------------------------------------------------------------
-- The statistical model must retain route if route is needed by the consumer.
------------------------------------------------------------------------

data RouteCollapsedIntoSexCoefficient : Set where

data BinaryDecisionBeforeRefinement : Set where

data AnyExtraMeasurementGuaranteesIdentification : Set where

data SeparatingMeasurementGuaranteesCausalMechanism : Set where

data TernaryRefinementMeansPermanentIndecision : Set where

routeDoesNotCollapseIntoSexCoefficient :
  RouteCollapsedIntoSexCoefficient → ⊥
routeDoesNotCollapseIntoSexCoefficient ()

binaryDecisionShouldNotPreemptRequiredRefinement :
  BinaryDecisionBeforeRefinement → ⊥
binaryDecisionShouldNotPreemptRequiredRefinement ()

anyExtraMeasurementDoesNotGuaranteeIdentification :
  AnyExtraMeasurementGuaranteesIdentification → ⊥
anyExtraMeasurementDoesNotGuaranteeIdentification ()

separatingMeasurementDoesNotGuaranteeCausalMechanism :
  SeparatingMeasurementGuaranteesCausalMechanism → ⊥
separatingMeasurementDoesNotGuaranteeCausalMechanism ()

ternaryRefinementDoesNotMeanPermanentIndecision :
  TernaryRefinementMeansPermanentIndecision → ⊥
ternaryRefinementDoesNotMeanPermanentIndecision ()

------------------------------------------------------------------------
-- Cross-owner regressions.
------------------------------------------------------------------------

binaryHistoricalCollapseStillLosesFineStatus =
  BT.binaryBackwardCollapseCannotRecoverFineStatus

sexLabelStillCannotRecoverConstructionDirection :
  INF.FactorsThrough Stats.recordedSexSurface Stats.relationalCell → ⊥
sexLabelStillCannotRecoverConstructionDirection =
  Stats.recordedSexCannotRecoverConstructionDirection

record SexedHistoricalAdaptiveMeasurementBoundary : Set where
  constructor sexed-historical-adaptive-measurement-boundary
  field
    unresolvedRequiresBinaryCommitment : Bool
    nextMeasurementCanBeQuestionIndexed : Bool
    currentStatusAloneRecoversPath : Bool
    sequenceMeasurementSeparatesCanonicalPaths : Bool
    anyExtraMeasurementGuaranteesIdentification : Bool
    pathIdentificationEqualsCausalMechanism : Bool
    refinementCanTerminateWhenSeparatorArrives : Bool

canonicalSexedHistoricalAdaptiveMeasurementBoundary :
  SexedHistoricalAdaptiveMeasurementBoundary
canonicalSexedHistoricalAdaptiveMeasurementBoundary =
  sexed-historical-adaptive-measurement-boundary
    false true false true false false true
