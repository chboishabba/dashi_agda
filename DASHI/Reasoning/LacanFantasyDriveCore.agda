module DASHI.Reasoning.LacanFantasyDriveCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.BraidLearningTransport as Braid
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Reasoning.LacanSignifierSubjectCore as Lacan

------------------------------------------------------------------------
-- Desire, drive and fantasy remain distinct typed relations.
------------------------------------------------------------------------

record FantasyFrame : Set₁ where
  field
    subject : Lacan.BarredSubject
    cause : Lacan.CandidateObjetA
    relationLabel : String
    navigableClosureProduced : Bool
    originatingResidualEliminatedClaimed : Bool
    fantasyEqualsVerifiedWorldModelClaimed : Bool
    fantasyReceipt : String

record DesireTraversal : Set₁ where
  field
    currentSignifier nextSignifier : PNF.EventPNF
    causePosition : Lacan.CandidateObjetA
    metonymicShiftReceipt : String
    targetConsumptionTerminatesDesireClaimed : Bool
    finalSatisfactionProved : Bool

record DriveOrbitCandidate : Set₁ where
  field
    stateEvent : PNF.EventPNF
    retainedCause : Lacan.CandidateObjetA
    recurrentBraid : Braid.BraidOrderReceipt
    versionedMemory : Memory.VersionedMemory
    repetitionReceipt : String
    partialSatisfactionLabel : String
    terminalObjectReachedClaimed : Bool
    fixedPointTheoremClaimed : Bool

record DesireDriveDistinction : Set where
  field
    desireMovesAlongSignifierChain : Bool
    driveCirclesCausePosition : Bool
    desireEqualsNeed : Bool
    driveEqualsDynamicalFixedPoint : Bool
    repetitionAutomaticallyPathological : Bool
    distinctionReceipt : String

canonicalDesireDriveDistinction : DesireDriveDistinction
canonicalDesireDriveDistinction = record
  { desireMovesAlongSignifierChain = true
  ; driveCirclesCausePosition = true
  ; desireEqualsNeed = false
  ; driveEqualsDynamicalFixedPoint = false
  ; repetitionAutomaticallyPathological = false
  ; distinctionReceipt =
      "Desire is represented by signifier displacement; drive by recurrent transport around a retained cause-position. Neither is promoted to a biological mechanism."
  }

record LacanFantasyDriveAuthorityBoundary : Set where
  field
    fantasyRelationEliminatesGap : Bool
    objetAOrdinaryTarget : Bool
    desireFinalObjectGuaranteed : Bool
    driveOrbitIsAnalyticAttractorTheorem : Bool
    braidOrderCrossPollinated : Bool
    versionedMemoryCrossPollinated : Bool
    clinicalDiagnosisPromoted : Bool
    boundaryNote : String

canonicalLacanFantasyDriveAuthorityBoundary :
  LacanFantasyDriveAuthorityBoundary
canonicalLacanFantasyDriveAuthorityBoundary = record
  { fantasyRelationEliminatesGap = false
  ; objetAOrdinaryTarget = false
  ; desireFinalObjectGuaranteed = false
  ; driveOrbitIsAnalyticAttractorTheorem = false
  ; braidOrderCrossPollinated = true
  ; versionedMemoryCrossPollinated = true
  ; clinicalDiagnosisPromoted = false
  ; boundaryNote =
      "Fantasy, desire and drive are structural relations over PNF, braid and memory carriers; they do not diagnose a person or prove a physical attractor."
  }
