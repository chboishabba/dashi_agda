module DASHI.Reasoning.FaithfulRepetitionCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.BraidLearningTransport as Braid
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Remembering, repetition and working-through.
--
-- Fidelity is attached to a preserved problem relation and a residual-bearing
-- revision, not to literal equality of historical actions.
------------------------------------------------------------------------

record HistoricalEvent
  (Problem Context Action Residual : Set) : Set₁ where
  field
    problem : Problem
    context : Context
    action : Action
    residual : Residual

record ProblemEquivalence (Problem : Set) : Set₁ where
  field
    EquivalentProblem : Problem → Problem → Set
    reflexive : ∀ problem → EquivalentProblem problem problem
    symmetric :
      ∀ {left right} →
      EquivalentProblem left right →
      EquivalentProblem right left
    transitive :
      ∀ {first second third} →
      EquivalentProblem first second →
      EquivalentProblem second third →
      EquivalentProblem first third

record FaithfulRepetition
  (Problem Context Action Residual : Set)
  (problemEquivalence : ProblemEquivalence Problem) : Set₁ where
  field
    source target : HistoricalEvent Problem Context Action Residual
    problemPreserved :
      ProblemEquivalence.EquivalentProblem problemEquivalence
        (HistoricalEvent.problem source)
        (HistoricalEvent.problem target)
    contextChangeReceipt : String
    priorResidualConstrainsNewAction : Residual → Action → Set
    workingThroughWitness :
      priorResidualConstrainsNewAction
        (HistoricalEvent.residual source)
        (HistoricalEvent.action target)
    literalActionCopyRequired : Bool
    oldFailureErased : Bool

record PNFFaithfulRepetition : Set₁ where
  field
    sourceProblem targetProblem : PNF.EventPNF
    sourceResidual targetResidual : Residual.ResidualLevel
    problemShapePreserved : Bool
    contextChanged : Bool
    revision : PNF.PNFRevision
    versionedMemory : Memory.VersionedMemory
    braidOrderReceipt : Braid.BraidOrderReceipt
    oldVersionRetained : Bool
    oldResidualUsedAsConstraint : Bool
    literalHistoricalActionCopied : Bool
    repetitionReceipt : String

record WorkingThroughTransition : Set₁ where
  field
    rememberedProblem : PNF.EventPNF
    currentProblem : PNF.EventPNF
    revisedAction : PNF.EventPNF
    retainedMemory : Memory.VersionedMemory
    boundaryBefore : Residual.ResidualLevel
    boundaryAfter : Residual.ResidualLevel
    revisionReceipt : PNF.PNFRevision
    resistanceOrResidualConsumedAsEvidence : Bool
    actionEqualityRequired : Bool
    unresolvedResidualRetained : Bool

record RepetitionAuthorityBoundary : Set where
  field
    rememberingIsRetrieval : Bool
    repetitionIsLiteralCopy : Bool
    workingThroughConsumesResidual : Bool
    problemPreservationRequired : Bool
    memoryAndBraidReceiptsIntegrated : Bool
    politicalSuccessGuaranteed : Bool
    clinicalAuthorityPromoted : Bool
    boundaryNote : String

canonicalRepetitionAuthorityBoundary : RepetitionAuthorityBoundary
canonicalRepetitionAuthorityBoundary = record
  { rememberingIsRetrieval = true
  ; repetitionIsLiteralCopy = false
  ; workingThroughConsumesResidual = true
  ; problemPreservationRequired = true
  ; memoryAndBraidReceiptsIntegrated = true
  ; politicalSuccessGuaranteed = false
  ; clinicalAuthorityPromoted = false
  ; boundaryNote =
      "Faithful repetition preserves a problem relation and lets retained failure constrain a context-changed action; it does not require restoration."
  }
