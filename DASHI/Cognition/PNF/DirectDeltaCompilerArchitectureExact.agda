module DASHI.Cognition.PNF.DirectDeltaCompilerArchitectureExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

-- Existing theorem owners assembled by this constitution.  This module does
-- not replace them; it makes their combined runtime consequence explicit.
import DASHI.Cognition.PNF.DeltaNativePNFDreamFlowExact
import DASHI.Cognition.PNF.FibreSolverDeltaStreamExact
import DASHI.Cognition.PNF.FibreNaturalDeltaTransportExact
import DASHI.Cognition.PNF.SentenceParagraphNaturalDeltaExact
import DASHI.Cognition.PNF.DreamFlowExecutionPlacementExact
import DASHI.Cognition.PNF.DreamFlowRuntimeComplexityExact
import DASHI.Cognition.PNF.FibreLocalTokenAddressExact
import DASHI.Cognition.PNF.FibreLocalPackedStorageExact
import DASHI.Cognition.PNF.PackedNormativeDeltaAuthorityBridgeExact
import DASHI.Cognition.PNF.PackedNormativeSparseAdmissionExact
import DASHI.Cognition.PNF.SparseFibredFrontier
import DASHI.Cognition.PNF.AffectedBoundaryLocalReductionExact
import DASHI.Cognition.PNF.RelationDeltaReconciliationExact

------------------------------------------------------------------------
-- Direct Delta Compiler constitution.
--
-- PostgreSQL is the durable authority boundary, not the internal execution
-- bus.  Parser fibres and local solver state are execution objects.  Durable
-- semantic publication begins only at an explicitly classified persistence
-- cut.  The relational parser projection remains a reference/audit adapter;
-- it is not a mandatory production intermediary.
------------------------------------------------------------------------

data RuntimeDomain : Set where
  executionDomain durableDomain referenceDomain diagnosticDomain : RuntimeDomain

data RuntimeObjectClass : Set where
  executionInterior durableNonAuthority semanticAuthority : RuntimeObjectClass

data PersistenceCut : Set where
  immutableInputCut recoveryArtifactCut semanticStagingCut authorityPublicationCut : PersistenceCut

data PostgreSQLRole : Set where
  durableAuthorityRole globalIdentityRole globalReconciliationRole
    recoveryMetadataRole referenceAuditRole : PostgreSQLRole

data ParserProjectionMode : Set where
  productionDirect parityReference auditDebug : ParserProjectionMode

record PersistenceClassification : Set where
  constructor persistenceClassification
  field
    runtimeDomain : RuntimeDomain
    objectClass : RuntimeObjectClass
    persistenceCut : PersistenceCut
    postgresRole : PostgreSQLRole

open PersistenceClassification public

------------------------------------------------------------------------
-- Physical production laws.
--
-- These are architecture acceptance counters.  They say nothing about the
-- number of reference/audit writes in certification mode; they constrain the
-- mandatory production path only.
------------------------------------------------------------------------

record DirectDeltaPhysicalConstitution : Set where
  constructor directDeltaPhysicalConstitution
  field
    sentenceLocalDBCrossings : Nat
    productionParserTokenWrites : Nat
    unchangedRelationWrites : Nat
    closedChildInteriorReadsByParent : Nat

    sentenceLocalDBCrossingsZero : sentenceLocalDBCrossings ≡ 0
    productionParserTokenWritesZero : productionParserTokenWrites ≡ 0
    unchangedRelationWritesZero : unchangedRelationWrites ≡ 0
    closedChildInteriorReadsZero : closedChildInteriorReadsByParent ≡ 0

open DirectDeltaPhysicalConstitution public

------------------------------------------------------------------------
-- Generation-based staging/publication.
--
-- Candidate semantic work may be durable without being current authority.
-- Consumer visibility changes only through the publication boundary after
-- validation/closure/certification.  This permits resumable short staging
-- transactions without requiring one giant semantic transaction.
------------------------------------------------------------------------

record GenerationPublicationBoundary : Set where
  constructor generationPublicationBoundary
  field
    candidateRowsVisibleBeforePublish : Nat
    publicationTransitions : Nat
    candidateInvisibleBeforePublish : candidateRowsVisibleBeforePublish ≡ 0
    oneAtomicPublicationTransition : publicationTransitions ≡ 1

open GenerationPublicationBoundary public

------------------------------------------------------------------------
-- Direct/reference semantic parity.
--
-- Physical database surrogate ids and execution coordinates are intentionally
-- absent.  The equality is over the declared consumer observation.
------------------------------------------------------------------------

record DirectReferenceParity (Observation : Set) : Set₁ where
  constructor directReferenceParity
  field
    directObservation : Observation
    referenceObservation : Observation
    consumerParity : directObservation ≡ referenceObservation

open DirectReferenceParity public

------------------------------------------------------------------------
-- Naturality of child-to-parent delta transport.
--
-- This is the generic commuting square used by sentence->paragraph and later
-- hierarchy edges.  Existing natural-transport modules provide the concrete
-- instances; this record states the compiler-level obligation once.
------------------------------------------------------------------------

record TransportCommutation
    (ChildState ParentBoundary ChildDelta ParentDelta : Set) : Set₁ where
  field
    applyChild : ChildState → ChildDelta → ChildState
    restrict : ChildState → ParentBoundary
    transport : ChildDelta → ParentDelta
    applyParent : ParentBoundary → ParentDelta → ParentBoundary
    commutes :
      (state : ChildState) →
      (delta : ChildDelta) →
      restrict (applyChild state delta) ≡
        applyParent (restrict state) (transport delta)

open TransportCommutation public

------------------------------------------------------------------------
-- Fixed point means no remaining outward semantic delta, not that an
-- accumulated relational state was rescanned.
------------------------------------------------------------------------

record DirectDeltaFixedPointReceipt : Set where
  constructor directDeltaFixedPointReceipt
  field
    outwardSemanticDeltas : Nat
    fixedPointExact : outwardSemanticDeltas ≡ 0

open DirectDeltaFixedPointReceipt public

------------------------------------------------------------------------
-- Diagnostic plane.
--
-- Diagnostic samples may survive rollback/SIGTERM and may describe partial
-- work.  They never acquire semantic authority merely by being durable.
------------------------------------------------------------------------

record DiagnosticPlaneBoundary : Set where
  constructor diagnosticPlaneBoundary
  field
    durableDiagnosticSamples : Nat
    semanticAuthorityEffects : Nat
    diagnosticAuthorityEffectZero : semanticAuthorityEffects ≡ 0

open DiagnosticPlaneBoundary public

------------------------------------------------------------------------
-- Invalid architectural interpretations are intentionally uninhabited.
------------------------------------------------------------------------

data PostgreSQLIsMandatoryInternalExecutionBus : Set where

data ParserTokenRelationIsMandatoryProductionBus : Set where

data LocalSentenceSolveRequiresPostgreSQL : Set where

data DatabaseSurrogateIsSemanticIdentity : Set where

data ClosedChildInteriorIsOrdinaryParentInput : Set where

data ReconsiderationIsSemanticTransition : Set where

data WholeCompilationMustBeOneTransaction : Set where

data DiagnosticTelemetryIsSemanticAuthority : Set where

data BenchmarkMayRedefineCompilerArchitecture : Set where

postgresIsAuthorityBoundaryNotMandatoryBus :
  PostgreSQLIsMandatoryInternalExecutionBus → ⊥
postgresIsAuthorityBoundaryNotMandatoryBus ()

parserTokenRelationIsReferenceNotMandatoryBus :
  ParserTokenRelationIsMandatoryProductionBus → ⊥
parserTokenRelationIsReferenceNotMandatoryBus ()

localSentenceSolveNeedNotCrossPostgres :
  LocalSentenceSolveRequiresPostgreSQL → ⊥
localSentenceSolveNeedNotCrossPostgres ()

databaseSurrogateIsNotSemanticIdentity :
  DatabaseSurrogateIsSemanticIdentity → ⊥
databaseSurrogateIsNotSemanticIdentity ()

closedChildInteriorIsNotOrdinaryParentInput :
  ClosedChildInteriorIsOrdinaryParentInput → ⊥
closedChildInteriorIsNotOrdinaryParentInput ()

reconsiderationDoesNotManufactureTransition :
  ReconsiderationIsSemanticTransition → ⊥
reconsiderationDoesNotManufactureTransition ()

wholeCompilationNeedNotBeOneTransaction :
  WholeCompilationMustBeOneTransaction → ⊥
wholeCompilationNeedNotBeOneTransaction ()

diagnosticsHaveNoSemanticAuthority :
  DiagnosticTelemetryIsSemanticAuthority → ⊥
diagnosticsHaveNoSemanticAuthority ()

benchmarksPrioritizeButDoNotRedefineArchitecture :
  BenchmarkMayRedefineCompilerArchitecture → ⊥
benchmarksPrioritizeButDoNotRedefineArchitecture ()
