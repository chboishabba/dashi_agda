module DASHI.ComputerScience.RSA260BidiProductionAStarDiagnosticAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String public using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADO
import DASHI.ComputerScience.RSA260BidiProjectionFreezeObservableExact as Freeze
import DASHI.ComputerScience.RSA260BidiProjectionIndexedGeneratorSignatureExact as Signature

------------------------------------------------------------------------
-- RSA-260 BIDI PRODUCTION A* DIAGNOSTIC ADAPTER
--
-- CADO's documented BWC schema names Krylov sequence artifacts as
--
--   wdir/A<n1>-<n2>.<j1>-<j2>.
--
-- This owner compiles custody states into consumer-specific diagnostic
-- admissions.  It does NOT claim that any same-object RSA-260 A* bytes have
-- been acquired.  Filename schema, same-object identity, byte custody, and
-- projection-pair custody remain separate payments.
------------------------------------------------------------------------

cadoArtifactSchema : CADO.CADOBlockWiedemannArtifactSchema
cadoArtifactSchema = CADO.currentCADOBlockWiedemannArtifactSchema

productionAStarPattern : String
productionAStarPattern = CADO.krylovSequencePattern cadoArtifactSchema

signatureBoundary : Signature.ProjectionIndexedGeneratorBoundary
signatureBoundary = Signature.canonicalProjectionIndexedGeneratorBoundary

------------------------------------------------------------------------
-- Sequence-only same-object custody.
------------------------------------------------------------------------

record SameObjectProjectedSequenceCustody : Set where
  constructor same-object-projected-sequence-custody
  field
    artifactPath : String
    sameObjectRSA260Identity : Bool
    sequenceBytesAvailable : Bool
    sourceObjectIdentityBound : Bool

    sameObjectIdentityPaid : sameObjectRSA260Identity ≡ true
    sequenceBytesPaid : sequenceBytesAvailable ≡ true
    sourceObjectBindingPaid : sourceObjectIdentityBound ≡ true
open SameObjectProjectedSequenceCustody public

record SequenceRelativeDiagnosticAdmission
    (receipt : SameObjectProjectedSequenceCustody) : Set where
  constructor sequence-relative-diagnostic-admission
  field
    realizedProjectedDegreeAdmitted : Bool
    realizedHankelProfileAdmitted : Bool
    finiteHorizonRankDiagnosticAdmitted : Bool
    dynamicReachableRankDiagnosticAdmitted : Bool

    degreeAdmissionPaid : realizedProjectedDegreeAdmitted ≡ true
    hankelAdmissionPaid : realizedHankelProfileAdmitted ≡ true
    finiteHorizonAdmissionPaid : finiteHorizonRankDiagnosticAdmitted ≡ true
    dynamicRankAdmissionPaid : dynamicReachableRankDiagnosticAdmitted ≡ true
open SequenceRelativeDiagnosticAdmission public

sequenceCustodyPaysSequenceRelativeDiagnostics :
  (receipt : SameObjectProjectedSequenceCustody) →
  SequenceRelativeDiagnosticAdmission receipt
sequenceCustodyPaysSequenceRelativeDiagnostics receipt =
  sequence-relative-diagnostic-admission
    true true true true
    refl refl refl refl

------------------------------------------------------------------------
-- Projection-pair custody is an additional grade, not a prerequisite for
-- measuring diagnostics from the sequence bytes themselves.
------------------------------------------------------------------------

record SameObjectProjectedSequenceWithPairCustody : Set where
  constructor same-object-projected-sequence-with-pair-custody
  field
    sequenceCustody : SameObjectProjectedSequenceCustody
    xProjectionIdentityAvailable : Bool
    yProjectionIdentityAvailable : Bool
    projectionFreeze : Freeze.ProjectionPairFreezeReceipt

    xProjectionIdentityPaid : xProjectionIdentityAvailable ≡ true
    yProjectionIdentityPaid : yProjectionIdentityAvailable ≡ true
open SameObjectProjectedSequenceWithPairCustody public

record ControlledProjectionDiagnosticAdmission
    (receipt : SameObjectProjectedSequenceWithPairCustody) : Set where
  constructor controlled-projection-diagnostic-admission
  field
    reproduceOriginalProjectionAdmitted : Bool
    projectionGeometryExplanationAdmitted : Bool
    controlledCrossProjectionComparisonAdmitted : Bool

    reproductionAdmissionPaid : reproduceOriginalProjectionAdmitted ≡ true
    projectionGeometryAdmissionPaid : projectionGeometryExplanationAdmitted ≡ true
    controlledComparisonAdmissionPaid :
      controlledCrossProjectionComparisonAdmitted ≡ true
open ControlledProjectionDiagnosticAdmission public

projectionPairCustodyPaysControlledDiagnostics :
  (receipt : SameObjectProjectedSequenceWithPairCustody) →
  ControlledProjectionDiagnosticAdmission receipt
projectionPairCustodyPaysControlledDiagnostics receipt =
  controlled-projection-diagnostic-admission
    true true true
    refl refl refl

------------------------------------------------------------------------
-- Current acquisition state remains unpaid.
------------------------------------------------------------------------

record CurrentProductionAStarAcquisitionState : Set where
  constructor current-production-astar-acquisition-state
  field
    sameObjectAStarBytesLocated : Bool
    sameObjectAStarIdentityAuthenticated : Bool
    xProjectionIdentityRecovered : Bool
    yProjectionIdentityRecovered : Bool
    exactExecutedRevisionRecovered : Bool
open CurrentProductionAStarAcquisitionState public

currentProductionAStarAcquisitionState : CurrentProductionAStarAcquisitionState
currentProductionAStarAcquisitionState =
  current-production-astar-acquisition-state
    false false false false false

------------------------------------------------------------------------
-- Boundary and live roadmap.
------------------------------------------------------------------------

record ProductionAStarAdapterBoundary : Set where
  constructor production-astar-adapter-boundary
  field
    cadoAStarFilenameSchemaPaid : Bool
    sequenceCustodyCompilerPaid : Bool
    projectionPairCustodyCompilerPaid : Bool
    sequenceOnlyCustodySufficesForOwnDegreeDiagnostic : Bool
    sequenceOnlyCustodySufficesForOwnHankelDiagnostic : Bool
    projectionPairNeededForControlledComparison : Bool
    sameObjectAStarBytesCurrentlyPaid : Bool
    sameObjectAStarIdentityCurrentlyPaid : Bool
    projectionPairCurrentlyPaid : Bool
    productionAStarDiagnosticExecuted : Bool
    adapterCreatesMissingBytes : Bool
    filenameSchemaCreatesSameObjectIdentity : Bool
open ProductionAStarAdapterBoundary public

canonicalProductionAStarAdapterBoundary : ProductionAStarAdapterBoundary
canonicalProductionAStarAdapterBoundary =
  production-astar-adapter-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false

data ProductionAStarAdapterResidual : Set where
  acquireSameObjectProjectedAStarBytes : ProductionAStarAdapterResidual
  authenticateSameObjectAStarIdentity : ProductionAStarAdapterResidual
  computeSequenceRelativeDegreeHankelAndFiniteHorizonDiagnostics : ProductionAStarAdapterResidual
  recoverProjectionPairForReproductionAndControlledComparison : ProductionAStarAdapterResidual
  compareProductionSignatureAgainstFrozenSyntheticPortfolio : ProductionAStarAdapterResidual
  acquireSameObjectFSolsIfAStarUnavailable : ProductionAStarAdapterResidual

firstProductionAStarAdapterResidual : ProductionAStarAdapterResidual
firstProductionAStarAdapterResidual = acquireSameObjectProjectedAStarBytes

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data CADOFilenameMeansSameObjectRSA260Artifact : Set where
data AdapterCompilerMeansArtifactAcquired : Set where
data SequenceOnlyCustodyMeansProjectionReproducible : Set where
data ProjectionPairCustodyMeansExactExecutedRevision : Set where

cadoFilenameDoesNotCreateSameObjectArtifact :
  CADOFilenameMeansSameObjectRSA260Artifact → ⊥
cadoFilenameDoesNotCreateSameObjectArtifact ()

adapterCompilerDoesNotAcquireArtifact : AdapterCompilerMeansArtifactAcquired → ⊥
adapterCompilerDoesNotAcquireArtifact ()

sequenceOnlyCustodyDoesNotCreateProjectionReproduction :
  SequenceOnlyCustodyMeansProjectionReproducible → ⊥
sequenceOnlyCustodyDoesNotCreateProjectionReproduction ()

projectionPairCustodyDoesNotCreateExecutedRevision :
  ProjectionPairCustodyMeansExactExecutedRevision → ⊥
projectionPairCustodyDoesNotCreateExecutedRevision ()
