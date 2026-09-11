module DASHI.ComputerScience.RSA260BlockWiedemannProductionScaleReconstructionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.ComputerScience.RSA260SnowballPrimaryAttributionExact as RSA260
import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADO
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Sources

------------------------------------------------------------------------
-- RSA-260 BLOCK-WIEDEMANN PRODUCTION-SCALE RECONSTRUCTION
--
-- This owner records a source-derived parameter reconstruction, not a recovered
-- production matrix or executable revision.
--
-- Primary/public RSA-260 coordinates:
--   rows = 656182601
--   cols = 656182189
--   m=n=512
--   checkpoint interval = 8192
--   reported lingen generator length = 1281607
--   reported final Krylov iteration = 2564096.
--
-- Theory / implementation alignment:
--   ceil(rows / 512) = 1281607
--   CADO README: lingen represents an n x n polynomial matrix of degree
--                ceil(N/n)
--   CADO bw-common.c default Krylov length:
--       ceil(maxDim/m) + ceil(maxDim/n) + 2*ceil(m/n)
--     = 1281607 + 1281607 + 2 = 2563216
--   CADO then rounds length up to a multiple of interval:
--       roundUp_8192(2563216) = 2564096.
--
-- These exact equalities reconstruct the documented PARAMETER RULE from public
-- RSA-260 coordinates.  They do not establish that Lu/Devin ran the inspected
-- stale mirror revision byte-for-byte.
------------------------------------------------------------------------

rsa260Primary : Source.AttributedSource
rsa260Primary = RSA260.rsa260CognitionTechnicalSource

thomeGeneratorPrimary : Source.AttributedSource
thomeGeneratorPrimary =
  Source.mkDOISource
    "Emmanuel Thome"
    "Subquadratic Computation of Vector Generating Polynomials and Improvement of the Block Wiedemann Algorithm"
    "Journal of Symbolic Computation 33(5)"
    "2002"
    "10.1006/jsco.2002.0533"
    "https://doi.org/10.1006/jsco.2002.0533"
    Source.academicArticleSource
    "primary theory source: typical Block-Wiedemann generator/span scale ceil(N/m), sequence scale N/m+N/n+O(1), and generator degree N/n+O(1); not an RSA-260 execution receipt"
    Source.publicAttribution

coppersmithPrimary : Source.AttributedSource
coppersmithPrimary = Sources.coppersmithBlockWiedemannPrimary

cadoSchema : CADO.CADOBlockWiedemannArtifactSchema
cadoSchema = CADO.currentCADOBlockWiedemannArtifactSchema

cadoSnapshot : CADO.CADOReadmeSnapshot
cadoSnapshot = CADO.currentCADOReadmeSnapshot

record ProductionScaleSourceAtlas : Set where
  constructor production-scale-source-atlas
  field
    rsa260ExecutionSource : Source.AttributedSource
    blockWiedemannAlgorithmSource : Source.AttributedSource
    vectorGeneratorTheorySource : Source.AttributedSource
    cadoImplementationSchemaSource : Source.AttributedSource
open ProductionScaleSourceAtlas public

currentProductionScaleSourceAtlas : ProductionScaleSourceAtlas
currentProductionScaleSourceAtlas = production-scale-source-atlas
  rsa260Primary
  coppersmithPrimary
  thomeGeneratorPrimary
  CADO.cadoBWCReadmeMirror

------------------------------------------------------------------------
-- Exact public arithmetic coordinates.
------------------------------------------------------------------------

record ProductionBlockScaleCoordinates : Set where
  constructor production-block-scale-coordinates
  field
    matrixRows : Nat
    matrixColumns : Nat
    blockM : Nat
    blockN : Nat
    checkpointInterval : Nat
    reportedGeneratorLength : Nat
    reportedKrylovEnd : Nat
    rowQuotientBy512 : Nat
    rowRemainderBy512 : Nat
    rowCeilingBy512 : Nat
    columnCeilingBy512 : Nat
    documentedDefaultKrylovLength : Nat
    intervalRoundedKrylovLength : Nat
    roundingSlack : Nat
open ProductionBlockScaleCoordinates public

currentProductionBlockScaleCoordinates : ProductionBlockScaleCoordinates
currentProductionBlockScaleCoordinates = production-block-scale-coordinates
  656182601 656182189
  512 512
  8192
  1281607
  2564096
  1281606
  329
  1281607
  1281606
  2563216
  2564096
  880

------------------------------------------------------------------------
-- Source-paid semantic interpretation.
------------------------------------------------------------------------

record ProductionScaleReconstructionBoundary : Set where
  constructor production-scale-reconstruction-boundary
  field
    reportedGeneratorLengthEqualsCeilRowsOver512 : Bool
    reportedGeneratorLengthEqualsCeilColumnsOver512 : Bool
    thomeTypicalGeneratorScaleMatchesRowCeilingWhenEffectiveDimensionIsRows : Bool
    cadoReadmeDocumentsDegreeCeilNOverN : Bool
    cadoDefaultKrylovFormulaReconstructed : Bool
    cadoIntervalRoundingRuleReconstructed : Bool
    reportedKrylovEndExactlyReproducedByFormulaAndInterval : Bool
    exactProductionCADORevisionRecovered : Bool
    generatorLengthProvedCanonicalMinimalDegree : Bool
    effectiveProductionSquareDimensionProvedToBeRowsByThisOwner : Bool
    formulaReproductionEqualsHistoricalByteReplay : Bool
open ProductionScaleReconstructionBoundary public

canonicalProductionScaleReconstructionBoundary : ProductionScaleReconstructionBoundary
canonicalProductionScaleReconstructionBoundary = production-scale-reconstruction-boundary
  true
  false
  true
  true
  true
  true
  true
  false
  false
  false
  false

------------------------------------------------------------------------
-- Identifier snowball.
------------------------------------------------------------------------

record ProductionScaleIdentityCoordinates : Set where
  constructor production-scale-identity-coordinates
  field
    thomeDOI : String
    coppersmithDOI : String
    generalNumberFieldSieveQID : Sources.IdentifierApplicability
    finiteFieldQID : Sources.IdentifierApplicability
    sparseMatrixQID : Sources.IdentifierApplicability
    blockWiedemannQID : Sources.IdentifierApplicability
    deweyCoordinate : Sources.IdentifierApplicability
    oeisCoordinate : Sources.IdentifierApplicability
open ProductionScaleIdentityCoordinates public

currentProductionScaleIdentityCoordinates : ProductionScaleIdentityCoordinates
currentProductionScaleIdentityCoordinates = production-scale-identity-coordinates
  "10.1006/jsco.2002.0533"
  "10.1090/S0025-5718-1994-1192970-7"
  (Sources.identifierRecorded "Q140770")
  (Sources.identifierRecorded "Q603880")
  (Sources.identifierRecorded "Q1050404")
  Sources.identifierUnresolved
  Sources.identifierUnresolved
  Sources.identifierNotApplicable

------------------------------------------------------------------------
-- New investigative residual.
------------------------------------------------------------------------

data ProductionScaleResidual : Set where
  identifyExactRSA260EffectivePaddedDimension : ProductionScaleResidual
  recoverSameObjectBalancingMetadata : ProductionScaleResidual
  recoverSameObjectGeneratorHeaderOrLengthMetadata : ProductionScaleResidual
  compareProductionScaleAgainstFineIncidencePredictor : ProductionScaleResidual

firstProductionScaleResidual : ProductionScaleResidual
firstProductionScaleResidual = recoverSameObjectGeneratorHeaderOrLengthMetadata

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ExactFormulaMatchImpliesExactRevision : Set where
data ReportedLengthImpliesCanonicalMinimalDegree : Set where
data TypicalTheoryScaleImpliesProductionFineIncidence : Set where
data SourceFormulaReproductionImpliesProductionReplay : Set where

formulaMatchDoesNotCreateExactRevision : ExactFormulaMatchImpliesExactRevision → ⊥
formulaMatchDoesNotCreateExactRevision ()

reportedLengthDoesNotCreateCanonicalMinimalDegree : ReportedLengthImpliesCanonicalMinimalDegree → ⊥
reportedLengthDoesNotCreateCanonicalMinimalDegree ()

typicalScaleDoesNotCreateProductionFineIncidence : TypicalTheoryScaleImpliesProductionFineIncidence → ⊥
typicalScaleDoesNotCreateProductionFineIncidence ()

sourceFormulaDoesNotCreateProductionReplay : SourceFormulaReproductionImpliesProductionReplay → ⊥
sourceFormulaDoesNotCreateProductionReplay ()
