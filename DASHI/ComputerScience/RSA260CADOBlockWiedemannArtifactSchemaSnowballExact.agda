module DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Sources

------------------------------------------------------------------------
-- CADO-NFS BLOCK-WIEDEMANN ARTIFACT-SCHEMA SNOWBALL
--
-- The official INRIA GitLab is the canonical project location, but direct
-- inspection was blocked by its anti-bot front end in the current acquisition
-- environment.  We therefore bind the implementation-schema observations to a
-- public GitHub mirror snapshot and keep that source role explicit.
--
-- The README itself warns that it is not regularly checked to be up to date.
-- Consequently this module pays file/parameter naming and historical
-- implementation-schema coordinates only.  It does NOT identify the exact
-- RSA-260 checkout or prove that Lu/Devin retained every standard artifact.
------------------------------------------------------------------------

cadoBWCReadmeMirror : Source.AttributedSource
cadoBWCReadmeMirror =
  Source.mkNoDOISource
    "CADO-NFS Development Team; public mirror snapshot maintained by Michael Bell"
    "linalg/bwc/README"
    "CADO-NFS source-tree implementation documentation (public GitHub mirror)"
    "snapshot 2021; README update notes through 2016"
    "https://github.com/MichaelBell/cado-nfs/blob/792169c33c26d05a4f7c90e91584285133ea5c55/linalg/bwc/README"
    Source.softwareSource
    "implementation-schema evidence for BWC inputs, files, parameters, balancing/permutation and step ownership; README explicitly warns it may be stale"
    Source.publicAttribution

record CADOReadmeSnapshot : Set where
  constructor cado-readme-snapshot
  field
    canonicalProjectURL : String
    directlyInspectedCanonicalGitLabREADME : Bool
    mirrorRepository : String
    mirrorCommit : String
    readmePath : String
    readmeBlob : String
    readmeWarnsNotRegularlyUpToDate : Bool
open CADOReadmeSnapshot public

currentCADOReadmeSnapshot : CADOReadmeSnapshot
currentCADOReadmeSnapshot = cado-readme-snapshot
  "https://gitlab.inria.fr/cado-nfs/cado-nfs"
  false
  "MichaelBell/cado-nfs"
  "792169c33c26d05a4f7c90e91584285133ea5c55"
  "linalg/bwc/README"
  "34b029d2ab166fa2d400dd13351e2d31adc8952d"
  true

------------------------------------------------------------------------
-- Source-paid BWC carrier/file schema.
------------------------------------------------------------------------

record CADOBlockWiedemannArtifactSchema : Set where
  constructor cado-block-wiedemann-artifact-schema
  field
    matrixInputBinaryPattern : String
    matrixBinaryEncoding : String
    rowWeightCompanionPattern : String
    columnWeightCompanionPattern : String
    balancingPattern : String
    initialXPattern : String
    initialVPattern : String
    krylovSequencePattern : String
    generatorPattern : String
    mksolSequencePattern : String
    gatheredKernelPattern : String
    binarySplitWidth : Nat
    prepSelectsInitialBlocks : Bool
    secureProducesCheckData : Bool
    krylovProducesSequence : Bool
    lingenProducesGenerator : Bool
    mksolProducesSolutionSequence : Bool
    gatherProducesKernelVectors : Bool
    leftNullspaceUsesTransposeOperation : Bool
    globalMAndNExpectedMultiplesOf64 : Bool
    multipleIndependentSequencesSumIntoGlobalN : Bool
open CADOBlockWiedemannArtifactSchema public

currentCADOBlockWiedemannArtifactSchema : CADOBlockWiedemannArtifactSchema
currentCADOBlockWiedemannArtifactSchema = cado-block-wiedemann-artifact-schema
  "[PREFIX].bin"
  "headerless rows: uint32-LE row length followed by uint32-LE nonzero column indices"
  "[PREFIX].rw.bin"
  "[PREFIX].cw.bin"
  "wdir/mat.<nh>x<nv>[.<bchecksum>].bin"
  "wdir/X0-<splitwidth>"
  "wdir/V<n1>-<n2>.0"
  "wdir/A<n1>-<n2>.<j1>-<j2>"
  "wdir/F.sols<s1>-<s2>.<j1>-<j2>"
  "wdir/S.sols<s1>-<s2>.<n1>-<n2>"
  "wdir/W and W.sols/K.sols variants"
  64
  true true true true true true
  true true true

------------------------------------------------------------------------
-- Documented balancing/permutation shape.
------------------------------------------------------------------------

record CADOBalancingPermutationSchema : Set where
  constructor cado-balancing-permutation-schema
  field
    squarePaddingDocumented : Bool
    paddedDimensionMultipleOfGridProduct : Bool
    gridCoordinatesDocumented : Bool
    blockTransposeShapeDocumented : Bool
    exactDirectionFixedByThisREADMEText : Bool
    balancingFileEqualsRSA260BalancingFile : Bool
open CADOBalancingPermutationSchema public

canonicalCADOBalancingPermutationSchema : CADOBalancingPermutationSchema
canonicalCADOBalancingPermutationSchema = cado-balancing-permutation-schema
  true true true true false false

------------------------------------------------------------------------
-- Snowball identity coordinates.
------------------------------------------------------------------------

record CADOArtifactSnowballCoordinates : Set where
  constructor cado-artifact-snowball-coordinates
  field
    generalNumberFieldSieveQID : Sources.IdentifierApplicability
    sparseMatrixQID : Sources.IdentifierApplicability
    finiteFieldQID : Sources.IdentifierApplicability
    blockWiedemannQID : Sources.IdentifierApplicability
    deweyCoordinate : Sources.IdentifierApplicability
    oeisCoordinate : Sources.IdentifierApplicability
open CADOArtifactSnowballCoordinates public

currentCADOArtifactSnowballCoordinates : CADOArtifactSnowballCoordinates
currentCADOArtifactSnowballCoordinates = cado-artifact-snowball-coordinates
  (Sources.identifierRecorded "Q140770")
  (Sources.identifierRecorded "Q1050404")
  (Sources.identifierRecorded "Q603880")
  Sources.identifierUnresolved
  Sources.identifierUnresolved
  Sources.identifierNotApplicable

------------------------------------------------------------------------
-- Acquisition consequence: exact file classes can now be searched directly.
------------------------------------------------------------------------

data CADOArtifactSearchTarget : Set where
  inputMatrixBinary : CADOArtifactSearchTarget
  balancingPermutation : CADOArtifactSearchTarget
  initialProjectionX : CADOArtifactSearchTarget
  initialKrylovV : CADOArtifactSearchTarget
  krylovSequenceA : CADOArtifactSearchTarget
  lingenGeneratorF : CADOArtifactSearchTarget
  mksolSequenceS : CADOArtifactSearchTarget
  gatheredKernelW : CADOArtifactSearchTarget

firstHighValueArtifactSearchTarget : CADOArtifactSearchTarget
firstHighValueArtifactSearchTarget = gatheredKernelW

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data MirrorSchemaImpliesExactRSA260Revision : Set where
data StandardFilenameImpliesSameObjectArtifact : Set where
data ReadmePermutationImpliesRecoveredBalancingFile : Set where
data QIDImpliesSourceAuthority : Set where

mirrorSchemaDoesNotCreateExactRSA260Revision : MirrorSchemaImpliesExactRSA260Revision → ⊥
mirrorSchemaDoesNotCreateExactRSA260Revision ()

standardFilenameDoesNotCreateSameObjectArtifact : StandardFilenameImpliesSameObjectArtifact → ⊥
standardFilenameDoesNotCreateSameObjectArtifact ()

readmePermutationDoesNotCreateRecoveredBalancingFile : ReadmePermutationImpliesRecoveredBalancingFile → ⊥
readmePermutationDoesNotCreateRecoveredBalancingFile ()

qidDoesNotCreateSourceAuthority : QIDImpliesSourceAuthority → ⊥
qidDoesNotCreateSourceAuthority ()
