module DASHI.ComputerScience.RSA260BidiCADOGridPermutationCrossValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADO
import DASHI.ComputerScience.RSA260BidiRandomIncidenceCarrierCrossValidationExact as RandomIncidence

------------------------------------------------------------------------
-- SOURCE-DERIVED CADO GRID-PERMUTATION CROSS-VALIDATION
--
-- CADO's historical BWC README documents a block-grid transpose permutation
-- after square padding.  The exact RSA-260 balancing file is not public in the
-- admitted source set, so this experiment tests the documented permutation
-- SHAPE on the 512-state intermediate carrier used by the executable shadow.
--
-- Canonical cyclic carrier:
--   grids 2x2, 4x2, 4x4, 8x4, 16x4, 4x8
--   two independent projection seeds each
--   all 12 runs recover the declared kernel consumer, d in {16,17}.
--
-- Random fine-incidence carriers:
--   carrier seeds 260001 and 260003
--   source-shaped grids 4x4 and 8x4
--   all four runs recover the consumer only at d in {65,66}.
--
-- Therefore the CADO-shaped balancing permutation does not explain away the
-- recurrence-complexity jump caused by changing fine incidence geometry.
------------------------------------------------------------------------

cadoArtifactSchema : CADO.CADOBlockWiedemannArtifactSchema
cadoArtifactSchema = CADO.currentCADOBlockWiedemannArtifactSchema

cadoBalancingSchema : CADO.CADOBalancingPermutationSchema
cadoBalancingSchema = CADO.canonicalCADOBalancingPermutationSchema

randomIncidenceBoundary : RandomIncidence.RandomIncidenceInterpretationBoundary
randomIncidenceBoundary = RandomIncidence.canonicalRandomIncidenceInterpretationBoundary

record CADOGridRuntimeSource : Set where
  constructor cado-grid-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    dependencyPath : String
    dependencyGitBlob : String
    cadoReadmeMirrorCommit : String
    cadoReadmeMirrorBlob : String
    exactRuntimeBlobExecuted : Bool
    exactDependencyBlobExecuted : Bool
open CADOGridRuntimeSource public

currentCADOGridRuntimeSource : CADOGridRuntimeSource
currentCADOGridRuntimeSource = cado-grid-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_cado_grid_permutation_crossvalidation.py"
  "8bda894aa6a31ff5467e5d8484cefcb05559a4c3"
  "5c07cb16a4b1f64121eb7abd2f2e0c25227c8e64"
  "rsa260_bidi_candidate_robustness.py"
  "0f60c28f01b50c2337f2e5dec0016f918119371d"
  "792169c33c26d05a4f7c90e91584285133ea5c55"
  "34b029d2ab166fa2d400dd13351e2d31adc8952d"
  true
  true

record CADOGridCrossValidationReceipt : Set where
  constructor cado-grid-cross-validation-receipt
  field
    carrierRows : Nat
    carrierColumns : Nat
    sourceShapedCanonicalGridFamilies : Nat
    projectionSeedsPerCanonicalGrid : Nat
    canonicalRuns : Nat
    canonicalRunsAdmitted : Nat
    canonicalMinimumGeneratorDegree : Nat
    canonicalMaximumGeneratorDegree : Nat
    canonicalZeroShiftRelationsObserved : Nat
    randomFineIncidenceCarriers : Nat
    randomSourceShapedGridFamiliesPerCarrier : Nat
    randomizedRuns : Nat
    randomizedRunsAdmitted : Nat
    randomizedMinimumGeneratorDegree : Nat
    randomizedMaximumGeneratorDegree : Nat
    randomizedAllShiftedRanks512 : Bool
    exactProductionBalancingFileRecovered : Bool
    exactRSA260CADORevisionRecovered : Bool
open CADOGridCrossValidationReceipt public

currentCADOGridCrossValidationReceipt : CADOGridCrossValidationReceipt
currentCADOGridCrossValidationReceipt = cado-grid-cross-validation-receipt
  924 512
  6 2
  12 12
  16 17
  1
  2 2
  4 4
  65 66
  true
  false false

record CADOGridInterpretationBoundary : Set where
  constructor cado-grid-interpretation-boundary
  field
    sourceDerivedGridShapePreservesCanonicalConsumer : Bool
    sourceDerivedGridShapePreservesRandomCarrierConsumer : Bool
    sourceDerivedGridShapeCollapsesRandomCarrierDegreeToCyclicRange : Bool
    fineIncidenceStillSeparatesRecurrenceComplexity : Bool
    cadoReadmeMirrorEqualsExactRSA260Revision : Bool
    documentedPermutationShapeEqualsRecoveredBalancingFile : Bool
    sourceShapedExperimentIdentifiesHistoricalMatrix : Bool
open CADOGridInterpretationBoundary public

canonicalCADOGridInterpretationBoundary : CADOGridInterpretationBoundary
canonicalCADOGridInterpretationBoundary = cado-grid-interpretation-boundary
  true
  true
  false
  true
  false
  false
  false

------------------------------------------------------------------------
-- Highest-alpha residual after the source-derived preparation check.
------------------------------------------------------------------------

data CADOGridResidual : Set where
  deriveFineIncidencePredictorForGeneratorDegree : CADOGridResidual
  searchSameObjectBalancingFileByDocumentedFilename : CADOGridResidual
  searchSameObjectKrylovAArtifactsByDocumentedFilename : CADOGridResidual
  searchSameObjectGeneratorFArtifactsByDocumentedFilename : CADOGridResidual
  searchSameObjectKernelWArtifactsByDocumentedFilename : CADOGridResidual

firstCADOGridResidual : CADOGridResidual
firstCADOGridResidual = deriveFineIncidencePredictorForGeneratorDegree

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data DocumentedGridShapeImpliesExactBalancing : Set where
data SourceShapedPermutationImpliesProductionReplay : Set where
data SameCoarseContractImpliesSameRecurrence : Set where

documentedGridShapeDoesNotCreateExactBalancing : DocumentedGridShapeImpliesExactBalancing → ⊥
documentedGridShapeDoesNotCreateExactBalancing ()

sourceShapedPermutationDoesNotCreateProductionReplay : SourceShapedPermutationImpliesProductionReplay → ⊥
sourceShapedPermutationDoesNotCreateProductionReplay ()

sameCoarseContractDoesNotCreateSameRecurrence : SameCoarseContractImpliesSameRecurrence → ⊥
sameCoarseContractDoesNotCreateSameRecurrence ()
