module DASHI.ComputerScience.RSA260BidiMksolConsumerProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADO
import DASHI.ComputerScience.RSA260BidiProductionGeneratorResidualAdapterExact as Generator
import DASHI.ComputerScience.RSA260BidiRankObserverGrowthStressExact as RankStress

------------------------------------------------------------------------
-- MKSOL-RELATIVE GENERATOR CONSUMER
--
-- Source-bounded CADO implementation schema:
--   * lingen creates F.sols*;
--   * mksol reads F.sols* and V<n1>-<n2>.0;
--   * mksol performs matrix-times-vector work and creates S.sols* partials;
--   * gather sums the S* files and advances M until a kernel vector is found.
--
-- Consequence for the untangling programme:
--
-- exact receipt identity is not the primitive downstream consumer.  The mksol
-- consumer needs a representation that preserves the generator evaluation used
-- together with the initial V / prepared operator context.  A rank sketch may
-- remain a cheap diagnostic, but cannot enter the adequate stratum merely by
-- separating a finite set of generator names.
------------------------------------------------------------------------

cadoSchema : CADO.CADOBlockWiedemannArtifactSchema
cadoSchema = CADO.currentCADOBlockWiedemannArtifactSchema

cadoGeneratorPattern : String
cadoGeneratorPattern = CADO.generatorPattern cadoSchema

cadoInitialVPattern : String
cadoInitialVPattern = CADO.initialVPattern cadoSchema

cadoMksolPattern : String
cadoMksolPattern = CADO.mksolSequencePattern cadoSchema

rankGrowthBoundary : RankStress.RankObserverGrowthStressBoundary
rankGrowthBoundary = RankStress.canonicalRankObserverGrowthStressBoundary

------------------------------------------------------------------------
-- Consumer projection.
------------------------------------------------------------------------

data GeneratorConsumer : Set where
  syntheticReceiptIdentity : GeneratorConsumer
  mksolGeneratorEvaluation : GeneratorConsumer
  exactCoefficientReplay : GeneratorConsumer

record MksolConsumerInputs : Set₁ where
  constructor mksol-consumer-inputs
  field
    GeneratorState : Set
    Representation : Set
    InitialVState : Set
    PreparedOperatorState : Set
    SolutionRange : Set
    PartialSolutionState : Set

    representGenerator : GeneratorState -> Representation

    evaluateFull :
      GeneratorState ->
      InitialVState ->
      PreparedOperatorState ->
      SolutionRange ->
      PartialSolutionState

    evaluateRepresentation :
      Representation ->
      InitialVState ->
      PreparedOperatorState ->
      SolutionRange ->
      PartialSolutionState

    representationPreservesMksolEvaluation :
      (generator : GeneratorState) ->
      (v : InitialVState) ->
      (operator : PreparedOperatorState) ->
      (solutions : SolutionRange) ->
      evaluateFull generator v operator solutions
      ≡ evaluateRepresentation
          (representGenerator generator)
          v operator solutions
open MksolConsumerInputs public

------------------------------------------------------------------------
-- A same-object generator residual can supply coefficient semantics, but it
-- still does not manufacture the V / prepared-operator inputs required by the
-- actual mksol consumer.
------------------------------------------------------------------------

record MksolProductionAdmission : Set where
  constructor mksol-production-admission
  field
    generatorResidualCustodyPaid : Bool
    generatorEvaluationSemanticsPaid : Bool
    sameObjectInitialVPaid : Bool
    sameObjectPreparedOperatorPaid : Bool
    solutionRangePaid : Bool
    mksolEvaluationPreservationPaid : Bool
    partialSolsProduced : Bool
open MksolProductionAdmission public

currentMksolProductionAdmission : MksolProductionAdmission
currentMksolProductionAdmission =
  mksol-production-admission
    false false false false false false false

------------------------------------------------------------------------
-- Consumer-relative reading of the rank-fingerprint experiments.
------------------------------------------------------------------------

record RankSketchMksolReading : Set where
  constructor rank-sketch-mksol-reading
  field
    rankSketchUsefulAsCheapDiagnostic : Bool
    finiteReceiptSeparationEqualsMksolAdequacy : Bool
    receiptSHAIdentityPrimitiveMksolInput : Bool
    degreeAndRankCoordinatesPrimitiveMksolInput : Bool
    exactCoefficientReplayCanSupportMksolSemanticsAfterAuthentication : Bool
    smallerRepresentationMayBeMksolAdequateIfEvaluationPreserved : Bool
    evaluationPreservationTheoremCurrentlyPaidForRankSketch : Bool
open RankSketchMksolReading public

canonicalRankSketchMksolReading : RankSketchMksolReading
canonicalRankSketchMksolReading =
  rank-sketch-mksol-reading
    true
    false
    false
    false
    true
    true
    false

------------------------------------------------------------------------
-- Boundary / next residual.
------------------------------------------------------------------------

record MksolConsumerProjectionBoundary : Set where
  constructor mksol-consumer-projection-boundary
  field
    cadoGeneratorArtifactSchemaPaid : Bool
    cadoInitialVArtifactSchemaPaid : Bool
    cadoMksolOutputSchemaPaid : Bool
    mksolReadsGeneratorAndInitialV : Bool
    mksolRequiresPreparedMatrixVectorAction : Bool
    gatherConsumesMksolPartials : Bool
    finiteReceiptIdentityIsPrimitiveMksolConsumer : Bool
    rankFingerprintIsPrimitiveMksolConsumer : Bool
    exactGeneratorActionIsConsumerRelevant : Bool
    consumerAdequateCompressionMayIgnoreReceiptIdentity : Bool
    representationMustProveMksolEvaluationPreservation : Bool
    currentRankSketchPaysEvaluationPreservation : Bool
    currentProductionMksolAdmissionPaid : Bool
open MksolConsumerProjectionBoundary public

canonicalMksolConsumerProjectionBoundary : MksolConsumerProjectionBoundary
canonicalMksolConsumerProjectionBoundary =
  mksol-consumer-projection-boundary
    true true true true true true
    false false true true true false false

data MksolConsumerProjectionResidual : Set where
  defineSyntheticMksolEvaluationConsumer : MksolConsumerProjectionResidual
  testHybridReplayCodecAgainstMksolEvaluation : MksolConsumerProjectionResidual
  searchForStrictlyCoarserEvaluationPreservingGeneratorRepresentation : MksolConsumerProjectionResidual
  bindSameObjectInitialVAndPreparedOperatorForProduction : MksolConsumerProjectionResidual
  executeIndependentMksol : MksolConsumerProjectionResidual
  feedGatherAndVerifyKernel : MksolConsumerProjectionResidual

firstMksolConsumerProjectionResidual : MksolConsumerProjectionResidual
firstMksolConsumerProjectionResidual = defineSyntheticMksolEvaluationConsumer
