module DASHI.ComputerScience.RSA260BidiCADOMksolContextFamilyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADO
import DASHI.ComputerScience.RSA260GNFSRunParameterArtifactSnowballExact as Run
import DASHI.ComputerScience.RSA260BidiMksolConsumerProjectionExact as Mksol
import DASHI.ComputerScience.RSA260BidiMksolVContextStressExact as Stress

------------------------------------------------------------------------
-- SOURCE-NATIVE CADO MKSOL CONTEXT FAMILY
--
-- The correct compression consumer is not one fixed synthetic V block. CADO's
-- BWC schema distinguishes the generator artifact F.sols*, starting V blocks,
-- prepared/balanced matrix action and S.sols* partial solution ranges.
--
-- RSA-260's primary run-parameter owner additionally pays two width-256 Krylov
-- sequences and 40 mksol ranges of width 32768.  Those published coordinates are
-- retained here, while exact file/range binding and prepared-operator identity
-- remain unpaid.
------------------------------------------------------------------------

cadoSchema : CADO.CADOBlockWiedemannArtifactSchema
cadoSchema = CADO.currentCADOBlockWiedemannArtifactSchema

rsa260RunParameters : Run.RunParameterReceipt
rsa260RunParameters = Run.rsa260LinearAlgebraParameters

mksolBoundary : Mksol.MksolConsumerProjectionBoundary
mksolBoundary = Mksol.canonicalMksolConsumerProjectionBoundary

vStressBoundary : Stress.MksolVContextStressBoundary
vStressBoundary = Stress.canonicalMksolVContextStressBoundary

record CADOMksolContextFamily : Set₁ where
  constructor cado-mksol-context-family
  field
    GeneratorArtifact : Set
    InitialVBlock : Set
    PreparedOperator : Set
    SolutionRange : Set
    PartialSolution : Set

    generatorPath : GeneratorArtifact -> String
    initialVPath : InitialVBlock -> String
    solutionPath : SolutionRange -> String

    evaluate :
      GeneratorArtifact ->
      InitialVBlock ->
      PreparedOperator ->
      SolutionRange ->
      PartialSolution
open CADOMksolContextFamily public

record FamilyAdequateGeneratorRepresentation
    (family : CADOMksolContextFamily) : Set₁ where
  constructor family-adequate-generator-representation
  field
    Representation : Set
    encodeGenerator : GeneratorArtifact family -> Representation
    evaluateRepresentation :
      Representation ->
      InitialVBlock family ->
      PreparedOperator family ->
      SolutionRange family ->
      PartialSolution family

    preservesEveryDeclaredContext :
      (generator : GeneratorArtifact family) ->
      (v : InitialVBlock family) ->
      (operator : PreparedOperator family) ->
      (range : SolutionRange family) ->
      evaluate family generator v operator range
      ≡ evaluateRepresentation
          (encodeGenerator generator)
          v operator range
open FamilyAdequateGeneratorRepresentation public

------------------------------------------------------------------------
-- Source-paid coordinates versus same-object binding.
------------------------------------------------------------------------

record CADOMksolContextSchemaReceipt : Set where
  constructor cado-mksol-context-schema-receipt
  field
    generatorPattern : String
    initialVPattern : String
    partialSolutionPattern : String
    lingenProducesGenerator : Bool
    mksolProducesSolutionSequence : Bool
    gatherProducesKernelVectors : Bool
    binarySplitWidth : Nat

    publishedKrylovSequenceCount : Nat
    publishedKrylovSequenceWidth : Nat
    publishedMksolRangeCount : Nat
    publishedMksolRangeWidth : Nat
    primaryRunCoordinatesPaid : Bool

    exactRSA260VBlockFileBindingKnown : Bool
    exactRSA260MksolRangeFileBindingKnown : Bool
    exactRSA260PreparedOperatorBytesKnown : Bool
open CADOMksolContextSchemaReceipt public

currentCADOMksolContextSchemaReceipt : CADOMksolContextSchemaReceipt
currentCADOMksolContextSchemaReceipt =
  cado-mksol-context-schema-receipt
    (CADO.generatorPattern cadoSchema)
    (CADO.initialVPattern cadoSchema)
    (CADO.mksolSequencePattern cadoSchema)
    (CADO.lingenProducesGenerator cadoSchema)
    (CADO.mksolProducesSolutionSequence cadoSchema)
    (CADO.gatherProducesKernelVectors cadoSchema)
    (CADO.binarySplitWidth cadoSchema)
    2
    256
    40
    32768
    true
    false false false

record CADOMksolContextFamilyBoundary : Set where
  constructor cado-mksol-context-family-boundary
  field
    sourceNativeGeneratorRolePaid : Bool
    sourceNativeInitialVRolePaid : Bool
    sourceNativePartialSolutionRolePaid : Bool
    contextFamilyPreservationInterfaceWritten : Bool
    primaryTwoWidth256SequenceCoordinatePaid : Bool
    primaryFortyMksolRangesOf32768Paid : Bool
    oneFixedVContextIsSufficientCompressionConsumer : Bool
    syntheticTwoVStressShowsContextExpansionCanReopenKernel : Bool
    exactRSA260VFileBindingPaid : Bool
    exactRSA260MksolRangeFileBindingPaid : Bool
    exactRSA260PreparedOperatorPaid : Bool
    exactHistoricalMksolRevisionPaid : Bool
    compressionMayBeRankedBeforeContextFamilyAdequacy : Bool
open CADOMksolContextFamilyBoundary public

canonicalCADOMksolContextFamilyBoundary : CADOMksolContextFamilyBoundary
canonicalCADOMksolContextFamilyBoundary =
  cado-mksol-context-family-boundary
    true true true true true true
    false true false false false false false

data CADOMksolContextFamilyResidual : Set where
  bindPublishedSequencesToExactRSA260VFiles : CADOMksolContextFamilyResidual
  bindPublishedMksolRangesToExactSolutionFiles : CADOMksolContextFamilyResidual
  bindPreparedOperatorSameObjectIdentity : CADOMksolContextFamilyResidual
  instantiateDeclaredProductionContextFamily : CADOMksolContextFamilyResidual
  testGeneratorRepresentationAgainstWholeFamily : CADOMksolContextFamilyResidual
  rankOnlyInsideFamilyAdequateStratum : CADOMksolContextFamilyResidual

firstCADOMksolContextFamilyResidual : CADOMksolContextFamilyResidual
firstCADOMksolContextFamilyResidual = bindPublishedSequencesToExactRSA260VFiles
