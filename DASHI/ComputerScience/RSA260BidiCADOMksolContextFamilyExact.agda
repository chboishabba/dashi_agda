module DASHI.ComputerScience.RSA260BidiCADOMksolContextFamilyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADO
import DASHI.ComputerScience.RSA260BidiMksolConsumerProjectionExact as Mksol
import DASHI.ComputerScience.RSA260BidiMksolVContextStressExact as Stress

------------------------------------------------------------------------
-- SOURCE-NATIVE CADO MKSOL CONTEXT FAMILY
--
-- The correct compression consumer is not one fixed synthetic V block.  CADO's
-- BWC schema distinguishes the generator artifact F.sols*, starting V blocks,
-- prepared/balanced matrix action and S.sols* partial solution ranges.
--
-- This owner therefore defines the family shape that any generator quotient has
-- to preserve.  Public implementation schema pays the artifact roles and naming
-- pattern only.  It does NOT recover the exact RSA-260 V partition, solution
-- range schedule, balanced operator bytes, or historical mksol revision.
------------------------------------------------------------------------

cadoSchema : CADO.CADOBlockWiedemannArtifactSchema
cadoSchema = CADO.currentCADOBlockWiedemannArtifactSchema

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

------------------------------------------------------------------------
-- Exact preservation is quantified over the declared family, not one context.
------------------------------------------------------------------------

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
-- Source-paid schema coordinates and unpaid same-object coordinates.
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
    exactRSA260VBlockPartitionKnown : Bool
    exactRSA260SolutionRangesKnown : Bool
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
    false false false

record CADOMksolContextFamilyBoundary : Set where
  constructor cado-mksol-context-family-boundary
  field
    sourceNativeGeneratorRolePaid : Bool
    sourceNativeInitialVRolePaid : Bool
    sourceNativePartialSolutionRolePaid : Bool
    contextFamilyPreservationInterfaceWritten : Bool
    oneFixedVContextIsSufficientCompressionConsumer : Bool
    syntheticTwoVStressShowsContextExpansionCanReopenKernel : Bool
    exactRSA260VPartitionPaid : Bool
    exactRSA260SolutionRangesPaid : Bool
    exactRSA260PreparedOperatorPaid : Bool
    exactHistoricalMksolRevisionPaid : Bool
    compressionMayBeRankedBeforeContextFamilyAdequacy : Bool
open CADOMksolContextFamilyBoundary public

canonicalCADOMksolContextFamilyBoundary : CADOMksolContextFamilyBoundary
canonicalCADOMksolContextFamilyBoundary =
  cado-mksol-context-family-boundary
    true true true true
    false true false false false false false

data CADOMksolContextFamilyResidual : Set where
  acquireExactRSA260VBlockPartition : CADOMksolContextFamilyResidual
  acquireExactRSA260MksolSolutionRanges : CADOMksolContextFamilyResidual
  bindPreparedOperatorSameObjectIdentity : CADOMksolContextFamilyResidual
  instantiateDeclaredProductionContextFamily : CADOMksolContextFamilyResidual
  testGeneratorRepresentationAgainstWholeFamily : CADOMksolContextFamilyResidual
  rankOnlyInsideFamilyAdequateStratum : CADOMksolContextFamilyResidual

firstCADOMksolContextFamilyResidual : CADOMksolContextFamilyResidual
firstCADOMksolContextFamilyResidual = acquireExactRSA260VBlockPartition
