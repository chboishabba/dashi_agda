module DASHI.ComputerScience.RSA260BidiHybridReplayMksolAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecExact as Codec
import DASHI.ComputerScience.RSA260BidiMksolConsumerProjectionExact as Mksol
import DASHI.ComputerScience.RSA260BidiMksolStyleConsumerCollisionExact as Collision

------------------------------------------------------------------------
-- EXACT REPLAY AS A SUFFICIENT UPPER ENDPOINT FOR GENERATOR-ACTION CONSUMERS
--
-- The previous collision owner showed that rank sketches can fail a concrete
-- mksol-style evaluation consumer.  Here we record the opposite endpoint:
-- once a representation reopens the exact generator state, any pure consumer
-- of that generator is preserved after decode.
--
-- The theorem is intentionally representation-level.  The finite Codec owner
-- has a formal tag round-trip; the runtime byte codec has a separate receipt.
-- Therefore this theorem does NOT upgrade the tag retraction into a generic
-- packed-byte kernel proof.
------------------------------------------------------------------------

codecBoundary : Codec.CoefficientHybridReplayCodecBoundary
codecBoundary = Codec.canonicalCoefficientHybridReplayCodecBoundary

mksolBoundary : Mksol.MksolConsumerProjectionBoundary
mksolBoundary = Mksol.canonicalMksolConsumerProjectionBoundary

collisionBoundary : Collision.MksolStyleConsumerCollisionBoundary
collisionBoundary = Collision.canonicalMksolStyleConsumerCollisionBoundary

consumerPreservedByHybridReplay :
  {Observation : Set} ->
  (consumer : Codec.SyntheticGenerator -> Observation) ->
  (generator : Codec.SyntheticGenerator) ->
  consumer (Codec.decodeHybrid (Codec.encodeHybrid generator))
  ≡ consumer generator
consumerPreservedByHybridReplay consumer generator =
  cong consumer (Codec.hybridRoundTripExact generator)

------------------------------------------------------------------------
-- A small explicit mksol-style consumer carrier makes the intended use clear.
-- Its values are semantic labels, not numeric CADO outputs.
------------------------------------------------------------------------

data GeneratorActionClass : Set where
  identityAction : GeneratorActionClass
  rotate1Action : GeneratorActionClass
  rotate2Action : GeneratorActionClass
  rotate3Action : GeneratorActionClass
  affine3Action : GeneratorActionClass
  affine5Action : GeneratorActionClass
  affine7Action : GeneratorActionClass
  affine9Action : GeneratorActionClass
  xor1Action : GeneratorActionClass
  bitrev9Action : GeneratorActionClass

generatorActionClass : Codec.SyntheticGenerator -> GeneratorActionClass
generatorActionClass Codec.identityGenerator = identityAction
generatorActionClass Codec.rotate1Generator = rotate1Action
generatorActionClass Codec.rotate2Generator = rotate2Action
generatorActionClass Codec.rotate3Generator = rotate3Action
generatorActionClass Codec.affine3Generator = affine3Action
generatorActionClass Codec.affine5Generator = affine5Action
generatorActionClass Codec.affine7Generator = affine7Action
generatorActionClass Codec.affine9Generator = affine9Action
generatorActionClass Codec.xor1Generator = xor1Action
generatorActionClass Codec.bitrev9Generator = bitrev9Action

hybridReplayPreservesActionClass :
  (generator : Codec.SyntheticGenerator) ->
  generatorActionClass (Codec.decodeHybrid (Codec.encodeHybrid generator))
  ≡ generatorActionClass generator
hybridReplayPreservesActionClass = consumerPreservedByHybridReplay generatorActionClass

record HybridReplayMksolAdequacyBoundary : Set where
  constructor hybrid-replay-mksol-adequacy-boundary
  field
    rankSketchFailureForSyntheticActionInherited : Bool
    exactTagReplayRoundTripInherited : Bool
    arbitraryPureGeneratorConsumerPreservedAfterDecode : Bool
    finiteActionClassConsumerPreserved : Bool
    exactReplayProvidesSufficientReferenceRepresentation : Bool
    theoremProvesPackedByteCodecCorrectness : Bool
    theoremProvesExactCADOMksolSemantics : Bool
    theoremUsesProductionRSA260Carrier : Bool
    strictlyCoarserEvaluationPreservingRepresentationFoundHere : Bool
open HybridReplayMksolAdequacyBoundary public

canonicalHybridReplayMksolAdequacyBoundary : HybridReplayMksolAdequacyBoundary
canonicalHybridReplayMksolAdequacyBoundary =
  hybrid-replay-mksol-adequacy-boundary
    true true true true true
    false false false false

data HybridReplayMksolAdequacyResidual : Set where
  searchStrictlyCoarserEvaluationPreservingQuotient : HybridReplayMksolAdequacyResidual
  instantiateActionOnActualCoefficientArrays : HybridReplayMksolAdequacyResidual
  alignSyntheticActionWithSourceNativeCADOMksolEvaluation : HybridReplayMksolAdequacyResidual
  payPackedByteDecodeTheoremIfNeeded : HybridReplayMksolAdequacyResidual
  bindSameObjectVAndPreparedOperatorForProduction : HybridReplayMksolAdequacyResidual

firstHybridReplayMksolAdequacyResidual : HybridReplayMksolAdequacyResidual
firstHybridReplayMksolAdequacyResidual = searchStrictlyCoarserEvaluationPreservingQuotient
