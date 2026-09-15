module DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiCoefficientRankPrefixFrontierExact as RankFrontier
import DASHI.ComputerScience.RSA260BidiSignedResidualAStarSearchExact as Search

------------------------------------------------------------------------
-- EXACT HYBRID REPLAY CODEC RECEIPT
--
-- The rank-prefix frontier is a discriminator only.  This owner moves to a
-- replay-preserving representation of the actual synthetic coefficient arrays.
-- Each 8x8 GF(2) coefficient layer chooses the shorter of:
--
--   raw:    1 mode bit + 64 matrix payload bits
--   factor: 1 mode bit + 4 rank bits + r*8 basis-row bits + 8*r row-mask bits
--
-- The Python receipt reconstructs every coefficient matrix, re-packs the full
-- generator, and checks the recovered SHA-256 against the original receipt.
--
-- Description/payload/witness bits and decode XOR work stay separate.  This is
-- exactly the cost-discipline imported from the signed SSP/FRACTRAN lane; it is
-- not a claim that the biological/SSP semantics are Block-Wiedemann semantics.
------------------------------------------------------------------------

rankFrontierBoundary : RankFrontier.CoefficientRankPrefixFrontierBoundary
rankFrontierBoundary = RankFrontier.canonicalCoefficientRankPrefixFrontierBoundary

searchBoundary : Search.SignedResidualAStarSearchBoundary
searchBoundary = Search.canonicalSignedResidualAStarSearchBoundary

record HybridCodecRuntimeReceipt : Set where
  constructor hybrid-codec-runtime-receipt
  field
    runtimePath : String
    runtimeGitBlob : String
    runtimeSHA256 : String
    outputPath : String
    outputGitBlob : String
    outputSHA256 : String
    portfolioSize : Nat
    minimumBitsSaved : Nat
    maximumBitsSaved : Nat
    allRoundTripsExact : Bool
    allReconstructedSHAsMatch : Bool
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open HybridCodecRuntimeReceipt public

currentHybridCodecRuntimeReceipt : HybridCodecRuntimeReceipt
currentHybridCodecRuntimeReceipt =
  hybrid-codec-runtime-receipt
    "/mnt/data/rsa260_coefficient_hybrid_codec.py"
    "dd11b619b146727203b4e4ff79cbd8b6074ef734"
    "439074e5f9d21e05d057c8671671bd56fb46b731c1ef9038253064c2a9cd5dac"
    "/mnt/data/rsa260_coefficient_hybrid_codec.json"
    "3b85313cb2ac9f7d2752c6eb6837c793b51543db"
    "8aa2d11ebfb88a75ffd56cd6685a6498dc487bd0eac1e96fee8b7df7a24b0a9f"
    10
    52
    159
    true
    true
    true
    false

------------------------------------------------------------------------
-- Finite formal carrier for the ten runtime-paid generators.
------------------------------------------------------------------------

data SyntheticGenerator : Set where
  identityGenerator : SyntheticGenerator
  rotate1Generator : SyntheticGenerator
  rotate2Generator : SyntheticGenerator
  rotate3Generator : SyntheticGenerator
  affine3Generator : SyntheticGenerator
  affine5Generator : SyntheticGenerator
  affine7Generator : SyntheticGenerator
  affine9Generator : SyntheticGenerator
  xor1Generator : SyntheticGenerator
  bitrev9Generator : SyntheticGenerator

data HybridEncodedGenerator : Set where
  identityHybrid : HybridEncodedGenerator
  rotate1Hybrid : HybridEncodedGenerator
  rotate2Hybrid : HybridEncodedGenerator
  rotate3Hybrid : HybridEncodedGenerator
  affine3Hybrid : HybridEncodedGenerator
  affine5Hybrid : HybridEncodedGenerator
  affine7Hybrid : HybridEncodedGenerator
  affine9Hybrid : HybridEncodedGenerator
  xor1Hybrid : HybridEncodedGenerator
  bitrev9Hybrid : HybridEncodedGenerator

encodeHybrid : SyntheticGenerator → HybridEncodedGenerator
encodeHybrid identityGenerator = identityHybrid
encodeHybrid rotate1Generator = rotate1Hybrid
encodeHybrid rotate2Generator = rotate2Hybrid
encodeHybrid rotate3Generator = rotate3Hybrid
encodeHybrid affine3Generator = affine3Hybrid
encodeHybrid affine5Generator = affine5Hybrid
encodeHybrid affine7Generator = affine7Hybrid
encodeHybrid affine9Generator = affine9Hybrid
encodeHybrid xor1Generator = xor1Hybrid
encodeHybrid bitrev9Generator = bitrev9Hybrid

decodeHybrid : HybridEncodedGenerator → SyntheticGenerator
decodeHybrid identityHybrid = identityGenerator
decodeHybrid rotate1Hybrid = rotate1Generator
decodeHybrid rotate2Hybrid = rotate2Generator
decodeHybrid rotate3Hybrid = rotate3Generator
decodeHybrid affine3Hybrid = affine3Generator
decodeHybrid affine5Hybrid = affine5Generator
decodeHybrid affine7Hybrid = affine7Generator
decodeHybrid affine9Hybrid = affine9Generator
decodeHybrid xor1Hybrid = xor1Generator
decodeHybrid bitrev9Hybrid = bitrev9Generator

hybridRoundTripExact :
  (generator : SyntheticGenerator) →
  decodeHybrid (encodeHybrid generator) ≡ generator
hybridRoundTripExact identityGenerator = refl
hybridRoundTripExact rotate1Generator = refl
hybridRoundTripExact rotate2Generator = refl
hybridRoundTripExact rotate3Generator = refl
hybridRoundTripExact affine3Generator = refl
hybridRoundTripExact affine5Generator = refl
hybridRoundTripExact affine7Generator = refl
hybridRoundTripExact affine9Generator = refl
hybridRoundTripExact xor1Generator = refl
hybridRoundTripExact bitrev9Generator = refl

------------------------------------------------------------------------
-- Cost coordinates from the exact runtime receipt.
------------------------------------------------------------------------

record CodecCost : Set where
  constructor codec-cost
  field
    rawCoefficientBits : Nat
    payloadBits : Nat
    witnessBits : Nat
    descriptionBits : Nat
    decodeXorOps : Nat
    bitsSavedVsRaw : Nat
    descriptionIsPayloadPlusWitness : descriptionBits ≡ payloadBits + witnessBits
open CodecCost public

identityCost : CodecCost
identityCost = codec-cost 1088 928 29 957 8 131 refl

rotate1Cost : CodecCost
rotate1Cost = codec-cost 1088 896 33 929 7 159 refl

rotate2Cost : CodecCost
rotate2Cost = codec-cost 1024 944 28 972 15 52 refl

rotate3Cost : CodecCost
rotate3Cost = codec-cost 1088 912 29 941 1 147 refl

affine3Cost : CodecCost
affine3Cost = codec-cost 1024 944 24 968 10 56 refl

affine5Cost : CodecCost
affine5Cost = codec-cost 1088 976 29 1005 13 83 refl

affine7Cost : CodecCost
affine7Cost = codec-cost 1088 912 29 941 1 147 refl

affine9Cost : CodecCost
affine9Cost = codec-cost 1024 944 24 968 9 56 refl

xor1Cost : CodecCost
xor1Cost = codec-cost 1088 928 29 957 2 131 refl

bitrev9Cost : CodecCost
bitrev9Cost = codec-cost 1024 944 24 968 11 56 refl

costOf : SyntheticGenerator → CodecCost
costOf identityGenerator = identityCost
costOf rotate1Generator = rotate1Cost
costOf rotate2Generator = rotate2Cost
costOf rotate3Generator = rotate3Cost
costOf affine3Generator = affine3Cost
costOf affine5Generator = affine5Cost
costOf affine7Generator = affine7Cost
costOf affine9Generator = affine9Cost
costOf xor1Generator = xor1Cost
costOf bitrev9Generator = bitrev9Cost

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record CoefficientHybridReplayCodecBoundary : Set where
  constructor coefficient-hybrid-replay-codec-boundary
  field
    actualCoefficientArraysInherited : Bool
    exactByteRoundTripPaidOnTenGenerators : Bool
    reconstructedDigestMatchPaidOnTenGenerators : Bool
    everyCheckedGeneratorCompressedBelowBareCoefficientBits : Bool
    descriptionPayloadWitnessCostsSeparated : Bool
    decodeExecutionCostRetainedSeparately : Bool
    rankPrefixAloneReplaysCoefficients : Bool
    hybridCodecProvedGloballyOptimal : Bool
    formalFiniteTagRoundTripIsByteDecoderProof : Bool
    syntheticCodecIsProductionRSA260CodecReceipt : Bool
    coefficientCodecImpliesGeneratorAlgebraicCanonicity : Bool
open CoefficientHybridReplayCodecBoundary public

canonicalCoefficientHybridReplayCodecBoundary :
  CoefficientHybridReplayCodecBoundary
canonicalCoefficientHybridReplayCodecBoundary =
  coefficient-hybrid-replay-codec-boundary
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

------------------------------------------------------------------------
-- Roadmap.
--
-- We now have a replay-preserving synthetic codec.  The next high-alpha work is
-- robustness/generalisation of that codec and then compiling it as an OPTIONAL
-- representation under the production generator-residual interface.  Authentic
-- A*/F.sols acquisition remains an independent parallel leaf.
------------------------------------------------------------------------

data CoefficientHybridReplayCodecResidual : Set where
  crossValidateHybridCodecAcrossIndependentSyntheticGenerators : CoefficientHybridReplayCodecResidual
  searchAlternativeReplayCodecsOnDescriptionExecutionWitnessParetoFrontier : CoefficientHybridReplayCodecResidual
  proveGenericGF2RowBasisCodecRoundTrip : CoefficientHybridReplayCodecResidual
  compileHybridCodecIntoProductionGeneratorResidualInterface : CoefficientHybridReplayCodecResidual
  acquireSameObjectAStarOrFSols : CoefficientHybridReplayCodecResidual
  replayMksolFromAuthenticatedGeneratorResidual : CoefficientHybridReplayCodecResidual

firstCoefficientHybridReplayCodecResidual : CoefficientHybridReplayCodecResidual
firstCoefficientHybridReplayCodecResidual =
  crossValidateHybridCodecAcrossIndependentSyntheticGenerators

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data RuntimeRoundTripMeansKernelProof : Set where
data CompressionMeansAlgebraicCanonicality : Set where
data SyntheticCodecMeansProductionArtifact : Set where
data LowerDescriptionMeansLowerExecution : Set where

runtimeRoundTripDoesNotCreateKernelProof : RuntimeRoundTripMeansKernelProof → ⊥
runtimeRoundTripDoesNotCreateKernelProof ()

compressionDoesNotCreateAlgebraicCanonicality :
  CompressionMeansAlgebraicCanonicality → ⊥
compressionDoesNotCreateAlgebraicCanonicality ()

syntheticCodecDoesNotCreateProductionArtifact : SyntheticCodecMeansProductionArtifact → ⊥
syntheticCodecDoesNotCreateProductionArtifact ()

lowerDescriptionDoesNotMeanLowerExecution : LowerDescriptionMeansLowerExecution → ⊥
lowerDescriptionDoesNotMeanLowerExecution ()
