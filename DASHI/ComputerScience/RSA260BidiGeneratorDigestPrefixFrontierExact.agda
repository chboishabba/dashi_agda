module DASHI.ComputerScience.RSA260BidiGeneratorDigestPrefixFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiSignedResidualAStarSearchExact as Search

------------------------------------------------------------------------
-- FINITE GENERATOR-RECEIPT PREFIX FRONTIER
--
-- The ten-adapter fixed-BASEX/BASEY synthetic portfolio already records a
-- SHA-256 receipt for each recovered shared matrix-generator coefficient blob.
-- We now search hexadecimal prefix length in increasing order and ask whether
-- the prefix still determines RECEIPT identity on this finite portfolio.
--
-- Runtime result:
--   1 hex char / 4 bits: fails
--      c -> identity, rotate1, affine5
--      d -> rotate2, rotate3, affine9
--   2 hex chars / 8 bits: separates all ten current receipts
--
-- This is deliberately not a coefficient compression theorem.  An 8-bit
-- receipt prefix cannot reopen or replay the generator coefficients, is not an
-- algebraic generator identity, and carries no production-RSA-260 authority.
------------------------------------------------------------------------

searchBoundary : Search.SignedResidualAStarSearchBoundary
searchBoundary = Search.canonicalSignedResidualAStarSearchBoundary

record DigestPrefixRuntimeReceipt : Set where
  constructor digest-prefix-runtime-receipt
  field
    runtimePath : String
    runtimeGitBlob : String
    runtimeSHA256 : String
    outputPath : String
    outputGitBlob : String
    outputSHA256 : String
    portfolioSize : Nat
    firstFailingPrefixBits : Nat
    firstSeparatingPrefixBits : Nat
    projectionPairHeldFixed : Bool
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open DigestPrefixRuntimeReceipt public

currentDigestPrefixRuntimeReceipt : DigestPrefixRuntimeReceipt
currentDigestPrefixRuntimeReceipt =
  digest-prefix-runtime-receipt
    "/mnt/data/rsa260_generator_digest_prefix_frontier.py"
    "79bdf7b7a790535b4cd589ef8ceecfcb9253ff93"
    "3336035760797bab2737caf82d3d0ab154a71599a4e3b001a9703fa567871514"
    "/mnt/data/rsa260_generator_digest_prefix_frontier.json"
    "2a35bc8b6b0e6291898534f3b7ab7df0ef86dd05"
    "08551c137bbf849de11968b1fb9e0aabaad53216c2a94222582f9cfd25762619"
    10
    4
    8
    true
    true
    false

------------------------------------------------------------------------
-- Exact finite carrier.
------------------------------------------------------------------------

data AdapterWorld : Set where
  identityWorld : AdapterWorld
  rotate1World : AdapterWorld
  rotate2World : AdapterWorld
  rotate3World : AdapterWorld
  affine3World : AdapterWorld
  affine5World : AdapterWorld
  affine7World : AdapterWorld
  affine9World : AdapterWorld
  xor1World : AdapterWorld
  bitrev9World : AdapterWorld

data FourBitPrefix : Set where
  prefixC : FourBitPrefix
  prefixD : FourBitPrefix
  prefix2 : FourBitPrefix
  prefix9 : FourBitPrefix
  prefix4 : FourBitPrefix
  prefix8 : FourBitPrefix

data EightBitPrefix : Set where
  prefixCC : EightBitPrefix
  prefixC6 : EightBitPrefix
  prefixD0 : EightBitPrefix
  prefixD8 : EightBitPrefix
  prefix2C : EightBitPrefix
  prefixCD : EightBitPrefix
  prefix9A : EightBitPrefix
  prefixDA : EightBitPrefix
  prefix44 : EightBitPrefix
  prefix86 : EightBitPrefix

data GeneratorReceiptQuery : Set where
  recoveredGeneratorReceiptIdentity : GeneratorReceiptQuery

data GeneratorReceiptAnswer : Set where
  identityReceipt : GeneratorReceiptAnswer
  rotate1Receipt : GeneratorReceiptAnswer
  rotate2Receipt : GeneratorReceiptAnswer
  rotate3Receipt : GeneratorReceiptAnswer
  affine3Receipt : GeneratorReceiptAnswer
  affine5Receipt : GeneratorReceiptAnswer
  affine7Receipt : GeneratorReceiptAnswer
  affine9Receipt : GeneratorReceiptAnswer
  xor1Receipt : GeneratorReceiptAnswer
  bitrev9Receipt : GeneratorReceiptAnswer

fourBitObserve : AdapterWorld → FourBitPrefix
fourBitObserve identityWorld = prefixC
fourBitObserve rotate1World = prefixC
fourBitObserve rotate2World = prefixD
fourBitObserve rotate3World = prefixD
fourBitObserve affine3World = prefix2
fourBitObserve affine5World = prefixC
fourBitObserve affine7World = prefix9
fourBitObserve affine9World = prefixD
fourBitObserve xor1World = prefix4
fourBitObserve bitrev9World = prefix8

eightBitObserve : AdapterWorld → EightBitPrefix
eightBitObserve identityWorld = prefixCC
eightBitObserve rotate1World = prefixC6
eightBitObserve rotate2World = prefixD0
eightBitObserve rotate3World = prefixD8
eightBitObserve affine3World = prefix2C
eightBitObserve affine5World = prefixCD
eightBitObserve affine7World = prefix9A
eightBitObserve affine9World = prefixDA
eightBitObserve xor1World = prefix44
eightBitObserve bitrev9World = prefix86

generatorReceiptAnswer :
  GeneratorReceiptQuery → AdapterWorld → GeneratorReceiptAnswer
generatorReceiptAnswer recoveredGeneratorReceiptIdentity identityWorld = identityReceipt
generatorReceiptAnswer recoveredGeneratorReceiptIdentity rotate1World = rotate1Receipt
generatorReceiptAnswer recoveredGeneratorReceiptIdentity rotate2World = rotate2Receipt
generatorReceiptAnswer recoveredGeneratorReceiptIdentity rotate3World = rotate3Receipt
generatorReceiptAnswer recoveredGeneratorReceiptIdentity affine3World = affine3Receipt
generatorReceiptAnswer recoveredGeneratorReceiptIdentity affine5World = affine5Receipt
generatorReceiptAnswer recoveredGeneratorReceiptIdentity affine7World = affine7Receipt
generatorReceiptAnswer recoveredGeneratorReceiptIdentity affine9World = affine9Receipt
generatorReceiptAnswer recoveredGeneratorReceiptIdentity xor1World = xor1Receipt
generatorReceiptAnswer recoveredGeneratorReceiptIdentity bitrev9World = bitrev9Receipt

generatorReceiptSemantics :
  Query.QuerySemantics AdapterWorld GeneratorReceiptQuery GeneratorReceiptAnswer
generatorReceiptSemantics = Query.querySemantics generatorReceiptAnswer

------------------------------------------------------------------------
-- Four bits fail.
------------------------------------------------------------------------

FourBitPrefixAdequacyDefect : Set₁
FourBitPrefixAdequacyDefect =
  Query.QueryAdequacyDefect
    fourBitObserve
    generatorReceiptSemantics
    recoveredGeneratorReceiptIdentity

fourBitPrefixCannotDetermineGeneratorReceipt : FourBitPrefixAdequacyDefect
fourBitPrefixCannotDetermineGeneratorReceipt =
  Query.queryAdequacyDefect
    identityWorld
    rotate1World
    refl
    (λ ())

fourBitPrefixNotAdequate :
  Query.AdequateFor
    fourBitObserve
    generatorReceiptSemantics
    recoveredGeneratorReceiptIdentity → ⊥
fourBitPrefixNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    fourBitPrefixCannotDetermineGeneratorReceipt

------------------------------------------------------------------------
-- Eight bits separate the ten CURRENT receipt identities.
------------------------------------------------------------------------

answerFromEightBitPrefix : EightBitPrefix → GeneratorReceiptAnswer
answerFromEightBitPrefix prefixCC = identityReceipt
answerFromEightBitPrefix prefixC6 = rotate1Receipt
answerFromEightBitPrefix prefixD0 = rotate2Receipt
answerFromEightBitPrefix prefixD8 = rotate3Receipt
answerFromEightBitPrefix prefix2C = affine3Receipt
answerFromEightBitPrefix prefixCD = affine5Receipt
answerFromEightBitPrefix prefix9A = affine7Receipt
answerFromEightBitPrefix prefixDA = affine9Receipt
answerFromEightBitPrefix prefix44 = xor1Receipt
answerFromEightBitPrefix prefix86 = bitrev9Receipt

eightBitFactorisation :
  (world : AdapterWorld) →
  generatorReceiptAnswer recoveredGeneratorReceiptIdentity world
    ≡ answerFromEightBitPrefix (eightBitObserve world)
eightBitFactorisation identityWorld = refl
eightBitFactorisation rotate1World = refl
eightBitFactorisation rotate2World = refl
eightBitFactorisation rotate3World = refl
eightBitFactorisation affine3World = refl
eightBitFactorisation affine5World = refl
eightBitFactorisation affine7World = refl
eightBitFactorisation affine9World = refl
eightBitFactorisation xor1World = refl
eightBitFactorisation bitrev9World = refl

EightBitPrefixAdequacy : Set₁
EightBitPrefixAdequacy =
  Query.AdequateFor
    eightBitObserve
    generatorReceiptSemantics
    recoveredGeneratorReceiptIdentity

generatorReceiptFactorsThroughEightBitPrefix : EightBitPrefixAdequacy
generatorReceiptFactorsThroughEightBitPrefix =
  Query.factorsForQuery answerFromEightBitPrefix eightBitFactorisation

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record GeneratorDigestPrefixFrontierBoundary : Set where
  constructor generator-digest-prefix-frontier-boundary
  field
    tenAdapterPortfolioPaid : Bool
    projectionPairFrozen : Bool
    fourBitPrefixCollisionPaid : Bool
    eightBitPrefixSeparatesCurrentPortfolio : Bool
    eightBitsIsFirstSeparatingCheckedPrefix : Bool
    eightBitPrefixReopensCoefficientBytes : Bool
    eightBitPrefixIsAlgebraicGeneratorIdentity : Bool
    shaPrefixCollisionResistanceProved : Bool
    eightBitsSufficientForProductionRSA260 : Bool
    eightBitsGloballyMinimalGeneratorResidual : Bool
    digestPrefixIsReplayPacket : Bool
open GeneratorDigestPrefixFrontierBoundary public

canonicalGeneratorDigestPrefixFrontierBoundary :
  GeneratorDigestPrefixFrontierBoundary
canonicalGeneratorDigestPrefixFrontierBoundary =
  generator-digest-prefix-frontier-boundary
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

------------------------------------------------------------------------
-- Roadmap: receipt identification is cheap; replay compression is still open.
------------------------------------------------------------------------

data GeneratorDigestPrefixFrontierResidual : Set where
  exposeActualSyntheticGeneratorCoefficientArrays : GeneratorDigestPrefixFrontierResidual
  searchReplayPreservingCoefficientCompression : GeneratorDigestPrefixFrontierResidual
  attackStructuredCoefficientCompressionWithGeneratorConsumer : GeneratorDigestPrefixFrontierResidual
  deriveAdmissibleCompressionSearchLowerBoundIfAvailable : GeneratorDigestPrefixFrontierResidual
  compileSurvivingResidualIntoProductionReplayPacket : GeneratorDigestPrefixFrontierResidual
  acquireSameObjectAStarOrFSols : GeneratorDigestPrefixFrontierResidual

firstGeneratorDigestPrefixFrontierResidual : GeneratorDigestPrefixFrontierResidual
firstGeneratorDigestPrefixFrontierResidual =
  exposeActualSyntheticGeneratorCoefficientArrays

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ReceiptPrefixMeansCoefficientReplay : Set where
data ReceiptPrefixMeansAlgebraicIdentity : Set where
data FinitePrefixFrontierMeansProductionSufficiency : Set where
data FirstFinitePrefixMeansGlobalMinimum : Set where

receiptPrefixDoesNotCreateCoefficientReplay : ReceiptPrefixMeansCoefficientReplay → ⊥
receiptPrefixDoesNotCreateCoefficientReplay ()

receiptPrefixDoesNotCreateAlgebraicIdentity : ReceiptPrefixMeansAlgebraicIdentity → ⊥
receiptPrefixDoesNotCreateAlgebraicIdentity ()

finitePrefixDoesNotCreateProductionSufficiency :
  FinitePrefixFrontierMeansProductionSufficiency → ⊥
finitePrefixDoesNotCreateProductionSufficiency ()

firstFinitePrefixDoesNotCreateGlobalMinimum : FirstFinitePrefixMeansGlobalMinimum → ⊥
firstFinitePrefixDoesNotCreateGlobalMinimum ()
