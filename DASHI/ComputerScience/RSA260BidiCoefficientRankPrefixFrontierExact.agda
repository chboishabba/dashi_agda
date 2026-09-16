module DASHI.ComputerScience.RSA260BidiCoefficientRankPrefixFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiGeneratorDigestPrefixFrontierExact as Digest

------------------------------------------------------------------------
-- STRUCTURED COEFFICIENT-DERIVED RANK-PREFIX FRONTIER
--
-- We now expose the actual synthetic shared-generator coefficient arrays and
-- derive a structured sketch from them: the GF(2) rank of each coefficient
-- matrix F_l.  Search prefix length k in increasing order, always retaining
-- the generator degree d.
--
-- On the fixed-BASEX/BASEY ten-adapter portfolio:
--
--   k = 0..4 all collide;
--   k = 4 still conflates affine3 and bitrev9 at
--       d=16, ranks=(1,2,7,7);
--   k = 5 is the first checked prefix that separates all ten generator receipts.
--
-- This is a genuine coefficient-derived structural sketch, unlike a SHA prefix.
-- It still does NOT reconstruct F_l, prove algebraic identity, or establish
-- production sufficiency.
------------------------------------------------------------------------

record CoefficientRankPrefixRuntimeReceipt : Set where
  constructor coefficient-rank-prefix-runtime-receipt
  field
    runtimePath : String
    runtimeGitBlob : String
    runtimeSHA256 : String
    outputPath : String
    outputGitBlob : String
    outputSHA256 : String
    portfolioSize : Nat
    minimumCoefficientBytes : Nat
    maximumCoefficientBytes : Nat
    firstSeparatingRankPrefixLayers : Nat
    projectionPairHeldFixed : Bool
    actualSyntheticCoefficientArraysExposed : Bool
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open CoefficientRankPrefixRuntimeReceipt public

currentCoefficientRankPrefixRuntimeReceipt : CoefficientRankPrefixRuntimeReceipt
currentCoefficientRankPrefixRuntimeReceipt =
  coefficient-rank-prefix-runtime-receipt
    "/mnt/data/rsa260_coefficient_rank_prefix_frontier.py"
    "3d15a911356dfc450c9ba9318a9c55ef2c065e3c"
    "4bc7e85ae8b66c9c81d1b740e217d398bf200c1a8e897b8348890e6067fa16ca"
    "/mnt/data/rsa260_coefficient_rank_prefix_frontier.json"
    "b3de2032d99c104c74bc16e421504669d7c83678"
    "defedd6d5b45ee6c70f7ca520341350db758e8cef25d958cb237d57712c4e9d1"
    10
    128
    136
    5
    true
    true
    true
    false

------------------------------------------------------------------------
-- Four-layer observer: exactly one collision remains in the current portfolio.
------------------------------------------------------------------------

data FourLayerRankPrefix : Set where
  r17-0-1-8-8 : FourLayerRankPrefix
  r17-0-0-3-7 : FourLayerRankPrefix
  r16-1-3-6-7 : FourLayerRankPrefix
  r17-0-0-7-7 : FourLayerRankPrefix
  r16-1-2-7-7 : FourLayerRankPrefix
  r17-1-3-7-7 : FourLayerRankPrefix
  r17-0-0-5-7 : FourLayerRankPrefix
  r16-1-2-7-6 : FourLayerRankPrefix
  r17-0-0-6-7 : FourLayerRankPrefix

data FiveLayerRankPrefix : Set where
  r17-0-1-8-8-7 : FiveLayerRankPrefix
  r17-0-0-3-7-7 : FiveLayerRankPrefix
  r16-1-3-6-7-7 : FiveLayerRankPrefix
  r17-0-0-7-7-6 : FiveLayerRankPrefix
  r16-1-2-7-7-8 : FiveLayerRankPrefix
  r17-1-3-7-7-7 : FiveLayerRankPrefix
  r17-0-0-5-7-8 : FiveLayerRankPrefix
  r16-1-2-7-6-7 : FiveLayerRankPrefix
  r17-0-0-6-7-8 : FiveLayerRankPrefix
  r16-1-2-7-7-7 : FiveLayerRankPrefix

fourLayerRankObserve : Digest.AdapterWorld → FourLayerRankPrefix
fourLayerRankObserve Digest.identityWorld = r17-0-1-8-8
fourLayerRankObserve Digest.rotate1World = r17-0-0-3-7
fourLayerRankObserve Digest.rotate2World = r16-1-3-6-7
fourLayerRankObserve Digest.rotate3World = r17-0-0-7-7
fourLayerRankObserve Digest.affine3World = r16-1-2-7-7
fourLayerRankObserve Digest.affine5World = r17-1-3-7-7
fourLayerRankObserve Digest.affine7World = r17-0-0-5-7
fourLayerRankObserve Digest.affine9World = r16-1-2-7-6
fourLayerRankObserve Digest.xor1World = r17-0-0-6-7
fourLayerRankObserve Digest.bitrev9World = r16-1-2-7-7

fiveLayerRankObserve : Digest.AdapterWorld → FiveLayerRankPrefix
fiveLayerRankObserve Digest.identityWorld = r17-0-1-8-8-7
fiveLayerRankObserve Digest.rotate1World = r17-0-0-3-7-7
fiveLayerRankObserve Digest.rotate2World = r16-1-3-6-7-7
fiveLayerRankObserve Digest.rotate3World = r17-0-0-7-7-6
fiveLayerRankObserve Digest.affine3World = r16-1-2-7-7-8
fiveLayerRankObserve Digest.affine5World = r17-1-3-7-7-7
fiveLayerRankObserve Digest.affine7World = r17-0-0-5-7-8
fiveLayerRankObserve Digest.affine9World = r16-1-2-7-6-7
fiveLayerRankObserve Digest.xor1World = r17-0-0-6-7-8
fiveLayerRankObserve Digest.bitrev9World = r16-1-2-7-7-7

------------------------------------------------------------------------
-- Four layers fail on affine3 / bitrev9.
------------------------------------------------------------------------

FourLayerRankAdequacyDefect : Set₁
FourLayerRankAdequacyDefect =
  Query.QueryAdequacyDefect
    fourLayerRankObserve
    Digest.generatorReceiptSemantics
    Digest.recoveredGeneratorReceiptIdentity

fourLayerRanksCannotDetermineGeneratorReceipt : FourLayerRankAdequacyDefect
fourLayerRanksCannotDetermineGeneratorReceipt =
  Query.queryAdequacyDefect
    Digest.affine3World
    Digest.bitrev9World
    refl
    (λ ())

fourLayerRanksNotAdequate :
  Query.AdequateFor
    fourLayerRankObserve
    Digest.generatorReceiptSemantics
    Digest.recoveredGeneratorReceiptIdentity → ⊥
fourLayerRanksNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    fourLayerRanksCannotDetermineGeneratorReceipt

------------------------------------------------------------------------
-- Five layers separate every current receipt.
------------------------------------------------------------------------

answerFromFiveLayerRanks : FiveLayerRankPrefix → Digest.GeneratorReceiptAnswer
answerFromFiveLayerRanks r17-0-1-8-8-7 = Digest.identityReceipt
answerFromFiveLayerRanks r17-0-0-3-7-7 = Digest.rotate1Receipt
answerFromFiveLayerRanks r16-1-3-6-7-7 = Digest.rotate2Receipt
answerFromFiveLayerRanks r17-0-0-7-7-6 = Digest.rotate3Receipt
answerFromFiveLayerRanks r16-1-2-7-7-8 = Digest.affine3Receipt
answerFromFiveLayerRanks r17-1-3-7-7-7 = Digest.affine5Receipt
answerFromFiveLayerRanks r17-0-0-5-7-8 = Digest.affine7Receipt
answerFromFiveLayerRanks r16-1-2-7-6-7 = Digest.affine9Receipt
answerFromFiveLayerRanks r17-0-0-6-7-8 = Digest.xor1Receipt
answerFromFiveLayerRanks r16-1-2-7-7-7 = Digest.bitrev9Receipt

fiveLayerRankFactorisation :
  (world : Digest.AdapterWorld) →
  Digest.generatorReceiptAnswer Digest.recoveredGeneratorReceiptIdentity world
    ≡ answerFromFiveLayerRanks (fiveLayerRankObserve world)
fiveLayerRankFactorisation Digest.identityWorld = refl
fiveLayerRankFactorisation Digest.rotate1World = refl
fiveLayerRankFactorisation Digest.rotate2World = refl
fiveLayerRankFactorisation Digest.rotate3World = refl
fiveLayerRankFactorisation Digest.affine3World = refl
fiveLayerRankFactorisation Digest.affine5World = refl
fiveLayerRankFactorisation Digest.affine7World = refl
fiveLayerRankFactorisation Digest.affine9World = refl
fiveLayerRankFactorisation Digest.xor1World = refl
fiveLayerRankFactorisation Digest.bitrev9World = refl

FiveLayerRankAdequacy : Set₁
FiveLayerRankAdequacy =
  Query.AdequateFor
    fiveLayerRankObserve
    Digest.generatorReceiptSemantics
    Digest.recoveredGeneratorReceiptIdentity

generatorReceiptFactorsThroughFiveLayerRanks : FiveLayerRankAdequacy
generatorReceiptFactorsThroughFiveLayerRanks =
  Query.factorsForQuery answerFromFiveLayerRanks fiveLayerRankFactorisation

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record CoefficientRankPrefixFrontierBoundary : Set where
  constructor coefficient-rank-prefix-frontier-boundary
  field
    actualCoefficientArraysExposed : Bool
    coefficientArraysSmallEnoughForDirectSyntheticReplay : Bool
    fourLayerRankPrefixCollisionPaid : Bool
    fiveLayerRankPrefixSeparatesCurrentPortfolio : Bool
    fiveLayersIsFirstSeparatingCheckedRankPrefix : Bool
    rankPrefixDerivedFromCoefficientStructure : Bool
    rankPrefixReopensCoefficientMatrices : Bool
    rankPrefixIsAlgebraicGeneratorIdentity : Bool
    rankPrefixSufficientForProductionRSA260 : Bool
    rankPrefixGloballyMinimalResidual : Bool
    rankPrefixCanReplaceGeneratorForMksol : Bool
open CoefficientRankPrefixFrontierBoundary public

canonicalCoefficientRankPrefixFrontierBoundary :
  CoefficientRankPrefixFrontierBoundary
canonicalCoefficientRankPrefixFrontierBoundary =
  coefficient-rank-prefix-frontier-boundary
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
-- Roadmap: use rank prefix as a cheap discriminator, retain coefficient bytes
-- whenever replay is required, and now attack richer replay-preserving codecs.
------------------------------------------------------------------------

data CoefficientRankPrefixFrontierResidual : Set where
  defineReplayPreservingCoefficientCodecFamily : CoefficientRankPrefixFrontierResidual
  testCodecRoundTripOnAllTenSyntheticGenerators : CoefficientRankPrefixFrontierResidual
  rankSurvivingCodecsByDescriptionExecutionAndWitnessCost : CoefficientRankPrefixFrontierResidual
  deriveAdmissibleCodecSearchHeuristicIfAvailable : CoefficientRankPrefixFrontierResidual
  compileWinningCodecIntoProductionGeneratorResidualAdapter : CoefficientRankPrefixFrontierResidual
  acquireSameObjectAStarOrFSols : CoefficientRankPrefixFrontierResidual

firstCoefficientRankPrefixFrontierResidual : CoefficientRankPrefixFrontierResidual
firstCoefficientRankPrefixFrontierResidual =
  defineReplayPreservingCoefficientCodecFamily

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data StructuralDiscriminatorMeansReplayCodec : Set where
data FiniteSeparationMeansAlgebraicIdentity : Set where
data FiveLayersMeansGlobalMinimalResidual : Set where
data SyntheticCodecMeansProductionSufficiency : Set where

structuralDiscriminatorDoesNotCreateReplayCodec :
  StructuralDiscriminatorMeansReplayCodec → ⊥
structuralDiscriminatorDoesNotCreateReplayCodec ()

finiteSeparationDoesNotCreateAlgebraicIdentity :
  FiniteSeparationMeansAlgebraicIdentity → ⊥
finiteSeparationDoesNotCreateAlgebraicIdentity ()

fiveLayersDoNotCreateGlobalMinimality : FiveLayersMeansGlobalMinimalResidual → ⊥
fiveLayersDoNotCreateGlobalMinimality ()

syntheticCodecDoesNotCreateProductionSufficiency :
  SyntheticCodecMeansProductionSufficiency → ⊥
syntheticCodecDoesNotCreateProductionSufficiency ()
