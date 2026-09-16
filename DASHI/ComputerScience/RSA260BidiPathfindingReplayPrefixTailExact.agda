module DASHI.ComputerScience.RSA260BidiPathfindingReplayPrefixTailExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Computation.SSSPGeneralPullPrefixQuotientExact as Pull
import DASHI.Computation.SSSPBMSSPConsumerContractExact as BMSSP
import DASHI.ComputerScience.RSA260BidiGeneratorDigestPrefixFrontierExact as Digest
import DASHI.ComputerScience.RSA260BidiCoefficientRankPrefixFrontierExact as Rank
import DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecExact as Codec

------------------------------------------------------------------------
-- PATHFINDING PREFIX/TAIL -> RSA GENERATOR REPLAY CROSS-POLLINATION
--
-- BMSSP/Pull contributes a generic representation law, not graph semantics:
-- a consumer-visible prefix may be sufficient for one consumer while an
-- unexposed tail is retained for full reconstruction.  Instantiate that law as
--
--   prefix = degree + first five coefficient-matrix ranks
--   tail   = exact hybrid coefficient replay representation.
--
-- On the current ten-generator synthetic portfolio the prefix pays recovered
-- receipt identity; direct coefficient replay still uses the exact tail.  This
-- module does not import shortest-path correctness, pivot coverage, distance
-- semantics or graph authority into Block Wiedemann.
------------------------------------------------------------------------

bmsspBoundary : BMSSP.BMSSPBidiBoundary
bmsspBoundary = BMSSP.canonicalBMSSPBidiBoundary

rankBoundary : Rank.CoefficientRankPrefixFrontierBoundary
rankBoundary = Rank.canonicalCoefficientRankPrefixFrontierBoundary

codecBoundary : Codec.CoefficientHybridReplayCodecBoundary
codecBoundary = Codec.canonicalCoefficientHybridReplayCodecBoundary

record GeneratorReplayPacket : Set where
  constructor generator-replay-packet
  field
    replayPrefix : Rank.FiveLayerRankPrefix
    replayTail : Codec.HybridEncodedGenerator
open GeneratorReplayPacket public

rebuildGeneratorReplayPacket :
  Rank.FiveLayerRankPrefix →
  Codec.HybridEncodedGenerator →
  GeneratorReplayPacket
rebuildGeneratorReplayPacket = generator-replay-packet

rebuildGeneratorReplayPacketExact :
  (packet : GeneratorReplayPacket) →
  rebuildGeneratorReplayPacket (replayPrefix packet) (replayTail packet)
    ≡ packet
rebuildGeneratorReplayPacketExact (generator-replay-packet prefix tail) = refl

prefixOfRebuiltGeneratorReplayPacket :
  (prefix : Rank.FiveLayerRankPrefix)
  (tail : Codec.HybridEncodedGenerator) →
  replayPrefix (rebuildGeneratorReplayPacket prefix tail) ≡ prefix
prefixOfRebuiltGeneratorReplayPacket prefix tail = refl

GeneratorReplayPullFactorisation : Set₁
GeneratorReplayPullFactorisation = Pull.PullPrefixFactorisation

generatorReplayPullFactorisation : GeneratorReplayPullFactorisation
generatorReplayPullFactorisation =
  Pull.pullPrefixFactorisation
    GeneratorReplayPacket
    Rank.FiveLayerRankPrefix
    Codec.HybridEncodedGenerator
    replayPrefix
    replayTail
    rebuildGeneratorReplayPacket
    rebuildGeneratorReplayPacketExact
    prefixOfRebuiltGeneratorReplayPacket

------------------------------------------------------------------------
-- Consumer 1: current synthetic generator-receipt identity descends through
-- the cheap rank prefix alone.
------------------------------------------------------------------------

generatorReceiptPrefixConsumer :
  Pull.PrefixConsumer generatorReplayPullFactorisation
generatorReceiptPrefixConsumer =
  Pull.prefixConsumer
    Digest.GeneratorReceiptAnswer
    Rank.answerFromFiveLayerRanks

generatorReceiptFromReplayPacket :
  GeneratorReplayPacket → Digest.GeneratorReceiptAnswer
generatorReceiptFromReplayPacket =
  Pull.consumeFull generatorReceiptPrefixConsumer

receiptConsumerIgnoresTailGivenSamePrefix :
  {left right : GeneratorReplayPacket} →
  replayPrefix left ≡ replayPrefix right →
  generatorReceiptFromReplayPacket left
    ≡ generatorReceiptFromReplayPacket right
receiptConsumerIgnoresTailGivenSamePrefix =
  Pull.consumerIgnoresTailGivenSamePrefix generatorReceiptPrefixConsumer

------------------------------------------------------------------------
-- Consumer 2: direct replay keeps the exact hybrid tail.
------------------------------------------------------------------------

decodeReplayTail : GeneratorReplayPacket → Codec.SyntheticGenerator
decodeReplayTail packet = Codec.decodeHybrid (replayTail packet)

rotate3ReplayPacket : GeneratorReplayPacket
rotate3ReplayPacket =
  generator-replay-packet
    Rank.r17-0-0-7-7-6
    Codec.rotate3Hybrid

rotate3TailReplays :
  decodeReplayTail rotate3ReplayPacket ≡ Codec.rotate3Generator
rotate3TailReplays = refl

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record PathfindingReplayPrefixTailBoundary : Set where
  constructor pathfinding-replay-prefix-tail-boundary
  field
    genericPullPrefixTailFactorisationReused : Bool
    bmsspPrefixConsumerPatternAvailable : Bool
    fiveLayerRankPrefixPaysCurrentReceiptIdentity : Bool
    exactHybridTailPaysCurrentSyntheticReplay : Bool
    prefixAndTailRebuildRepresentationExactly : Bool
    directReplayRetainsTail : Bool
    prefixImplementedAsStandaloneCoefficientDecoder : Bool
    globalTailTotalOrderRequiredForReceiptConsumer : Bool
    bmsspGraphCorrectnessTransferredToRSA : Bool
    pivotCoverageTheoremTransferredWithoutAdapter : Bool
    finitePrefixSufficiencyMeansProductionSufficiency : Bool
open PathfindingReplayPrefixTailBoundary public

canonicalPathfindingReplayPrefixTailBoundary : PathfindingReplayPrefixTailBoundary
canonicalPathfindingReplayPrefixTailBoundary =
  pathfinding-replay-prefix-tail-boundary
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
------------------------------------------------------------------------

data PathfindingReplayPrefixTailResidual : Set where
  proveGenericGF2RowBasisCodecRoundTrip : PathfindingReplayPrefixTailResidual
  testPrefixTailPacketAcrossExpandedGeneratorPortfolio : PathfindingReplayPrefixTailResidual
  deriveConsumerSpecificTailQuotientsForNonReplayDiagnostics : PathfindingReplayPrefixTailResidual
  compilePrefixTailPacketIntoProductionGeneratorResidualInterface : PathfindingReplayPrefixTailResidual
  acquireSameObjectAStarOrFSols : PathfindingReplayPrefixTailResidual
  replayMksolAndRecoverKernel : PathfindingReplayPrefixTailResidual

firstPathfindingReplayPrefixTailResidual : PathfindingReplayPrefixTailResidual
firstPathfindingReplayPrefixTailResidual = proveGenericGF2RowBasisCodecRoundTrip

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data BMSSPMeansBlockWiedemann : Set where
data PrefixIdentityMeansCoefficientReplay : Set where
data FinitePrefixMeansProductionSufficiency : Set where
data PullQuotientMeansGeneratorAlgebra : Set where

bmsspDoesNotBecomeBlockWiedemann : BMSSPMeansBlockWiedemann → ⊥
bmsspDoesNotBecomeBlockWiedemann ()

prefixIdentityDoesNotCreateCoefficientReplay : PrefixIdentityMeansCoefficientReplay → ⊥
prefixIdentityDoesNotCreateCoefficientReplay ()

finitePrefixDoesNotCreateProductionSufficiency : FinitePrefixMeansProductionSufficiency → ⊥
finitePrefixDoesNotCreateProductionSufficiency ()

pullQuotientDoesNotCreateGeneratorAlgebra : PullQuotientMeansGeneratorAlgebra → ⊥
pullQuotientDoesNotCreateGeneratorAlgebra ()
