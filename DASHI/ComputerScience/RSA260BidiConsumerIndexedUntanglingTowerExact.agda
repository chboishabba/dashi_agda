module DASHI.ComputerScience.RSA260BidiConsumerIndexedUntanglingTowerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower
import DASHI.ComputerScience.RSA260BidiPathfindingReplayPrefixTailExact as Replay
import DASHI.ComputerScience.RSA260BidiCoefficientRankPrefixFrontierExact as Rank
import DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecExact as Codec
import DASHI.ComputerScience.RSA260BidiGeneratorDigestPrefixFrontierExact as Digest

------------------------------------------------------------------------
-- RSA-260 INSTANTIATION OF THE CONSUMER-INDEXED UNTANGLING TOWER
--
-- The first layer is the already-owned replay packet split:
--
--   GeneratorReplayPacket
--     <-> FiveLayerRankPrefix x HybridEncodedGenerator.
--
-- The current receipt-identity consumer terminates at the cheap prefix. Exact
-- packet reconstruction retains the tail. A second finite layer decodes the
-- hybrid tail to its exact synthetic generator identity; this demonstrates that
-- the generic tower really composes residual decompositions rather than merely
-- renaming one coarse/fine split.
--
-- This is a finite synthetic tower. It does not identify production RSA-260
-- artifacts, prove algebraic generator canonicity, or replace same-object
-- fine-incidence/matrix acquisition.
------------------------------------------------------------------------

GeneratorReplayPacket : Set
GeneratorReplayPacket = Replay.GeneratorReplayPacket

replayPacketGeometry : Fibre.CoarseFineReopening GeneratorReplayPacket
replayPacketGeometry =
  Fibre.coarseFineReopening
    Rank.FiveLayerRankPrefix
    Codec.HybridEncodedGenerator
    Replay.replayPrefix
    Replay.replayTail
    Replay.rebuildGeneratorReplayPacket
    Replay.rebuildGeneratorReplayPacketExact

data NoFurtherResidual : Set where
  noFurtherResidual : NoFurtherResidual

hybridTailReopen :
  Codec.SyntheticGenerator → NoFurtherResidual → Codec.HybridEncodedGenerator
hybridTailReopen generator noFurtherResidual = Codec.encodeHybrid generator

hybridTailReopenExact :
  (tail : Codec.HybridEncodedGenerator) →
  hybridTailReopen (Codec.decodeHybrid tail) noFurtherResidual ≡ tail
hybridTailReopenExact Codec.identityHybrid = refl
hybridTailReopenExact Codec.rotate1Hybrid = refl
hybridTailReopenExact Codec.rotate2Hybrid = refl
hybridTailReopenExact Codec.rotate3Hybrid = refl
hybridTailReopenExact Codec.affine3Hybrid = refl
hybridTailReopenExact Codec.affine5Hybrid = refl
hybridTailReopenExact Codec.affine7Hybrid = refl
hybridTailReopenExact Codec.affine9Hybrid = refl
hybridTailReopenExact Codec.xor1Hybrid = refl
hybridTailReopenExact Codec.bitrev9Hybrid = refl

hybridTailGeometry :
  Fibre.CoarseFineReopening Codec.HybridEncodedGenerator
hybridTailGeometry =
  Fibre.coarseFineReopening
    Codec.SyntheticGenerator
    NoFurtherResidual
    Codec.decodeHybrid
    (λ _ → noFurtherResidual)
    hybridTailReopen
    hybridTailReopenExact

RSAReplayUntanglingTower : Set₁
RSAReplayUntanglingTower = Tower.UntanglingTower GeneratorReplayPacket 2

rsaReplayUntanglingTower : RSAReplayUntanglingTower
rsaReplayUntanglingTower =
  Tower.layer replayPacketGeometry
    (Tower.layer hybridTailGeometry Tower.terminal)

encodeRSAReplayTower :
  GeneratorReplayPacket → Tower.TowerCode rsaReplayUntanglingTower
encodeRSAReplayTower = Tower.encodeTower rsaReplayUntanglingTower

decodeRSAReplayTower :
  Tower.TowerCode rsaReplayUntanglingTower → GeneratorReplayPacket
decodeRSAReplayTower = Tower.decodeTower rsaReplayUntanglingTower

rsaReplayTowerRoundTrip :
  (packet : GeneratorReplayPacket) →
  decodeRSAReplayTower (encodeRSAReplayTower packet) ≡ packet
rsaReplayTowerRoundTrip = Tower.towerRoundTrip rsaReplayUntanglingTower

------------------------------------------------------------------------
-- Consumer terminal: receipt identity factors through the first coarse layer.
------------------------------------------------------------------------

rsaReceiptObserve : GeneratorReplayPacket → Digest.GeneratorReceiptAnswer
rsaReceiptObserve packet =
  Rank.answerFromFiveLayerRanks (Replay.replayPrefix packet)

rsaReceiptFactorisation :
  Fibre.CoarseConsumerFactorisation replayPacketGeometry rsaReceiptObserve
rsaReceiptFactorisation =
  Fibre.coarseConsumerFactorisation
    Rank.answerFromFiveLayerRanks
    (λ _ → refl)

rsaReceiptConsumerTerminal :
  Tower.ConsumerTerminal replayPacketGeometry rsaReceiptObserve
rsaReceiptConsumerTerminal =
  Tower.consumerTerminalFromFactorisation rsaReceiptFactorisation

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record RSAConsumerIndexedUntanglingBoundary : Set where
  constructor rsa-consumer-indexed-untangling-boundary
  field
    genericUntanglingTowerReused : Bool
    replayPrefixTailGeometryReused : Bool
    hybridTailDecodedAtSecondLayer : Bool
    twoLayerFiniteTowerReopensPacketExactly : Bool
    receiptIdentityConsumerTerminatesAtFirstPrefix : Bool
    exactPacketReplayRetainsDeeperInformation : Bool
    finiteTowerProvesProductionGeneratorIdentity : Bool
    towerRecoversWithheldHistoricalAStarOrFSols : Bool
    towerEliminatesNeedForSameObjectCarrier : Bool
open RSAConsumerIndexedUntanglingBoundary public

canonicalRSAConsumerIndexedUntanglingBoundary :
  RSAConsumerIndexedUntanglingBoundary
canonicalRSAConsumerIndexedUntanglingBoundary =
  rsa-consumer-indexed-untangling-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
