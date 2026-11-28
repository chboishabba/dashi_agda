module DASHI.Cognition.PNF.X369OriginalMarkedSeedHypervoxelSourceExact where

-- Initial source state is the original signed seed (M,D,zero3).
-- There are seven legal M triads and 27 legal signed D triads:
-- 189 *marked* hyperfabric addresses, NOT all 3^9 worlds, NOT
-- all recurrent MoE states, and NOT a Stage13 source assignment.
-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Kernel intentionally deferred.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Product using (_×_; _,_)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as H
import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Cognition.PNF.X369NativeNineStageThirteenChartExact as Stage
import DASHI.Cognition.PNF.X369RecursiveHypervoxelPantsSameObjectExact as Parent

-- The original seven MEANS are zero plus signed coordinate unit axes.
data SourceMean7 : Set where
  zeroMean negX posX negY posY negZ posZ : SourceMean7

meanVoxel : SourceMean7 → H.Ternary27Point
meanVoxel zeroMean = H.origin
meanVoxel negX = H.ternary27Point Trit.sspNegOne Trit.sspZero Trit.sspZero
meanVoxel posX = H.ternary27Point Trit.sspPosOne Trit.sspZero Trit.sspZero
meanVoxel negY = H.ternary27Point Trit.sspZero Trit.sspNegOne Trit.sspZero
meanVoxel posY = H.ternary27Point Trit.sspZero Trit.sspPosOne Trit.sspZero
meanVoxel negZ = H.ternary27Point Trit.sspZero Trit.sspZero Trit.sspNegOne
meanVoxel posZ = H.ternary27Point Trit.sspZero Trit.sspZero Trit.sspPosOne

record SourceMarkedSeed : Set where
  constructor sourceMarkedSeed
  field
    mean : SourceMean7
    signedResidual : H.Ternary27Point
open SourceMarkedSeed public

markedFabric : SourceMarkedSeed → H.TernaryHyperformalPoint
markedFabric seed =
  H.ternaryHyperformalPoint
    (meanVoxel (mean seed))
    (signedResidual seed)
    H.origin

-- Complete original signed triad and mean orientation are retained,
-- including neutral residuals; the final 3 zero input slots stay zero.
originalSignedSeedInput : SourceMarkedSeed → H.TernaryHyperformalPoint
originalSignedSeedInput = markedFabric

sourceMeanCount : Nat
sourceMeanCount = 7

sourceResidualTriadCount : Nat
sourceResidualTriadCount = H.hypervoxelStateCount

sourceMarkedInputCount : sourceMeanCount * sourceResidualTriadCount ≡ 189
sourceMarkedInputCount = refl

sourceNotEntireFabric :
  H.hyperfabricStateCount ≡ 19683
sourceNotEntireFabric = H.hyperfabricStateCountIs19683

-- Retain a SOURCE witness of the mark. Projecting an arbitrary full
-- H369 world directly back to one of seven means is only partial.
-- This record prevents assuming all 19683 worlds are marked seeds.
record MarkedNativePoint : Set where
  constructor markedNativePoint
  field
    originalMark : SourceMarkedSeed
    nativePoint : H.TernaryHyperformalPoint
    nativeMatchesSeed : nativePoint ≡ markedFabric originalMark
open MarkedNativePoint

mark : SourceMarkedSeed → MarkedNativePoint
mark s = markedNativePoint s (markedFabric s) refl

reopenMark : MarkedNativePoint → SourceMarkedSeed
reopenMark = originalMark

sourceMarkBidi : (s : SourceMarkedSeed) → reopenMark (mark s) ≡ s
sourceMarkBidi s = refl

-- The original recurrent byte history is not equated to these nine
-- trits. An actual source-owned byte constructor must supply a
-- left-inverse on its admitted marked seed states; all other histories
-- retain a raw residual or are rejected by the chart.
module OriginalHistoryBytes
  (HistoryBytes : Set)
  (sourceSeedBytes : SourceMarkedSeed → HistoryBytes)
  (sourceByteDecoder : HistoryBytes → SourceMarkedSeed)
  (originalSeedDecoderCorrect : (s : SourceMarkedSeed) →
    sourceByteDecoder (sourceSeedBytes s) ≡ s) where

  record ExactOriginalSeed : Set where
    constructor exactOriginalSeed
    field
      sourceMark : SourceMarkedSeed
      originalBytes : HistoryBytes
      sourceBytesAreOriginal :
        originalBytes ≡ sourceSeedBytes sourceMark

  build : SourceMarkedSeed → ExactOriginalSeed
  build s = exactOriginalSeed s (sourceSeedBytes s) refl

  reopenSeedFromBytes : (s : SourceMarkedSeed) →
    sourceByteDecoder (ExactOriginalSeed.originalBytes (build s)) ≡ s
  reopenSeedFromBytes s = originalSeedDecoderCorrect s

-- A real 13-stage valuation requires four additional independent
-- stage trits. The original source input supplies only nine; no
-- thirteenth centre or future stage history is synthesized here.
module WithSourceStages
  (ExtraResidual SourceIndex : Set) where
  module Native = Parent.NinePlusFourSourceSpecimen ExtraResidual SourceIndex

  markedSourceStagePacket :
    SourceMarkedSeed → Stage.StageFour →
    ExtraResidual → SourceIndex →
    Parent.SameSourcePacket.Packet ExtraResidual SourceIndex
  markedSourceStagePacket source extra r k =
    Native.nativeWithStageResidual (markedFabric source) extra r k

  nativeMarkedBidi :
    (source : SourceMarkedSeed) (extra : Stage.StageFour)
    (r : ExtraResidual) (k : SourceIndex) →
    Parent.SameSourcePacket.nativeFabric
      (markedSourceStagePacket source extra r k)
    ≡ markedFabric source
  nativeMarkedBidi source extra r k = refl

-- The original signed-input seed constructor is an inhabited geometry
-- specimen. Original neural byte equality needs its own source-backed
-- codec owner; user-selected stage centre is an explicit residual.
