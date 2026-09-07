{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanR208BishopLegacyRingEmbeddingExact where

------------------------------------------------------------------------
-- R208 SCALAR TRANSPORT FROM THE CANONICAL BISHOP -> LEGACY REAL BRIDGE
--
-- R208 historically asked Yang--Mills callers for a bespoke
-- `RationalRealRingEmbedding`.  The repository now owns all rational embedding
-- laws concretely on Murray/Bishop reals.  The only remaining carrier-changing
-- authority is the already isolated foundational `BishopToDASHIRealBridge`.
--
-- This file proves:
--
--   BishopToDASHIRealBridge
--     -> OrderedRationalRealEmbedding
--     -> OrderedAdditiveRationalRealEmbedding
--     -> R208.RationalRealRingEmbedding.
--
-- Thus YM no longer pays a second independent Q -> legacy-R ring-embedding
-- receipt.  This does NOT inhabit the Bishop->legacy bridge itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bridge
import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as BishopQ
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as BishopInterval
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as R102
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as R104
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208

legacyRationalEmbed : Bridge.BishopToDASHIRealBridge → ℚ →
  DASHI.Foundations.RealAnalysisAxioms.ℝ
legacyRationalEmbed bridge q =
  Bridge.embed bridge (BishopQ.bishopRationalEmbed q)

bishopBridgeOrderedEmbedding :
  Bridge.BishopToDASHIRealBridge → R102.OrderedRationalRealEmbedding
bishopBridgeOrderedEmbedding bridge = record
  { R102.OrderedRationalRealEmbedding.embed = legacyRationalEmbed bridge
  ; R102.OrderedRationalRealEmbedding.zeroExact =
      trans
        (Bridge.embedEquivalent bridge BishopInterval.embedZero)
        (Bridge.embedZero bridge)
  ; R102.OrderedRationalRealEmbedding.orderPreserving =
      λ order → Bridge.embedLessEqual bridge (BishopQ.bishopEmbedOrder order)
  ; R102.OrderedRationalRealEmbedding.strictOrderPreserving =
      λ strict → Bridge.embedStrictLess bridge
        (BishopInterval.embedStrictOrder strict)
  }

bishopBridgeAdditiveEmbedding :
  Bridge.BishopToDASHIRealBridge → R104.OrderedAdditiveRationalRealEmbedding
bishopBridgeAdditiveEmbedding bridge = record
  { R104.OrderedAdditiveRationalRealEmbedding.base =
      bishopBridgeOrderedEmbedding bridge
  ; R104.OrderedAdditiveRationalRealEmbedding.oneExact =
      trans
        (Bridge.embedEquivalent bridge BishopInterval.embedOne)
        (Bridge.embedOne bridge)
  ; R104.OrderedAdditiveRationalRealEmbedding.addExact =
      λ a b →
        trans
          (Bridge.embedEquivalent bridge (BishopQ.bishopEmbedAdd a b))
          (Bridge.embedAdd bridge
            (BishopQ.bishopRationalEmbed a)
            (BishopQ.bishopRationalEmbed b))
  }

bishopBridgeRingEmbedding :
  Bridge.BishopToDASHIRealBridge → R208.RationalRealRingEmbedding
bishopBridgeRingEmbedding bridge = record
  { R208.RationalRealRingEmbedding.additive =
      bishopBridgeAdditiveEmbedding bridge
  ; R208.RationalRealRingEmbedding.multiplyExact =
      λ a b →
        trans
          (Bridge.embedEquivalent bridge (BishopInterval.embedMul a b))
          (Bridge.embedMul bridge
            (BishopQ.bishopRationalEmbed a)
            (BishopQ.bishopRationalEmbed b))
  }

r208BishopLegacyRingEmbeddingCompilerLevel : ProofLevel
r208BishopLegacyRingEmbeddingCompilerLevel = machineChecked

-- The bespoke R208 payment is pruned on this route.  The foundational carrier
-- equivalence/transport remains explicit and conditional in its own owner.
literalBishopToLegacyRealBridgeForR208Level : ProofLevel
literalBishopToLegacyRealBridgeForR208Level = conditional
