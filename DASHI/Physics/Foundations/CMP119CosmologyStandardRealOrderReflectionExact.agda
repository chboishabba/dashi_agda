{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyStandardRealOrderReflectionExact where

------------------------------------------------------------------------
-- STANDARD REAL ORDER ASYMMETRY -> ORDER REFLECTION AT ZERO.
--
-- The anomaly route previously carried an embedding-specific leaf
--
--   embed q < 0_R -> q < 0_Q.
--
-- That is not model-specific physics.  For the already-selected ordered
-- rational->real embedding it follows from exact rational trichotomy plus the
-- ordinary asymmetry of the strict real order.  Keep only that standard real
-- order authority explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout

record RealStrictOrderAsymmetry : Set₁ where
  field
    strictAsymmetric :
      ∀ {left right : ℝ} →
      left <ℝ right →
      right <ℝ left →
      ⊥

open RealStrictOrderAsymmetry public

negativeOrderReflectionAtZero :
  RealStrictOrderAsymmetry →
  (embedding : Embed.OrderedRationalRealEmbedding) →
  Readout.NegativeOrderReflectionAtZero embedding
negativeOrderReflectionAtZero realOrder embedding = record
  { Readout.NegativeOrderReflectionAtZero.reflectNegative = reflect
  }
  where
  reflect :
    ∀ rational →
    Embed.embed embedding rational <ℝ 0ℝ →
    rational < 0ℚ
  reflect rational embeddedNegative with ℚP.<-cmp rational 0ℚ
  ... | tri< rationalNegative _ _ = rationalNegative
  ... | tri≈ _ rationalZero _ =
    let
      embeddedIsZero :
        Embed.embed embedding rational ≡ 0ℝ
      embeddedIsZero =
        trans
          (cong (Embed.embed embedding) rationalZero)
          (Embed.zeroExact embedding)

      zeroNegative : 0ℝ <ℝ 0ℝ
      zeroNegative =
        subst
          (λ value → value <ℝ 0ℝ)
          embeddedIsZero
          embeddedNegative
    in
    ⊥-elim (strictAsymmetric realOrder zeroNegative zeroNegative)
  ... | tri> _ _ zeroBelowRational =
    let
      embeddedPositiveFromZero :
        Embed.embed embedding 0ℚ <ℝ Embed.embed embedding rational
      embeddedPositiveFromZero =
        Embed.strictOrderPreserving embedding zeroBelowRational

      realPositive :
        0ℝ <ℝ Embed.embed embedding rational
      realPositive =
        subst
          (λ value → value <ℝ Embed.embed embedding rational)
          (Embed.zeroExact embedding)
          embeddedPositiveFromZero
    in
    ⊥-elim
      (strictAsymmetric realOrder realPositive embeddedNegative)

embeddingSpecificNegativeReflectionIsCompilerOutput : Bool
embeddingSpecificNegativeReflectionIsCompilerOutput = true

remainingOrderAuthorityIsStandardRealStrictAsymmetry : Bool
remainingOrderAuthorityIsStandardRealStrictAsymmetry = true

standardRealOrderReflectionCompilerLevel : ProofLevel
standardRealOrderReflectionCompilerLevel = machineChecked

standardRealStrictOrderAsymmetryAuthorityLevel : ProofLevel
standardRealStrictOrderAsymmetryAuthorityLevel = standardImported
