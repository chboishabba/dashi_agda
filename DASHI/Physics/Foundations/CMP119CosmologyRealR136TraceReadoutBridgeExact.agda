{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact where

------------------------------------------------------------------------
-- RATIONAL R136 TRACE <-> REAL RENORMALIZED TRACE READOUT.
--
-- The cosmology terminal currently consumes an exact rational R136 readout.
-- The physical trace-anomaly lane proves strict negativity in the repository's
-- real scalar carrier.  Do not identify these scalars by name alone.
--
-- The only bridge needed for sign transport is:
--   * same readout after the ordered rational->real embedding;
--   * reflection of strict negativity at zero for that embedding/readout.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

record NegativeOrderReflectionAtZero
    (embedding : Embed.OrderedRationalRealEmbedding) : Set₁ where
  field
    reflectNegative : ∀ rational →
      Embed.embed embedding rational <ℝ 0ℝ →
      rational < 0ℚ

open NegativeOrderReflectionAtZero public

record R136RealTraceReadoutWeld
    (embedding : Embed.OrderedRationalRealEmbedding)
    (rationalTrace : ℚ)
    (realTrace : ℝ) : Set₁ where
  field
    sameReadout :
      Embed.embed embedding rationalTrace ≡ realTrace

    negativeReflection :
      NegativeOrderReflectionAtZero embedding

open R136RealTraceReadoutWeld public

realTraceNegativeForcesR136RationalNegative :
  ∀ {embedding rationalTrace realTrace} →
  R136RealTraceReadoutWeld embedding rationalTrace realTrace →
  realTrace <ℝ 0ℝ →
  rationalTrace < 0ℚ
realTraceNegativeForcesR136RationalNegative
    {embedding = embedding} {rationalTrace = rationalTrace}
    weld realNegative =
  reflectNegative (negativeReflection weld) rationalTrace
    (subst
      (λ value → value <ℝ 0ℝ)
      (sym (sameReadout weld))
      realNegative)

sameReadoutStillRequiresExplicitRepresentationWeld : Bool
sameReadoutStillRequiresExplicitRepresentationWeld = true

realAnomalySignCanFeedR136OnceReadoutWeldExists : Bool
realAnomalySignCanFeedR136OnceReadoutWeldExists = true
