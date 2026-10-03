{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223R136SourceEnvelopeUpperExact where

------------------------------------------------------------------------
-- SOURCE-ENVELOPE MAX-CUT.
--
-- The direct B1 receipt carries
--
--   embed Q_R136 <= embed D_Gamma,k + embed Tail_R109(k),
--
-- while the finite Eq.(2.23) compiler carries a rational upper bound
--
--   D_Gamma,k <= U.
--
-- Downstream sign transport does not need D_Gamma,k itself.  Using the
-- repository's existing additive ordered Q -> R embedding and real weak-order
-- transitivity, these compose to the strictly smaller terminal coordinate
--
--   embed Q_R136 <= embed (U + Tail_R109(k)).
--
-- This is a compiler reduction only.  It does not merge the two physical
-- producers that establish the B1 tail receipt and the source upper bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _≤ℝ_; _<ℝ_; ≤ℝ-trans)

import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as Direct
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as RealSign
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109

record R136SourceEnvelopeUpper
    (embedding : Additive.OrderedAdditiveRationalRealEmbedding)
    (source : R109.SourceNativeStressScaleCauchy)
    (completedRationalResponse sourceUpper : ℚ)
    (start : Nat) : Set₁ where
  field
    completionBelowSourceUpperPlusTail :
      Embed.embed (Additive.base embedding) completedRationalResponse
      ≤ℝ
      Embed.embed (Additive.base embedding)
        (sourceUpper + Tail.r109RemainingTail source start)

open R136SourceEnvelopeUpper public

fromDirectTailAndFiniteUpper :
  (embedding : Additive.OrderedAdditiveRationalRealEmbedding) →
  ∀ {source completed finite sourceUpper start} →
  Direct.DirectR144R109TailAnchor
    embedding source completed finite start →
  finite ≤ sourceUpper →
  R136SourceEnvelopeUpper
    embedding source completed sourceUpper start
fromDirectTailAndFiniteUpper
    embedding {source} {completed} {finite} {sourceUpper} {start}
    direct finiteBelow = record
  { R136SourceEnvelopeUpper.completionBelowSourceUpperPlusTail =
      ≤ℝ-trans completedBelowFiniteTail embeddedFiniteTailBelowSourceTail
  }
  where
  base = Additive.base embedding
  tail = Tail.r109RemainingTail source start

  completedBelowFiniteTail :
    Embed.embed base completed
    ≤ℝ Embed.embed base (finite + tail)
  completedBelowFiniteTail =
    subst
      (λ right → Embed.embed base completed ≤ℝ right)
      (sym (Additive.addExact embedding finite tail))
      (Direct.completionBelowFinitePlusTail direct)

  finiteTailBelowSourceTail : finite + tail ≤ sourceUpper + tail
  finiteTailBelowSourceTail =
    ℚP.+-mono-≤ finiteBelow ℚP.≤-refl

  embeddedFiniteTailBelowSourceTail :
    Embed.embed base (finite + tail)
    ≤ℝ Embed.embed base (sourceUpper + tail)
  embeddedFiniteTailBelowSourceTail =
    Embed.orderPreserving base finiteTailBelowSourceTail

sourceEnvelopeNegativeForcesR136Negative :
  (embedding : Additive.OrderedAdditiveRationalRealEmbedding) →
  (realOrder : RealSign.RealWeakStrictTransitivity) →
  (reflection :
    Readout.NegativeOrderReflectionAtZero (Additive.base embedding)) →
  ∀ {source completed sourceUpper start} →
  R136SourceEnvelopeUpper
    embedding source completed sourceUpper start →
  sourceUpper + Tail.r109RemainingTail source start < 0ℚ →
  completed < 0ℚ
sourceEnvelopeNegativeForcesR136Negative
    embedding realOrder reflection
    {source} {completed} {sourceUpper} {start}
    receipt sourceTailNegative =
  Readout.reflectNegative reflection completed
    (RealSign.weakThenStrict realOrder
      (completionBelowSourceUpperPlusTail receipt)
      embeddedSourceTailNegative)
  where
  base = Additive.base embedding
  sourceTail = sourceUpper + Tail.r109RemainingTail source start

  embeddedSourceTailNegative : Embed.embed base sourceTail <ℝ 0ℝ
  embeddedSourceTailNegative =
    subst
      (λ right → Embed.embed base sourceTail <ℝ right)
      (Embed.zeroExact base)
      (Embed.strictOrderPreserving base sourceTailNegative)

sourceEnvelopeTerminalConsumerNeedsFiniteDGamma : Bool
sourceEnvelopeTerminalConsumerNeedsFiniteDGamma = false

sourceEnvelopeUsesExistingRealWeakOrderAuthority : Bool
sourceEnvelopeUsesExistingRealWeakOrderAuthority = true

sourceEnvelopeAddsNewPhysicalPremise : Bool
sourceEnvelopeAddsNewPhysicalPremise = false

directTailAndFiniteUpperCompileToSourceEnvelope : Bool
directTailAndFiniteUpperCompileToSourceEnvelope = true
