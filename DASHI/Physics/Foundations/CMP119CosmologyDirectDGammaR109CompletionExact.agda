{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyDirectDGammaR109CompletionExact where

------------------------------------------------------------------------
-- B1 MAX-CUT BELOW THE FINITE-EXPECTATION PRESENTATION.
--
-- The terminal sign route does not need a separately named finite expectation
-- sequence.  Its finite scalar is the actual R144 effective-action response
-- D_Gamma,k.  Therefore use that sequence directly:
--
--   G k = embed(D_Gamma,k).
--
-- One source-native Cauchy statement on G, together with identification of the
-- completed R136 response as lim G, gives the direct tail anchor at EVERY k.
-- The old all-cutoff bridge
--
--   finiteExpectation k = embed(D_Gamma,k)
--
-- disappears completely from the shortest route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_; _≤ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyB1SelectedSameSequenceMaxCutExact as B1
import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as Direct
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record DirectDGammaR109Completion
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (embedding : Additive.OrderedAdditiveRationalRealEmbedding)
    (source : R109.SourceNativeStressScaleCauchy)
    (finiteDGamma : Nat → ℚ)
    (completedRationalResponse : ℚ) : Set₁ where
  field
    futureDGammaBelowStartPlusR109Tail :
      ∀ start count →
      Embed.embed (Additive.base embedding) (finiteDGamma (start + count))
      ≤ℝ
      Embed.embed (Additive.base embedding) (finiteDGamma start)
        +ℝ
        Embed.embed (Additive.base embedding)
          (Tail.r109RemainingTail source start)

    completedResponseIsDGammaSequenceLimit :
      Embed.embed (Additive.base embedding) completedRationalResponse
      ≡
      Seq.limit sequenceLimit
        (λ cutoff →
          Embed.embed (Additive.base embedding) (finiteDGamma cutoff))

open DirectDGammaR109Completion public

directAnchorAtEveryCutoff :
  ∀ {sequenceLimit embedding source finiteDGamma completed} →
  B1.RealTailLimitOrderAuthority sequenceLimit →
  DirectDGammaR109Completion
    sequenceLimit embedding source finiteDGamma completed →
  ∀ cutoff →
  Direct.DirectR144R109TailAnchor
    embedding source completed (finiteDGamma cutoff) cutoff
directAnchorAtEveryCutoff
    {sequenceLimit} {embedding} {source} {finiteDGamma} {completed}
    limitOrder completion cutoff = record
  { Direct.DirectR144R109TailAnchor.completionBelowFinitePlusTail =
      completedBelow
  }
  where
  base = Additive.base embedding

  upper : ℝ
  upper =
    Embed.embed base (finiteDGamma cutoff)
      +ℝ Embed.embed base (Tail.r109RemainingTail source cutoff)

  shifted : Nat → ℝ
  shifted count = Embed.embed base (finiteDGamma (cutoff + count))

  shiftedBelow : ∀ count → shifted count ≤ℝ upper
  shiftedBelow = futureDGammaBelowStartPlusR109Tail completion cutoff

  shiftedLimitBelow : Seq.limit sequenceLimit shifted ≤ℝ upper
  shiftedLimitBelow =
    B1.limitBelowConstantFromPointwise
      limitOrder shifted upper shiftedBelow

  fullLimitBelow :
    Seq.limit sequenceLimit (λ k → Embed.embed base (finiteDGamma k))
    ≤ℝ upper
  fullLimitBelow =
    subst
      (λ value → value ≤ℝ upper)
      (B1.finitePrefixDoesNotChangeLimit
        limitOrder
        (λ k → Embed.embed base (finiteDGamma k))
        cutoff)
      shiftedLimitBelow

  completedBelow : Embed.embed base completed ≤ℝ upper
  completedBelow =
    subst
      (λ value → value ≤ℝ upper)
      (sym (completedResponseIsDGammaSequenceLimit completion))
      fullLimitBelow

directDGammaSequenceEliminatesFiniteExpectationBridge : Bool
directDGammaSequenceEliminatesFiniteExpectationBridge = true

allCutoffDirectAnchorIsCompilerOutput : Bool
allCutoffDirectAnchorIsCompilerOutput = true

remainingB1SourceContentIsDirectDGammaCauchyAndEndpoint : Bool
remainingB1SourceContentIsDirectDGammaCauchyAndEndpoint = true
