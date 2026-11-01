module DASHI.Foundations.BishopNatRealPositiveExact where

------------------------------------------------------------------------
-- STRICT POSITIVITY OF POSITIVE NAT EMBEDDINGS
--
-- The cubic-translation owner defines the canonical Bishop embedding
--
--   natReal n = embed (+ n / 1).
--
-- This companion exports the elementary positivity receipt needed whenever a
-- positive finite index is used as a real scaling factor.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed
open import DASHI.Physics.YangMills.CompactLieProofLevel

natRealSuccessorStrictlyPositive :
  (n : Nat) →
  BishopReal._<_ BishopReal.0ℝ (Iterated.natReal (suc n))
natRealSuccessorStrictlyPositive n =
  BishopP.p<q⇒p⋆<q⋆
    0ℚᵘ
    (NatEmbed.natAsRational (suc n))
    (ℚP.positive⁻¹ (NatEmbed.natAsRational (suc n)))

natRealSuccessorPositive :
  (n : Nat) → BishopReal.Positive (Iterated.natReal (suc n))
natRealSuccessorPositive n =
  BishopP.0<x⇒posx (natRealSuccessorStrictlyPositive n)

bishopNatRealPositiveLevel : ProofLevel
bishopNatRealPositiveLevel = machineChecked
