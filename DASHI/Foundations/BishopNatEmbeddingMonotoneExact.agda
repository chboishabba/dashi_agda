module DASHI.Foundations.BishopNatEmbeddingMonotoneExact where

------------------------------------------------------------------------
-- ORDER PRESERVATION OF THE CANONICAL NAT -> BISHOP REAL EMBEDDING
--
-- DASHI CONTRIBUTION
--
-- Several analytic lanes already use the same canonical embedding
--
--   Nat -> (+ n / 1) -> Bishop real.
--
-- The finite rational embedding owned its additive/multiplicative equations
-- but did not expose monotonicity at the generic foundations layer.  This
-- owner pays that elementary bridge once.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base as Int using (+≤+)
open import Data.Nat.Base using (_≤_)
open import Data.Rational.Unnormalised as Rat using (_≤_)
import Data.Rational.Unnormalised.Properties as RatP

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed

natAsRationalMonotone :
  ∀ {m n : Nat} →
  m ≤ n →
  Rat._≤_ (NatEmbed.natAsRational m) (NatEmbed.natAsRational n)
natAsRationalMonotone m≤n =
  Rat.*≤* (Int.+≤+ m≤n)

natRealMonotone :
  ∀ {m n : Nat} →
  m ≤ n →
  BishopReal._≤_ (NatReal.natReal m) (NatReal.natReal n)
natRealMonotone {m} {n} m≤n =
  BishopP.p≤q⇒p⋆≤q⋆
    (NatEmbed.natAsRational m)
    (NatEmbed.natAsRational n)
    (natAsRationalMonotone m≤n)
