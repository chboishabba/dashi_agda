module DASHI.Analysis.BishopFastCauchyRationalNormalizationRoundTripExact where

------------------------------------------------------------------------
-- ACTUAL ℚ <-> ℚᵘ RATIONAL NORMALIZATION ROUND TRIPS.
--
-- Sources: Agda standard library Data.Rational.Base and Properties,
-- plus vendored Bishop/Murray/Csimma Real._⋆ rational embedding.
--
-- Reduced rational ℚ and unnormalised rational ℚᵘ are different Agda
-- types. Their exact normalization isomorphism is already proved
-- in the standard library:
--
--   fromℚᵘ (toℚᵘ r) ≡ r
--   toℚᵘ (fromℚᵘ q) ≃ᵘ q.
--
-- This file pays the original rational TERM-level round trip of
-- the selected FastCauchy constant representatives, and lifts the
-- unnormalised round trip through BishopReal._⋆ congruence.
--
-- Important: this is not the missing equivalence of ALL regular
-- Bishop reals and FastCauchy reals. The full reindexing,
-- same-value zeta series, field homomorphism and completeness
-- compatibility must still be constructed at their original types.
-- Source-written, Agda 2.9 kernel admission pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import Data.Rational.Base as ℚ using (ℚ; fromℚᵘ; toℚᵘ)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; _≃_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.CanonicalRationalMetric as Metric
import DASHI.Analysis.BishopFastCauchyCanonicalRationalWeldExact as Canonical

toReduced : ℚᵘ → ℚ
toReduced = ℚ.fromℚᵘ

toUnnormalised : ℚ → ℚᵘ
toUnnormalised = ℚ.toℚᵘ

-- Exact standard-library propositional normalization on reduced ℚ.
reducedRationalRoundTrip :
  ∀ q → toReduced (toUnnormalised q) ≡ q
reducedRationalRoundTrip = ℚP.fromℚᵘ-toℚᵘ

-- Unnormalised ℚᵘ is a SETOID, not the quotient normal form type.
unnormalisedRationalRoundTrip :
  ∀ q → ℚᵘ._≃_ (toUnnormalised (toReduced q)) q
unnormalisedRationalRoundTrip = ℚP.toℚᵘ-fromℚᵘ

-- Transport of the selected original Bishop rational embedding across
-- the actual stdlib normalization, not a synthetic Real identity axiom.
bishopRationalEmbeddingNormalization :
  ∀ q →
  BishopReal._≃_
    (BishopReal._⋆ (toUnnormalised (toReduced q)))
    (BishopReal._⋆ q)
bishopRationalEmbeddingNormalization q =
  BishopP.⋆-cong (unnormalisedRationalRoundTrip q)

-- The original FastCauchy constant rational representation has the
-- actual reduced rational q at EVERY term of its defining stream.
canonicalFastReducedTermRoundTrip :
  ∀ (q : ℚ) (n : Nat) →
  Fast.approximate
    (Canonical.canonicalFastFromBishopRational (toUnnormalised q))
    n
  ≡ q
canonicalFastReducedTermRoundTrip q n =
  trans
    (Canonical.canonicalFastRationalTerm (toUnnormalised q) n)
    (reducedRationalRoundTrip q)
