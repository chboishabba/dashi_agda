module DASHI.Analysis.RiemannBishopPlattTrudgianLocatedHeightExact where

------------------------------------------------------------------------
-- CONCRETE MURRAY--BISHOP REALIZATION OF THE PT LOCATED HEIGHT WINDOW
--
-- The exact rational theorem is already owned by
-- RiemannPlattTrudgianLocatedHeightArithmeticExact.  Here we transport that
-- strict inequality into the pinned Murray--Bishop real carrier used elsewhere
-- in DASHI.  This is a concrete real theorem: no abstract Real socket and no
-- postulated real comparison are used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (toℚᵘ)
import Data.Rational.Properties as RationalLaws

import Real as Bishop
import RealProperties as BishopLaws

import DASHI.Analysis.RiemannPlattTrudgianLocatedHeightArithmeticExact as Arithmetic
import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as BishopCarrier

candidateHalfBishop : Bishop.ℝ
candidateHalfBishop =
  BishopCarrier.bishopRationalEmbed Arithmetic.candidateHalfHeight

publishedVerifiedHeightBishop : Bishop.ℝ
publishedVerifiedHeightBishop =
  BishopCarrier.bishopRationalEmbed Arithmetic.publishedVerifiedHeightRational

candidateHalfBelowPublishedHeightBishop :
  Bishop._<_ candidateHalfBishop publishedVerifiedHeightBishop
candidateHalfBelowPublishedHeightBishop =
  BishopLaws.p<q⇒p⋆<q⋆
    (toℚᵘ Arithmetic.candidateHalfHeight)
    (toℚᵘ Arithmetic.publishedVerifiedHeightRational)
    (RationalLaws.toℚᵘ-mono-<
      Arithmetic.candidateHalfBelowPublishedHeight)

record BishopPlattTrudgianLocatedHeightBoundary : Set where
  constructor bishop-platt-trudgian-located-height-boundary
  field
    standardRationalInequalityTransportedToBishop : Bool
    concreteOrderedRealThresholdsOwned : Bool
    abstractLegacyRealPostulateUsed : Bool
    analyticSubstrateCarrierIdentifiedWithBishopHere : Bool
    publishedZeroCriticalityTransportedHere : Bool
    rhDerivedHere : Bool

open BishopPlattTrudgianLocatedHeightBoundary public

canonicalBishopPlattTrudgianLocatedHeightBoundary :
  BishopPlattTrudgianLocatedHeightBoundary
canonicalBishopPlattTrudgianLocatedHeightBoundary =
  bishop-platt-trudgian-located-height-boundary
    true true false false false false
