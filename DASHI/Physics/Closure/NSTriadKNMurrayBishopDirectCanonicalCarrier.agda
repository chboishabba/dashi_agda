module DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- Agda standard-library contributors; Loukas Grafakos; Rodolfo H. Torres;
-- DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; "A Multilinear Schur Test and Multiplier Operators"; and
-- "Murray--Bishop direct-canonical output-relocation carrier".
-- Venue/year: Springer, 1985; Dalhousie University/arXiv, 2022; Journal of
-- Functional Analysis 187 (2001), 1--24; Agda standard library; DASHI formal
-- development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- 10.1006/jfan.2001.3804; the repository adapter has no DOI.
-- Source pin: viktorcsimma/bishop commit
-- 582c6afcdf805d06730c8c0aa970f4a6e033b611.
-- Uses: normalized-to-unnormalized rational conversion, Murray's rational
-- embedding and its exact additive/order transport laws.
-- Relationship: inhabits the setoid rational-envelope carrier on the concrete
-- nondegenerate Bishop real backend.  No quotient choice, real exponential or
-- logarithm is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as Rational using (ℚ; 0ℚ; toℚᵘ)
import Data.Rational.Properties as RationalLaws

import Real as Bishop
import RealProperties as BishopLaws

import DASHI.Analysis.SetoidConstructiveRealSpine as Spine
import DASHI.Analysis.MurrayBishopSetoidBackend as Backend
import DASHI.Physics.Closure.NSTriadKNSetoidDirectCanonicalEnvelopeClosure as Direct

bishopRationalEmbed : ℚ → Bishop.ℝ
bishopRationalEmbed rational = Bishop._⋆ (toℚᵘ rational)

bishopEmbedAdd : ∀ left right →
  Bishop._≃_
    (bishopRationalEmbed (Rational._+_ left right))
    (Bishop._+_
      (bishopRationalEmbed left)
      (bishopRationalEmbed right))
bishopEmbedAdd left right =
  BishopLaws.≃-trans
    (BishopLaws.⋆-cong
      (RationalLaws.toℚᵘ-homo-+ left right))
    (BishopLaws.⋆-distrib-+
      (toℚᵘ left) (toℚᵘ right))

bishopEmbedOrder : ∀ {left right} →
  Rational._≤_ left right →
  Bishop._≤_ (bishopRationalEmbed left) (bishopRationalEmbed right)
bishopEmbedOrder {left} {right} left≤right =
  BishopLaws.p≤q⇒p⋆≤q⋆
    (toℚᵘ left) (toℚᵘ right)
    (RationalLaws.toℚᵘ-mono-≤ left≤right)

murrayBishopDirectCanonicalCarrier :
  Direct.SetoidOrderedRationalEnvelopeCarrier
murrayBishopDirectCanonicalCarrier = record
  { Scalar = Bishop.ℝ
  ; _≈_ = Bishop._≃_
  ; zero = Bishop.0ℝ
  ; add = Bishop._+_
  ; negate = Bishop.-_
  ; leq = Bishop._≤_
  ; rationalEmbed = bishopRationalEmbed

  ; approxReflexive = λ value → BishopLaws.≃-refl {x = value}
  ; approxSymmetric = BishopLaws.≃-symm
  ; approxTransitive = BishopLaws.≃-trans

  ; addCongruent = BishopLaws.+-cong
  ; negateCongruent = BishopLaws.-‿cong

  ; leqReflexive = λ value → BishopLaws.≤-refl {x = value}
  ; leqTransitive = BishopLaws.≤-trans
  ; leqRespectsLeft = BishopLaws.≤-respˡ-≃
  ; leqRespectsRight = BishopLaws.≤-respʳ-≃
  ; addMonotone = BishopLaws.+-mono-≤
  ; negateAntitone = BishopLaws.neg-mono-≤

  ; negateAdd = BishopLaws.neg-distrib-+

  ; embedZero = BishopLaws.≃-refl
  ; embedAdd = bishopEmbedAdd
  ; embedOrder = bishopEmbedOrder
  }

murrayBishopDirectCanonicalTheorem :
    (bridge : Direct.DirectCanonicalCoefficientBridge
      murrayBishopDirectCanonicalCarrier) →
  Direct.SetoidDirectCanonicalArchetypeTheorem
    murrayBishopDirectCanonicalCarrier bridge
murrayBishopDirectCanonicalTheorem =
  Direct.setoidDirectCanonicalArchetypeTheorem
    murrayBishopDirectCanonicalCarrier

murrayBishopRationalEnvelopeCarrierClosed : Bool
murrayBishopRationalEnvelopeCarrierClosed = true

murrayBishopDirectCanonical128Over93Closed : Bool
murrayBishopDirectCanonical128Over93Closed = true

murrayBishopRationalEnvelopeCarrierClosedIsTrue :
  murrayBishopRationalEnvelopeCarrierClosed ≡ true
murrayBishopRationalEnvelopeCarrierClosedIsTrue = refl

murrayBishopDirectCanonical128Over93ClosedIsTrue :
  murrayBishopDirectCanonical128Over93Closed ≡ true
murrayBishopDirectCanonical128Over93ClosedIsTrue = refl
