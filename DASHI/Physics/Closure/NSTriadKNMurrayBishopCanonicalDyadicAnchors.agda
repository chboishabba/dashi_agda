module DASHI.Physics.Closure.NSTriadKNMurrayBishopCanonicalDyadicAnchors where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Viktor Csimma;
-- Agda standard-library contributors; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; and "Exact Murray--Bishop quarter and thirty-second anchors".
-- Venue/year: Springer, 1985; Dalhousie University/arXiv, 2022; Agda standard
-- library; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354; the repository
-- anchor package has no DOI.
-- Source pin: viktorcsimma/bishop commit
-- 582c6afcdf805d06730c8c0aa970f4a6e033b611.
-- Uses: exact rational powers, normalized-to-unnormalized rational conversion,
-- and Murray's additive/multiplicative rational embedding laws.
-- Relationship: provides the exact integer anchor sequences consumed by the
-- direct-canonical output-relocation theorem.  It replaces a total real
-- exponent/logarithm package with the strictly smaller proof object actually
-- needed by this archetype.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as Rational using (toℚᵘ; _*_)
import Data.Rational.Properties as RationalLaws

import Real as Bishop
import RealProperties as BishopLaws

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier

lowAnchor gapAnchor : Nat → Bishop.ℝ
lowAnchor shell = Carrier.bishopRationalEmbed (Geo.pow Geo.quarter shell)
gapAnchor gap = Carrier.bishopRationalEmbed (Geo.pow Geo.thirtySecond gap)

lowAnchorZero : Bishop._≃_ (lowAnchor zero) Bishop.1ℝ
lowAnchorZero = BishopLaws.≃-refl

gapAnchorZero : Bishop._≃_ (gapAnchor zero) Bishop.1ℝ
gapAnchorZero = BishopLaws.≃-refl

lowAnchorSuc : ∀ shell →
  Bishop._≃_
    (lowAnchor (suc shell))
    (Bishop._*_
      (Carrier.bishopRationalEmbed Geo.quarter)
      (lowAnchor shell))
lowAnchorSuc shell =
  BishopLaws.≃-trans
    (BishopLaws.⋆-cong
      (RationalLaws.toℚᵘ-homo-*
        Geo.quarter (Geo.pow Geo.quarter shell)))
    (BishopLaws.⋆-distrib-*
      (toℚᵘ Geo.quarter)
      (toℚᵘ (Geo.pow Geo.quarter shell)))

gapAnchorSuc : ∀ gap →
  Bishop._≃_
    (gapAnchor (suc gap))
    (Bishop._*_
      (Carrier.bishopRationalEmbed Geo.thirtySecond)
      (gapAnchor gap))
gapAnchorSuc gap =
  BishopLaws.≃-trans
    (BishopLaws.⋆-cong
      (RationalLaws.toℚᵘ-homo-*
        Geo.thirtySecond (Geo.pow Geo.thirtySecond gap)))
    (BishopLaws.⋆-distrib-*
      (toℚᵘ Geo.thirtySecond)
      (toℚᵘ (Geo.pow Geo.thirtySecond gap)))

lowAnchorNonnegative : ∀ shell →
  Bishop._≤_ Bishop.0ℝ (lowAnchor shell)
lowAnchorNonnegative shell =
  Carrier.bishopEmbedOrder
    (Geo.powNonnegative
      Geo.quarter shell Geo.quarterNonnegative)

gapAnchorNonnegative : ∀ gap →
  Bishop._≤_ Bishop.0ℝ (gapAnchor gap)
gapAnchorNonnegative gap =
  Carrier.bishopEmbedOrder
    (Geo.powNonnegative
      Geo.thirtySecond gap Geo.thirtySecondNonnegative)

record MurrayBishopCanonicalDyadicAnchorPackage : Set where
  field
    low : Nat → Bishop.ℝ
    gap : Nat → Bishop.ℝ
    lowZero : Bishop._≃_ (low zero) Bishop.1ℝ
    gapZero : Bishop._≃_ (gap zero) Bishop.1ℝ
    lowSuc : ∀ shell →
      Bishop._≃_ (low (suc shell))
        (Bishop._*_
          (Carrier.bishopRationalEmbed Geo.quarter)
          (low shell))
    gapSuc : ∀ distance →
      Bishop._≃_ (gap (suc distance))
        (Bishop._*_
          (Carrier.bishopRationalEmbed Geo.thirtySecond)
          (gap distance))
    lowNonnegative : ∀ shell → Bishop._≤_ Bishop.0ℝ (low shell)
    gapNonnegative : ∀ distance → Bishop._≤_ Bishop.0ℝ (gap distance)

open MurrayBishopCanonicalDyadicAnchorPackage public

murrayBishopCanonicalDyadicAnchors :
  MurrayBishopCanonicalDyadicAnchorPackage
murrayBishopCanonicalDyadicAnchors = record
  { low = lowAnchor
  ; gap = gapAnchor
  ; lowZero = lowAnchorZero
  ; gapZero = gapAnchorZero
  ; lowSuc = lowAnchorSuc
  ; gapSuc = gapAnchorSuc
  ; lowNonnegative = lowAnchorNonnegative
  ; gapNonnegative = gapAnchorNonnegative
  }

murrayBishopExactIntegerAnchorsClosed : Bool
murrayBishopExactIntegerAnchorsClosed = true

globalExpLogRequiredForIntegerAnchors : Bool
globalExpLogRequiredForIntegerAnchors = false

murrayBishopExactIntegerAnchorsClosedIsTrue :
  murrayBishopExactIntegerAnchorsClosed ≡ true
murrayBishopExactIntegerAnchorsClosedIsTrue = refl

globalExpLogRequiredForIntegerAnchorsIsFalse :
  globalExpLogRequiredForIntegerAnchors ≡ false
globalExpLogRequiredForIntegerAnchorsIsFalse = refl
