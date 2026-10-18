{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonAffineMarkedActivityExact where

------------------------------------------------------------------------
-- Literal affine two-Wilson factor -> marked polymer activity threshold.
--
-- The observable calculation already proves, on |s|,|t| <= 9/100 and
-- |W_L|,|W_R| <= 1,
--
--   |(1+s W_L)(1+t W_R)| <= 6/5.
--
-- If the physical base polymer activity obeys the existing 1/16 bound, the
-- literal two-Wilson marked activity therefore obeys
--
--   |z_{s,t}(gamma)|
--     <= (6/5)(1/16)
--      = 3/40
--      < 1/12.
--
-- Thus the source deformation itself pays the exact marked-inflation arithmetic
-- required by the existing Fernandez--Procacci lane. What remains physical is
-- identifying the actual finite YM polymer activity with baseActivity below;
-- no abstract marked-activity inflation token is required afterward.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonAffineSourceBoundExact as Affine

record LiteralTwoWilsonAffinePolymerMark (Polymer : Set) : Set₁ where
  field
    baseActivity : Polymer → ℚ
    baseActivityNonnegative : ∀ polymer → 0ℚ ≤ baseActivity polymer
    baseActivityBelowOneSixteenth : ∀ polymer →
      baseActivity polymer ≤ FP.rhoBase

    leftWilsonValue rightWilsonValue : Polymer → ℚ
    leftWilsonUnitBound : ∀ polymer →
      ∣ leftWilsonValue polymer ∣ ≤ 1ℚ
    rightWilsonUnitBound : ∀ polymer →
      ∣ rightWilsonValue polymer ∣ ≤ 1ℚ

    leftSource rightSource : ℚ
    leftSourceInsideRadius : Affine.SourceInsideRadius leftSource
    rightSourceInsideRadius : Affine.SourceInsideRadius rightSource

open LiteralTwoWilsonAffinePolymerMark public

literalAffineMultiplier :
  ∀ {Polymer} →
  LiteralTwoWilsonAffinePolymerMark Polymer →
  Polymer → ℚ
literalAffineMultiplier dataSet polymer =
  Affine.twoWilsonAffineFactor
    (leftSource dataSet)
    (rightSource dataSet)
    (leftWilsonValue dataSet polymer)
    (rightWilsonValue dataSet polymer)

literalMarkedActivityNorm :
  ∀ {Polymer} →
  LiteralTwoWilsonAffinePolymerMark Polymer →
  Polymer → ℚ
literalMarkedActivityNorm dataSet polymer =
  ∣ literalAffineMultiplier dataSet polymer ∣
    * baseActivity dataSet polymer

literalAffineMultiplierBelowSixFifths :
  ∀ {Polymer}
    (dataSet : LiteralTwoWilsonAffinePolymerMark Polymer)
    polymer →
  ∣ literalAffineMultiplier dataSet polymer ∣ ≤ FP.markedInflation
literalAffineMultiplierBelowSixFifths dataSet polymer =
  Affine.twoWilsonAffineFactorBelowSixFifths
    (leftSource dataSet)
    (rightSource dataSet)
    (leftWilsonValue dataSet polymer)
    (rightWilsonValue dataSet polymer)
    (leftSourceInsideRadius dataSet)
    (rightSourceInsideRadius dataSet)
    (leftWilsonUnitBound dataSet polymer)
    (rightWilsonUnitBound dataSet polymer)

literalMarkedActivityBelowInflatedBase :
  ∀ {Polymer}
    (dataSet : LiteralTwoWilsonAffinePolymerMark Polymer)
    polymer →
  literalMarkedActivityNorm dataSet polymer
  ≤ FP.markedInflation * baseActivity dataSet polymer
literalMarkedActivityBelowInflatedBase dataSet polymer =
  ℚP.*-mono-≤
    (ℚP.0≤∣p∣ (literalAffineMultiplier dataSet polymer))
    (literalAffineMultiplierBelowSixFifths dataSet polymer)
    (baseActivityNonnegative dataSet polymer)
    ℚP.≤-refl

literalMarkedActivityBelowThreeFortieths :
  ∀ {Polymer}
    (dataSet : LiteralTwoWilsonAffinePolymerMark Polymer)
    polymer →
  literalMarkedActivityNorm dataSet polymer
  ≤ FP.markedActivityMaximum
literalMarkedActivityBelowThreeFortieths dataSet polymer =
  let
    inflatedBase :
      FP.markedInflation * baseActivity dataSet polymer
      ≤ FP.markedInflation * FP.rhoBase
    inflatedBase =
      ℚP.*-mono-≤
        (ℚP.nonNegative⁻¹ FP.markedInflation)
        ℚP.≤-refl
        (baseActivityNonnegative dataSet polymer)
        (baseActivityBelowOneSixteenth dataSet polymer)
  in
  ℚP.≤-trans
    (literalMarkedActivityBelowInflatedBase dataSet polymer)
    (subst
      (λ upper →
        FP.markedInflation * baseActivity dataSet polymer ≤ upper)
      FP.markedBaseActivityExact
      inflatedBase)

literalMarkedActivityBelowFPThreshold :
  ∀ {Polymer}
    (dataSet : LiteralTwoWilsonAffinePolymerMark Polymer)
    polymer →
  literalMarkedActivityNorm dataSet polymer ≤ FP.rhoFPMax
literalMarkedActivityBelowFPThreshold dataSet polymer =
  ℚP.≤-trans
    (literalMarkedActivityBelowThreeFortieths dataSet polymer)
    FP.markedActivityBelowFPMaximum
