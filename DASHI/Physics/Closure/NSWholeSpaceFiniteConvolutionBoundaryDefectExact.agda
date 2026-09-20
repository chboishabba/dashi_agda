module DASHI.Physics.Closure.NSWholeSpaceFiniteConvolutionBoundaryDefectExact where

------------------------------------------------------------------------
-- A / EUCLIDEAN FINITE-CONVOLUTION BOUNDARY-DEFECT COMPLETION
--
-- Exact translation reindexing is natural on a periodic finite carrier but is
-- too strong for a genuine truncated R^3 cubature: translating xi -> xi-eta
-- moves nodes across the finite boundary.  The correct whole-space finite
-- identity therefore keeps the boundary error explicitly.
--
-- For one finite quadrature Q let
--
--   E_Q       = sum_i e_i,
--   delta_i   = translated-inner-sum_i - E_Q,
--   Delta_Q   = sum_i e_i delta_i,
--   F_Q       = sum_i e_i translated-inner-sum_i.
--
-- If the selected cubature proves the setoid identity
--
--   translated-inner-sum_i ~= E_Q + delta_i,
--
-- finite Bishop algebra gives
--
--   F_Q ~= E_Q^2 + Delta_Q.
--
-- Consequently for an expanding/refining Euclidean cubature sequence,
--
--   E_n -> E,      Delta_n -> 0
--
-- imply
--
--   F_n -> E^2.
--
-- This is the correct R^3 replacement for exact finite translation
-- reindexing.  The older exact-reindexing theorem is recovered by choosing
-- every delta_i = 0.  No continuum Fubini/Tonelli theorem is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rect

record FiniteTranslationDefectConvolutionQuadrature : Set₁ where
  constructor finite-translation-defect-convolution-quadrature
  field
    energy : Nat → BishopReal.ℝ
    shiftedEnergy : Nat → Nat → BishopReal.ℝ
    translationDefect : Nat → BishopReal.ℝ
    count : Nat

    translatedInnerSumWithBoundaryDefect :
      (outer : Nat) →
      BishopReal._≃_
        (BishopSequence.SeriesOf (shiftedEnergy outer) count)
        (BishopReal._+_
          (BishopSequence.SeriesOf energy count)
          (translationDefect outer))

open FiniteTranslationDefectConvolutionQuadrature public

energyMass :
  FiniteTranslationDefectConvolutionQuadrature →
  BishopReal.ℝ
energyMass Q =
  BishopSequence.SeriesOf (energy Q) (count Q)

convolutionRow :
  FiniteTranslationDefectConvolutionQuadrature →
  Nat → BishopReal.ℝ
convolutionRow Q outer =
  BishopReal._*_
    (energy Q outer)
    (BishopSequence.SeriesOf
      (shiftedEnergy Q outer)
      (count Q))

boundaryDefectRow :
  FiniteTranslationDefectConvolutionQuadrature →
  Nat → BishopReal.ℝ
boundaryDefectRow Q outer =
  BishopReal._*_
    (energy Q outer)
    (translationDefect Q outer)

boundaryDefectMass :
  FiniteTranslationDefectConvolutionQuadrature →
  BishopReal.ℝ
boundaryDefectMass Q =
  BishopSequence.SeriesOf
    (boundaryDefectRow Q)
    (count Q)

convolutionMass :
  FiniteTranslationDefectConvolutionQuadrature →
  BishopReal.ℝ
convolutionMass Q =
  BishopSequence.SeriesOf
    (convolutionRow Q)
    (count Q)

rowSplitsIntoRectanglePlusBoundaryDefect :
  (Q : FiniteTranslationDefectConvolutionQuadrature) →
  (outer : Nat) →
  BishopReal._≃_
    (convolutionRow Q outer)
    (BishopReal._+_
      (Rect.rectangleRow
        (energy Q) (energy Q)
        outer (count Q))
      (boundaryDefectRow Q outer))
rowSplitsIntoRectanglePlusBoundaryDefect Q outer =
  let
    e = energy Q outer
    E = energyMass Q
    d = translationDefect Q outer
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-congˡ
      (translatedInnerSumWithBoundaryDefect Q outer))
    (solve 3
      (λ e0 E0 d0 →
        e0 ⊗ (E0 ⊕ d0)
        ⊜ (e0 ⊗ E0) ⊕ (e0 ⊗ d0))
      BishopP.≃-refl
      e E d)

finiteSumAdditive :
  (left right : Nat → BishopReal.ℝ) →
  (count0 : Nat) →
  BishopReal._≃_
    (BishopSequence.SeriesOf
      (λ n → BishopReal._+_ (left n) (right n))
      count0)
    (BishopReal._+_
      (BishopSequence.SeriesOf left count0)
      (BishopSequence.SeriesOf right count0))
finiteSumAdditive left right zero =
  let open BishopP.ℝ-Solver
  in solve 0
    (Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ)
    BishopP.≃-refl
finiteSumAdditive left right (suc count0) =
  let
    L = BishopSequence.SeriesOf left count0
    R = BishopSequence.SeriesOf right count0
    l = left count0
    r = right count0
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (finiteSumAdditive left right count0)
      BishopP.≃-refl)
    (solve 4
      (λ L0 R0 l0 r0 →
        (L0 ⊕ R0) ⊕ (l0 ⊕ r0)
        ⊜ (L0 ⊕ l0) ⊕ (R0 ⊕ r0))
      BishopP.≃-refl
      L R l r)

convolutionMassSplits :
  (Q : FiniteTranslationDefectConvolutionQuadrature) →
  BishopReal._≃_
    (convolutionMass Q)
    (BishopReal._+_
      (Rect.rectangleSum
        (energy Q) (energy Q)
        (count Q) (count Q))
      (boundaryDefectMass Q))
convolutionMassSplits Q =
  BishopP.≃-trans
    (Ext.seriesPartialSumsCongruent
      (rowSplitsIntoRectanglePlusBoundaryDefect Q)
      (count Q))
    (finiteSumAdditive
      (λ outer →
        Rect.rectangleRow
          (energy Q) (energy Q)
          outer (count Q))
      (boundaryDefectRow Q)
      (count Q))

finiteConvolutionFactorisationWithBoundaryDefect :
  (Q : FiniteTranslationDefectConvolutionQuadrature) →
  BishopReal._≃_
    (convolutionMass Q)
    (BishopReal._+_
      (BishopReal._*_
        (energyMass Q)
        (energyMass Q))
      (boundaryDefectMass Q))
finiteConvolutionFactorisationWithBoundaryDefect Q =
  BishopP.≃-trans
    (convolutionMassSplits Q)
    (BishopP.+-cong
      (Rect.rectangleProduct
        (energy Q) (energy Q)
        (count Q) (count Q))
      BishopP.≃-refl)

record EuclideanBoundaryDefectConvolutionSequence : Set₁ where
  constructor euclidean-boundary-defect-convolution-sequence
  field
    quadrature :
      Nat → FiniteTranslationDefectConvolutionQuadrature

    continuumEnergy : BishopReal.ℝ

    energyQuadraturesConverge :
      BishopSequence._ConvergesTo_
        (λ n → energyMass (quadrature n))
        continuumEnergy

    boundaryDefectVanishes :
      BishopSequence._ConvergesTo_
        (λ n → boundaryDefectMass (quadrature n))
        BishopReal.0ℝ

open EuclideanBoundaryDefectConvolutionSequence public

energySquarePlusBoundaryDefect :
  EuclideanBoundaryDefectConvolutionSequence →
  Nat → BishopReal.ℝ
energySquarePlusBoundaryDefect Q n =
  BishopReal._+_
    (BishopReal._*_
      (energyMass (quadrature Q n))
      (energyMass (quadrature Q n)))
    (boundaryDefectMass (quadrature Q n))

energySquarePlusBoundaryDefectConverges :
  (Q : EuclideanBoundaryDefectConvolutionSequence) →
  BishopSequence._ConvergesTo_
    (energySquarePlusBoundaryDefect Q)
    (BishopReal._*_
      (continuumEnergy Q)
      (continuumEnergy Q))
energySquarePlusBoundaryDefectConverges Q =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    { xs = energySquarePlusBoundaryDefect Q }
    { ys = energySquarePlusBoundaryDefect Q }
    (λ n {{_}} → BishopP.≃-refl)
    ( BishopReal._+_
        (BishopReal._*_
          (continuumEnergy Q)
          (continuumEnergy Q))
        BishopReal.0ℝ
    , BishopSequence.xₙ+yₙ→x₀+y₀
        ( BishopReal._*_
            (continuumEnergy Q)
            (continuumEnergy Q)
        , BishopSequence.xₙyₙ→x₀y₀
            (continuumEnergy Q , energyQuadraturesConverge Q)
            (continuumEnergy Q , energyQuadraturesConverge Q)
        )
        (BishopReal.0ℝ , boundaryDefectVanishes Q)
    )

convolutionQuadraturesConvergeFromEnergyAndBoundaryDefect :
  (Q : EuclideanBoundaryDefectConvolutionSequence) →
  BishopSequence._ConvergesTo_
    (λ n → convolutionMass (quadrature Q n))
    (BishopReal._*_
      (continuumEnergy Q)
      (continuumEnergy Q))
convolutionQuadraturesConvergeFromEnergyAndBoundaryDefect Q =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    { xs = energySquarePlusBoundaryDefect Q }
    { ys = λ n → convolutionMass (quadrature Q n) }
    (λ n {{_}} →
      BishopP.≃-symm
        (finiteConvolutionFactorisationWithBoundaryDefect
          (quadrature Q n)))
    ( BishopReal._*_
        (continuumEnergy Q)
        (continuumEnergy Q)
    , energySquarePlusBoundaryDefectConverges Q
    )

exactFiniteTranslationReindexingRequiredForR3 : Bool
exactFiniteTranslationReindexingRequiredForR3 = false

euclideanBoundaryDefectRetainedExplicitly : Bool
euclideanBoundaryDefectRetainedExplicitly = true

continuumFubiniTonelliRequiredByBoundaryDefectCompletion : Bool
continuumFubiniTonelliRequiredByBoundaryDefectCompletion = false

energyLimitPlusVanishingBoundaryDefectSuffices : Bool
energyLimitPlusVanishingBoundaryDefectSuffices = true

clayPromotion : Bool
clayPromotion = false

exactFiniteTranslationReindexingRequiredForR3IsFalse :
  exactFiniteTranslationReindexingRequiredForR3 ≡ false
exactFiniteTranslationReindexingRequiredForR3IsFalse = refl

euclideanBoundaryDefectRetainedExplicitlyIsTrue :
  euclideanBoundaryDefectRetainedExplicitly ≡ true
euclideanBoundaryDefectRetainedExplicitlyIsTrue = refl

energyLimitPlusVanishingBoundaryDefectSufficesIsTrue :
  energyLimitPlusVanishingBoundaryDefectSuffices ≡ true
energyLimitPlusVanishingBoundaryDefectSufficesIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
