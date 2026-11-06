{-# OPTIONS --safe #-}
module DASHI.Analysis.RiemannOpaqueZetaHalfPlaneCountermodelExact where

------------------------------------------------------------------------
-- K04d / RH: CONCRETE COUNTERMODEL TO AN INVALID ZETA IDENTIFICATION.
--
-- The original RiemannAnalyticSubstrate.ZetaHalfPlaneLayer names the
-- proposition ZetaEqualsDirichletSeries but does not fix its semantic
-- meaning as equality of values of the selected functions.
--
-- Construct TWO inhabitants of the exact original record. They
-- share one identical carrier and every Set-valued domain/convergence
-- field, but their actual zetaHalfPlane values at zero are DIFFERENT.
--
-- Therefore no theorem deriving a fixed numerical Dirichlet value
-- from ONLY this record can be correct. A selected same-object value
-- equality must be constructed on the original Bishop carrier, not
-- supplied by an arbitrary inhabitation of the opaque record field.
--
-- This is a logical countermodel, not the positive Bishop zeta proof.
-- No postulates, rewrite bypass, or synthetic claim of RH.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic

-- A small countermodel for the INTERFACE alone. The positive zeta
-- construction must remain on RiemannBishopComplexAnalyticCarrierExact;
-- this finite carrier is only a witness to interface underdetermination.
discreteCarrier : Analytic.ComplexAnalyticCarrier
discreteCarrier = record
  { Analytic.ComplexAnalyticCarrier.Complex = Nat
  ; Analytic.ComplexAnalyticCarrier.Real = Nat
  ; Analytic.ComplexAnalyticCarrier.zeroC = zero
  ; Analytic.ComplexAnalyticCarrier.oneC = suc zero
  ; Analytic.ComplexAnalyticCarrier._+C_ = _+_
  ; Analytic.ComplexAnalyticCarrier._*C_ = _*_
  ; Analytic.ComplexAnalyticCarrier.negC = λ n → n
  ; Analytic.ComplexAnalyticCarrier.conjC = λ n → n
  ; Analytic.ComplexAnalyticCarrier.realPart = λ n → n
  ; Analytic.ComplexAnalyticCarrier.imaginaryPart = λ _ → zero
  ; Analytic.ComplexAnalyticCarrier.Function = Nat → Nat
  ; Analytic.ComplexAnalyticCarrier.apply = λ f n → f n
  ; Analytic.ComplexAnalyticCarrier.Holomorphic = λ _ → ⊤
  ; Analytic.ComplexAnalyticCarrier.Entire = λ _ → ⊤
  ; Analytic.ComplexAnalyticCarrier.Meromorphic = λ _ → ⊤
  ; Analytic.ComplexAnalyticCarrier.SimplePoleAt = λ _ _ → ⊤
  }

-- The original field `ZetaEqualsDirichletSeries` can be satisfied
-- for ANY function because its type is freely selected by the layer.
opaqueHalfPlane :
  (f : Nat → Nat) →
  Analytic.ZetaHalfPlaneLayer discreteCarrier
opaqueHalfPlane f = record
  { Analytic.ZetaHalfPlaneLayer.zetaHalfPlane = f
  ; Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne = λ _ → ⊤
  ; Analytic.ZetaHalfPlaneLayer.DirichletSeriesConverges = λ _ → ⊤
  ; Analytic.ZetaHalfPlaneLayer.ZetaEqualsDirichletSeries = λ _ → ⊤
  ; Analytic.ZetaHalfPlaneLayer.EulerProductConverges = λ _ → ⊤
  ; Analytic.ZetaHalfPlaneLayer.ZetaEqualsEulerProduct = λ _ → ⊤
  ; Analytic.ZetaHalfPlaneLayer.dirichletSeriesConverges = λ _ _ → tt
  ; Analytic.ZetaHalfPlaneLayer.zetaEqualsDirichletSeries = λ _ _ → tt
  ; Analytic.ZetaHalfPlaneLayer.eulerProductConverges = λ _ _ → tt
  ; Analytic.ZetaHalfPlaneLayer.zetaEqualsEulerProduct = λ _ _ → tt
  }

zeroHalfPlane oneHalfPlane : Analytic.ZetaHalfPlaneLayer discreteCarrier
zeroHalfPlane = opaqueHalfPlane (λ _ → zero)
oneHalfPlane  = opaqueHalfPlane (λ _ → suc zero)

zeroIsNotOne : zero ≡ suc zero → ⊥
zeroIsNotOne ()

-- Both are original-record inhabitants, yet their selected
-- zetaHalfPlane functions cannot agree even at this one argument.
opaqueHalfPlaneCannotIdentifyZetaValues :
  Analytic.ComplexAnalyticCarrier.apply discreteCarrier
    (Analytic.ZetaHalfPlaneLayer.zetaHalfPlane zeroHalfPlane) zero
  ≡
  Analytic.ComplexAnalyticCarrier.apply discreteCarrier
    (Analytic.ZetaHalfPlaneLayer.zetaHalfPlane oneHalfPlane) zero
  → ⊥
opaqueHalfPlaneCannotIdentifyZetaValues = zeroIsNotOne
