module DASHI.Analysis.BishopMachinZetaRegularHalfPlaneExact where

------------------------------------------------------------------------
-- K04d: SAME BISHOP REAL SEQUENCE INSIDE THE ORIGINAL ANALYTIC
-- RIEMANN ZETA CONTRACT. No artificial zero/sieve/zeta identity.
--
-- Source: Riemann (1859), classical zeta Dirichlet series/Euler product;
-- original DASHI RiemannAnalyticSubstrate, concrete
-- RiemannBishopComplexAnalyticCarrierExact and genuine Bishop Machin.
-- Bishop/Bridges (1985), DOI 10.1007/978-3-642-61667-9;
-- Murray (2022), arXiv:2205.08354.
--
-- The existing analytic substrate's half-plane agreement is a
-- theorem FIELD, and remains supplied by its analytic implementer.
-- This module proves the actual points/limits and instantiates the
-- supplied agreement on the IDENTICAL completed-zeta function.
-- It does not derive continuity from the abstract word Meromorphic,
-- nor does SimplePoleAtOne assert absence of all other poles.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_; _<_)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (proj₁; proj₂)
open import Agda.Builtin.Equality using (_≡_; refl)
import Real as Bishop
import RealProperties as RP
import Sequence as Series

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Rational
import DASHI.Analysis.BishopMachinEventualHalfPlaneExact as Eventual
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Window
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin

module AtActualBishopCarrier
  (functions : BC.BishopComplexAnalyticFunctionLayer)
  (gamma : Analytic.GammaMellinLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (halfPlane : Analytic.ZetaHalfPlaneLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (completed : Analytic.CompletedRiemannZeta
    (BC.bishopComplexAnalyticCarrier functions) gamma halfPlane)
  where

  carrier : Analytic.ComplexAnalyticCarrier
  carrier = BC.bishopComplexAnalyticCarrier functions

  stagePoint : Nat → BC.BishopComplex
  stagePoint n =
    BC.bishop-complex
      (Bishop._⋆ (Rational.qMachinStage n))
      Bishop.0ℝ

  limitPoint : BC.BishopComplex
  limitPoint =
    BC.bishop-complex Machin.bishopMachinPi Bishop.0ℝ

  -- Actual, not synthetically introduced, stage and terminal coordinates.
  stageRealPart : ∀ n →
    BC.re (stagePoint n) ≡ Bishop._⋆ (Rational.qMachinStage n)
  stageRealPart n = refl

  limitRealPart : BC.re limitPoint ≡ Machin.bishopMachinPi
  limitRealPart = refl

  stageImaginaryZero : ∀ n →
    BC.im (stagePoint n) ≡ Bishop.0ℝ
  stageImaginaryZero n = refl

  limitImaginaryZero : BC.im limitPoint ≡ Bishop.0ℝ
  limitImaginaryZero = refl

  -- The real part of THE ACTUAL COMPLEX ARGUMENT converges to the
  -- actual Bishop Machin real; the imaginary part is identically 0.
  realPartConverges :
    Series._ConvergesTo_
      (λ n → BC.re (stagePoint n))
      (BC.re limitPoint)
  realPartConverges =
    Rational.rationalMachinStagesConvergeToOriginalMachinPi

  imaginaryPartConverges :
    Series._ConvergesTo_
      (λ n → BC.im (stagePoint n))
      (BC.im limitPoint)
  imaginaryPartConverges =
    Series.xₙ≃c⇒xₙ→c
      (λ {(suc n) → RP.≃-refl})

  zetaAtStage : Nat → BC.BishopComplex
  zetaAtStage n =
    BC.apply functions
      (Analytic.CompletedRiemannZeta.zeta completed)
      (stagePoint n)

  zetaAtLimit : BC.BishopComplex
  zetaAtLimit =
    BC.apply functions
      (Analytic.CompletedRiemannZeta.zeta completed)
      limitPoint

  halfPlaneZetaAtStage : Nat → BC.BishopComplex
  halfPlaneZetaAtStage n =
    BC.apply functions
      (Analytic.ZetaHalfPlaneLayer.zetaHalfPlane halfPlane)
      (stagePoint n)

  halfPlaneZetaAtLimit : BC.BishopComplex
  halfPlaneZetaAtLimit =
    BC.apply functions
      (Analytic.ZetaHalfPlaneLayer.zetaHalfPlane halfPlane)
      limitPoint

  -- Same-object agreement in the ACTUAL half-plane domain.
  -- Its proof is imported from the original CompletedRiemannZeta record;
  -- no fabricated global equality of entire/meromorphic functions.
  originalZetaEqualsDirichletAtStage :
    (n : Nat) →
    Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne
      halfPlane (stagePoint n) →
    zetaAtStage n ≡ halfPlaneZetaAtStage n
  originalZetaEqualsDirichletAtStage n regular =
    Analytic.CompletedRiemannZeta.agreesWithHalfPlane
      completed (stagePoint n) regular

  originalZetaEqualsDirichletAtLimit :
    Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne
      halfPlane limitPoint →
    zetaAtLimit ≡ halfPlaneZetaAtLimit
  originalZetaEqualsDirichletAtLimit regular =
    Analytic.CompletedRiemannZeta.agreesWithHalfPlane
      completed limitPoint regular

  -- Required next mathematical proofs, NOT discharged here:
  -- K04d1: regularity of actual q_n/limit points in sigma>1
  --         from true Bishop order (the source has 3<pi_M<22/7).
  -- K04d2: continuity of zeta/Dirichlet series on these points,
  --         including local uniform convergence and no poles.
  -- K04d3: true coordinatewise convergence of zetaAtStage to
  --         zetaAtLimit, as a *derived* theorem from K04d2.


  ------------------------------------------------------------------------
  -- K04d1: TRUE BISHOP ORDER REGULARITY OF ALL SUFFICIENTLY LATE
  -- ORIGINAL POINTS. The existing generic analytic carrier's
  -- realPartGreaterThanOne predicate is opaque; domainAdequacy is
  -- consequently explicit, not fabricated.
  ------------------------------------------------------------------------

  oneStrictlyBelowThree : Bishop._<_ Bishop.1ℝ (Window.embed Window.three)
  oneStrictlyBelowThree =
    RP.p<q⇒p⋆<q⋆
      (+ 1 / 1)
      Window.three
      (toWitness
        {a? = QP._<?_ (+ 1 / 1) Window.three} _)

  actualStageRealPartEventuallyAboveOne :
    Σ Nat (λ start →
      ∀ n → start ≤ n →
      Bishop._<_ Bishop.1ℝ (BC.re (stagePoint n)))
  actualStageRealPartEventuallyAboveOne =
    proj₁ Eventual.machinRationalStagesEventuallyAboveThree ,
    (λ n nLarge →
      RP.<-trans
        oneStrictlyBelowThree
        (proj₂ Eventual.machinRationalStagesEventuallyAboveThree
          n nLarge))

  actualStageEventuallyInOriginalZetaDomain :
    ((point : BC.BishopComplex) →
      Bishop._<_ Bishop.1ℝ (BC.re point) →
      Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne
        halfPlane point) →
    Σ Nat (λ start →
      ∀ n → start ≤ n →
      Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne
        halfPlane (stagePoint n))
  actualStageEventuallyInOriginalZetaDomain domainAdequacy =
    proj₁ actualStageRealPartEventuallyAboveOne ,
    (λ n nLarge →
      domainAdequacy (stagePoint n)
        (proj₂ actualStageRealPartEventuallyAboveOne
          n nLarge))

  -- The ORIGINAL completed-zeta function agrees with the ORIGINAL
  -- half-plane function at each sufficiently late actual q_n.
  -- This is not a continuity theorem, nor an analytic realization.
  actualZetaEqualsOriginalDirichletEventually :
    ((point : BC.BishopComplex) →
      Bishop._<_ Bishop.1ℝ (BC.re point) →
      Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne
        halfPlane point) →
    Σ Nat (λ start →
      ∀ n → start ≤ n →
      zetaAtStage n ≡ halfPlaneZetaAtStage n)
  actualZetaEqualsOriginalDirichletEventually domainAdequacy =
    proj₁ (actualStageEventuallyInOriginalZetaDomain domainAdequacy) ,
    (λ n nLarge →
      originalZetaEqualsDirichletAtStage n
        (proj₂ (actualStageEventuallyInOriginalZetaDomain domainAdequacy)
          n nLarge))

