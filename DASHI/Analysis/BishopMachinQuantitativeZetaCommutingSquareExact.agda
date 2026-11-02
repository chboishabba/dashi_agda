module DASHI.Analysis.BishopMachinQuantitativeZetaCommutingSquareExact where

------------------------------------------------------------------------
-- K04b/K04d: ONE ACTUAL MACHIN -> BISHOP -> RIEMANN ZETA SQUARE.
--
--       rational q_n ---------> Bishop embedding (q_n)
--          |                            |
--          | finite same-object         | Bishop complex (Re,0)
--          v                            v
--   signed finite series             original zeta(s_n)
--          |                            |
--          | quantitative limit         | original half-plane agreement
--          v                            v
--     bishopMachinPi -----------> original zeta(pi_M)
--
-- The finite left triangle is exact in the Bishop real setoid.
-- The K04b 4/25^n and 8/25^n bounds are imported, not reproved.
-- The right analytic square is an actual function evaluation, NOT
-- only a source-name alignment. The domain/continuity witnesses
-- remain explicit because the existing Riemann analytic layer's
-- generic Meromorphic and DirichletSeriesConverges fields are not
-- a same-object Bishop exp/log construction or continuity proof.
--
-- Attribution: Machin (1706), Riemann (1859), Bishop & Bridges
-- (1985, DOI 10.1007/978-3-642-61667-9), Murray (2022,
-- arXiv:2205.08354), original pinned Bishop and original DASHI
-- analytic/quantitative owners. Source-written only; kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Agda.Builtin.Sigma using (Σ)

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (ℚᵘ; _/_)
import Real as Bishop
import RealProperties as RP
import Sequence as Series

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopMachinZetaRegularHalfPlaneExact as OriginalZeta
import DASHI.Analysis.BishopMachinZetaSequentialContinuityReducerExact as Continuity
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Rational
import DASHI.Analysis.BishopMachinGeometricBishopRateExact as Rate
import DASHI.Analysis.BishopMachinSignedFiniteHistoryExact as Signed
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Window
import DASHI.Analysis.BishopMachinCombinedRemainderBoundExact as Combined

------------------------------------------------------------------------
-- Rational constant: avoids an implicit integer/real coercion in
-- the K04b two-index commuting-square bound.
------------------------------------------------------------------------

eight : ℚᵘ
eight = (+ 8 / 1)

module AtOriginalCompletedZeta
  (functions : BC.BishopComplexAnalyticFunctionLayer)
  (gamma : Analytic.GammaMellinLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (halfPlane : Analytic.ZetaHalfPlaneLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (completed : Analytic.CompletedRiemannZeta
    (BC.bishopComplexAnalyticCarrier functions) gamma halfPlane)
  where

  module Z = OriginalZeta.AtActualBishopCarrier
    functions gamma halfPlane completed
  module C = Continuity.AtActualCompletedZeta
    functions gamma halfPlane completed

  stageBishop : Nat → Bishop.ℝ
  stageBishop n = Bishop._⋆ (Rational.qMachinStage n)

  -- The first triangle commutes at EVERY index, including stage zero.
  finiteStageSquare :
    (n : Nat) →
    Bishop._≃_
      (BC.re (Z.stagePoint n))
      (Signed.machinSignedPartialStage n)
  finiteStageSquare n =
    Rational.qMachinStageEmbedsAsOriginalBishopPartial n

  -- Explicitly transfer the actual K04b quantitative estimates
  -- through the very same complex argument used by the original zeta.
  stageSquareRate :
    (n : Nat) →
    Bishop._≤_
      (Bishop.∣_∣
        (Bishop._-_
          (BC.re Z.limitPoint)
          (BC.re (Z.stagePoint n))))
      (Bishop._*_
        (Bishop.pow Rate.oneOver25 n)
        Combined.four)
  stageSquareRate n = Rate.machinBishopFourOver25Pow n

  stageSquareCauchy :
    (n j k : Nat) → n ≤ j → n ≤ k →
    Bishop._≤_
      (Bishop.∣_∣
        (Bishop._-_
          (BC.re (Z.stagePoint j))
          (BC.re (Z.stagePoint k))))
      (Bishop._*_
        (Bishop._⋆ (eight))
        (Bishop.pow Rate.oneOver25 n))
  stageSquareCauchy n j k nj nk =
    Rate.machinBishopEightOver25PowCauchy n j k nj nk

  stagePointRealConverges :
    Series._ConvergesTo_
      (λ n → BC.re (Z.stagePoint n))
      (BC.re Z.limitPoint)
  stagePointRealConverges = Z.realPartConverges

  limitInsideRealHalfPlane :
    Bishop._<_ Bishop.1ℝ (BC.re Z.limitPoint)
  limitInsideRealHalfPlane =
    RP.<-trans
      Z.oneStrictlyBelowThree
      Window.threeBelowMachinPi

  -- All three analytic obligations are named at their actual owner.
  -- They are not asserted, filled with trivially true Sets, or obtained
  -- from the opaque Meromorphic field of the original substrate.
  record AnalyticSameObjectGate : Set₁ where
    field
      domainAdequacy :
        (point : BC.BishopComplex) →
        Bishop._<_ Bishop.1ℝ (BC.re point) →
        Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne
          halfPlane point
      completedZetaRealContinuous :
        Continuity.BishopContinuousAt
          C.zetaRealOnMachinAxis Machin.bishopMachinPi
      completedZetaImagContinuous :
        Continuity.BishopContinuousAt
          C.zetaImagOnMachinAxis Machin.bishopMachinPi

  open AnalyticSameObjectGate public

  stageDomainEventually :
    (gate : AnalyticSameObjectGate) →
    Σ Nat (λ start →
      ∀ n → start ≤ n →
      Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne
        halfPlane (Z.stagePoint n))
  stageDomainEventually gate =
    Z.actualStageEventuallyInOriginalZetaDomain
      (domainAdequacy gate)

  originalZetaAgreesOnTail :
    (gate : AnalyticSameObjectGate) →
    Σ Nat (λ start →
      ∀ n → start ≤ n →
      Z.zetaAtStage n ≡ Z.halfPlaneZetaAtStage n)
  originalZetaAgreesOnTail gate =
    Z.actualZetaEqualsOriginalDirichletEventually
      (domainAdequacy gate)

  originalZetaAgreesAtLimit :
    (gate : AnalyticSameObjectGate) →
    Z.zetaAtLimit ≡ Z.halfPlaneZetaAtLimit
  originalZetaAgreesAtLimit gate =
    Z.originalZetaEqualsDirichletAtLimit
      (domainAdequacy gate Z.limitPoint limitInsideRealHalfPlane)

  -- True coordinatewise convergence of the ORIGINAL completed-zeta
  -- evaluations, not of an unrelated zeta-like sequence.
  completedZetaSquareConverges :
    (gate : AnalyticSameObjectGate) →
    (Series._ConvergesTo_
      (λ n → BC.re (Z.zetaAtStage n))
      (BC.re Z.zetaAtLimit))
    ×
    (Series._ConvergesTo_
      (λ n → BC.im (Z.zetaAtStage n))
      (BC.im Z.zetaAtLimit))
  completedZetaSquareConverges gate =
    C.realComponentConvergesFromActualContinuity
      (completedZetaRealContinuous gate)
    ,
    C.imagComponentConvergesFromActualContinuity
      (completedZetaImagContinuous gate)

  -- The two routes through the right square agree after applying
  -- either original complex coordinate; this uses only the
  -- original completed-zeta agreesWithHalfPlane theorem field.
  stageZetaRealSquare :
    (n : Nat) →
    Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne
      halfPlane (Z.stagePoint n) →
    BC.re (Z.zetaAtStage n) ≡ BC.re (Z.halfPlaneZetaAtStage n)
  stageZetaRealSquare n regular =
    cong BC.re (Z.originalZetaEqualsDirichletAtStage n regular)

  stageZetaImagSquare :
    (n : Nat) →
    Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne
      halfPlane (Z.stagePoint n) →
    BC.im (Z.zetaAtStage n) ≡ BC.im (Z.halfPlaneZetaAtStage n)
  stageZetaImagSquare n regular =
    cong BC.im (Z.originalZetaEqualsDirichletAtStage n regular)

