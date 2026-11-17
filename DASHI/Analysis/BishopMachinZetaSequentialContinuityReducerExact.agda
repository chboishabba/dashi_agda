module DASHI.Analysis.BishopMachinZetaSequentialContinuityReducerExact where

------------------------------------------------------------------------
-- K04d: EPSILON/DELTA -> ACTUAL COMPLETED-ZETA SEQUENTIAL LIMIT.
--
-- The proof is on the ORIGINAL pinned Bishop.ℝ and its genuine
-- Sequence._ConvergesTo_ datatype. It uses the original epsilon
-- extraction theorem, not an assumed sequence-continuity conclusion.
-- The actual completed-zeta and actual original Machin q_n are the
-- consumers. Continuity itself remains an EXPLICIT missing analytic
-- proof, not a field of RiemannAnalyticSubstrate.Meromorphic and not
-- an imported classical/Lean theorem.
--
-- Original mathematics: Cauchy sequential continuity, Riemann 1859;
-- Bishop & Bridges, Constructive Analysis, Springer (1985),
-- DOI 10.1007/978-3-642-61667-9.
-- Source code: Zachary Murray, arXiv:2205.08354 (2022),
-- pinned viktorcsimma/bishop Sequence, Real, RealProperties.
-- All source ownership is retained. Source-written; kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; _<_)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Data.Product.Base using (_×_; _,_; Σ; proj₁; proj₂)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Rational
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Analysis.BishopMachinZetaRegularHalfPlaneExact as Zeta

-- This is an ACTUAL real epsilon-delta function property, not
-- sequential continuity disguised as an input premise.
BishopContinuousAt :
  (f : R.ℝ → R.ℝ) → (point : R.ℝ) → Set
BishopContinuousAt f point =
  (epsilon : R.ℝ) →
  R.Positive epsilon →
  Σ R.ℝ (λ delta →
    R.Positive delta ×
    ((x : R.ℝ) →
      R._<_ (R.∣_∣ (R._-_ x point)) delta →
      R._<_
        (R.∣_∣ (R._-_ (f x) (f point)))
        epsilon))

-- Original Bishop's constructive convergence is quantified over
-- arbitrary positive reciprocal Nat precision. The epsilon witness
-- below really is positive, using stdlib rational decidable strict
-- order and the original rational-to-Bishop order embedding.
reciprocalNatPositive :
  (k : Nat) → R.Positive (R._⋆ (+ 1 / suc k))
reciprocalNatPositive k =
  RP.0<x⇒posx
    (RP.p<q⇒p⋆<q⋆
      Q.0ℚᵘ
      (+ 1 / suc k)
      (toWitness
        {a? = QP._<?_ Q.0ℚᵘ (+ 1 / suc k)} _))

bishopContinuousImageConverges :
  (f : R.ℝ → R.ℝ) →
  (point : R.ℝ) →
  BishopContinuousAt f point →
  (history : Nat → R.ℝ) →
  Seq._ConvergesTo_ history point →
  Seq._ConvergesTo_
    (λ n → f (history n))
    (f point)
bishopContinuousImageConverges f point continuity history converges =
  Seq.con* (λ
    { (suc k) →
      let
        epsilon = R._⋆ (+ 1 / suc k)
        continuousWitness =
          continuity epsilon (reciprocalNatPositive k)
        delta = proj₁ continuousWitness
        deltaPositive = proj₁ (proj₂ continuousWitness)
        localInequality = proj₂ (proj₂ continuousWitness)
        inputReceipt =
          Seq.fast-ε-from-convergence
            (point , converges)
            delta
            deltaPositive
      in
      proj₁ inputReceipt ,
      (λ n large →
        RP.<⇒≤
          (localInequality
            (history n)
            (proj₂ inputReceipt n large)))
    })

-- Instantiate the exact function used by the original CompletedRiemannZeta.
-- The imaginary component is not silently assumed to vanish: both real
-- and imaginary evaluations receive their OWN continuity witnesses.
module AtActualCompletedZeta
  (functions : BC.BishopComplexAnalyticFunctionLayer)
  (gamma : Analytic.GammaMellinLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (halfPlane : Analytic.ZetaHalfPlaneLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (completed : Analytic.CompletedRiemannZeta
    (BC.bishopComplexAnalyticCarrier functions) gamma halfPlane)
  where

  module Original =
    Zeta.AtActualBishopCarrier functions gamma halfPlane completed

  zetaRealOnMachinAxis : R.ℝ → R.ℝ
  zetaRealOnMachinAxis x =
    BC.re
      (BC.apply functions
        (Analytic.CompletedRiemannZeta.zeta completed)
        (BC.bishop-complex x R.0ℝ))

  zetaImagOnMachinAxis : R.ℝ → R.ℝ
  zetaImagOnMachinAxis x =
    BC.im
      (BC.apply functions
        (Analytic.CompletedRiemannZeta.zeta completed)
        (BC.bishop-complex x R.0ℝ))

  realAxisZetaAtStage :
    ∀ n →
    zetaRealOnMachinAxis
      (R._⋆ (Rational.qMachinStage n))
      ≡ BC.re (Original.zetaAtStage n)
  realAxisZetaAtStage n = refl

  imagAxisZetaAtStage :
    ∀ n →
    zetaImagOnMachinAxis
      (R._⋆ (Rational.qMachinStage n))
      ≡ BC.im (Original.zetaAtStage n)
  imagAxisZetaAtStage n = refl

  realAxisZetaAtLimit :
    zetaRealOnMachinAxis Machin.bishopMachinPi
      ≡ BC.re Original.zetaAtLimit
  realAxisZetaAtLimit = refl

  imagAxisZetaAtLimit :
    zetaImagOnMachinAxis Machin.bishopMachinPi
      ≡ BC.im Original.zetaAtLimit
  imagAxisZetaAtLimit = refl

  -- These are exact analytic obligations, not auto-filled records.
  -- The original `Meromorphic` field does not entail either of them.
  realComponentConvergesFromActualContinuity :
    BishopContinuousAt
      zetaRealOnMachinAxis Machin.bishopMachinPi →
    Seq._ConvergesTo_
      (λ n → BC.re (Original.zetaAtStage n))
      (BC.re Original.zetaAtLimit)
  realComponentConvergesFromActualContinuity continuity =
    bishopContinuousImageConverges
      zetaRealOnMachinAxis
      Machin.bishopMachinPi
      continuity
      (λ n → R._⋆ (Rational.qMachinStage n))
      Rational.rationalMachinStagesConvergeToOriginalMachinPi

  imagComponentConvergesFromActualContinuity :
    BishopContinuousAt
      zetaImagOnMachinAxis Machin.bishopMachinPi →
    Seq._ConvergesTo_
      (λ n → BC.im (Original.zetaAtStage n))
      (BC.im Original.zetaAtLimit)
  imagComponentConvergesFromActualContinuity continuity =
    bishopContinuousImageConverges
      zetaImagOnMachinAxis
      Machin.bishopMachinPi
      continuity
      (λ n → R._⋆ (Rational.qMachinStage n))
      Rational.rationalMachinStagesConvergeToOriginalMachinPi
