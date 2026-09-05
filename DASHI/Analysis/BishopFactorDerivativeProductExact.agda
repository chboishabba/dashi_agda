module DASHI.Analysis.BishopFactorDerivativeProductExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as Bishop
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as PowerFactor

------------------------------------------------------------------------
-- BISHOP FACTOR DERIVATIVE: IDENTITY, CONTINUITY, PRODUCT RULE
--
-- The factor derivative is strong enough to compile ordinary first-order
-- calculus internally.  In particular differentiability implies sequential
-- continuity because
--
--   f(x+h)-f(x) ~= h q(h),  h_j -> 0,  q(h_j) -> f'(x),
--
-- hence h_j q(h_j) -> 0.
------------------------------------------------------------------------

factorDerivativeIdentity :
  ∀ point →
  Factor.BishopFactorDerivativeAt
    (λ x → x)
    point Bishop.1ℝ
factorDerivativeIdentity point = record
  { Factor.quotient = λ _ → Bishop.1ℝ
  ; Factor.incrementFactorisation = λ h →
      let open BishopP.ℝ-Solver in
      solve 2
        (λ x h′ → (x ⊕ h′) ⊖ x ⊜ h′ ⊗ Κ 1ℚᵘ)
        BishopP.≃-refl point h
  ; Factor.quotientConvergesOnNullSequences = λ perturbationConverges →
      PowerFactor.constantConverges Bishop.1ℝ
  }

factorDerivativeSequentialContinuity :
  ∀ {f point derivativeValue} →
  Factor.BishopFactorDerivativeAt f point derivativeValue →
  ∀ {perturbation : Nat → Bishop.ℝ} →
  BishopSequence._ConvergesTo_ perturbation Bishop.0ℝ →
  BishopSequence._ConvergesTo_
    (λ index → f (Bishop._+_ point (perturbation index)))
    (f point)
factorDerivativeSequentialContinuity
    {f} {point} {derivativeValue} D {perturbation} perturbationConverges =
  let
    quotientConvergent : BishopSequence._isConvergent
      (λ index → Factor.quotient D (perturbation index))
    quotientConvergent =
      derivativeValue ,
      Factor.quotientConvergesOnNullSequences D perturbationConverges

    perturbationConvergent : BishopSequence._isConvergent perturbation
    perturbationConvergent = Bishop.0ℝ , perturbationConverges

    incrementProductConvergent : BishopSequence._isConvergent
      (λ index →
        Bishop._*_
          (perturbation index)
          (Factor.quotient D (perturbation index)))
    incrementProductConvergent =
      Bishop._*_ Bishop.0ℝ derivativeValue ,
      BishopSequence.xₙyₙ→x₀y₀
        perturbationConvergent quotientConvergent

    reconstructed : Nat → Bishop.ℝ
    reconstructed index =
      Bishop._+_
        (f point)
        (Bishop._*_
          (perturbation index)
          (Factor.quotient D (perturbation index)))

    reconstructedConverges : BishopSequence._isConvergent reconstructed
    reconstructedConverges =
      Bishop._+_ (f point) (Bishop._*_ Bishop.0ℝ derivativeValue) ,
      BishopSequence.xₙ+yₙ→x₀+y₀
        (f point , PowerFactor.constantConverges (f point))
        incrementProductConvergent

    actualIsReconstructed : ∀ index →
      Bishop._≃_
        (f (Bishop._+_ point (perturbation index)))
        (reconstructed index)
    actualIsReconstructed index =
      let
        h = perturbation index
        shifted = f (Bishop._+_ point h)
        base = f point
        q = Factor.quotient D h
        open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 2
          (λ shifted′ base′ →
            shifted′ ⊜ base′ ⊕ (shifted′ ⊖ base′))
          BishopP.≃-refl shifted base)
        (BishopP.+-cong
          BishopP.≃-refl
          (Factor.incrementFactorisation D h))

    actualConvergesToRawLimit :
      BishopSequence._ConvergesTo_
        (λ index → f (Bishop._+_ point (perturbation index)))
        (Bishop._+_ (f point) (Bishop._*_ Bishop.0ℝ derivativeValue))
    actualConvergesToRawLimit =
      BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ {(suc index) →
          BishopP.≃-symm (actualIsReconstructed (suc index))})
        reconstructedConverges

    rawLimitIsBase :
      Bishop._≃_
        (Bishop._+_ (f point) (Bishop._*_ Bishop.0ℝ derivativeValue))
        (f point)
    rawLimitIsBase =
      let open BishopP.ℝ-Solver in
      solve 1
        (λ base → base ⊕ (Κ 0ℚᵘ ⊗ derivativeValue) ⊜ base)
        BishopP.≃-refl
        (f point)
  in
  BishopSequence.xₙ→x∧x≃y⇒xₙ→y
    actualConvergesToRawLimit rawLimitIsBase

factorDerivativeProduct :
  ∀ {f g point df dg} →
  Factor.BishopFactorDerivativeAt f point df →
  Factor.BishopFactorDerivativeAt g point dg →
  Factor.BishopFactorDerivativeAt
    (λ x → Bishop._*_ (f x) (g x))
    point
    (Bishop._+_
      (Bishop._*_ df (g point))
      (Bishop._*_ (f point) dg))
factorDerivativeProduct {f} {g} {point} {df} {dg} F G = record
  { Factor.quotient = λ h →
      Bishop._+_
        (Bishop._*_
          (Factor.quotient F h)
          (g (Bishop._+_ point h)))
        (Bishop._*_
          (f point)
          (Factor.quotient G h))
  ; Factor.incrementFactorisation = λ h →
      let
        f1 = f (Bishop._+_ point h)
        f0 = f point
        g1 = g (Bishop._+_ point h)
        g0 = g point
        qf = Factor.quotient F h
        qg = Factor.quotient G h
        open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 4
          (λ f1′ f0′ g1′ g0′ →
            (f1′ ⊗ g1′) ⊖ (f0′ ⊗ g0′)
            ⊜ ((f1′ ⊖ f0′) ⊗ g1′)
              ⊕ (f0′ ⊗ (g1′ ⊖ g0′)))
          BishopP.≃-refl f1 f0 g1 g0)
        (BishopP.≃-trans
          (BishopP.+-cong
            (BishopP.*-cong
              (Factor.incrementFactorisation F h)
              BishopP.≃-refl)
            (BishopP.*-cong
              BishopP.≃-refl
              (Factor.incrementFactorisation G h)))
          (solve 5
            (λ h′ qf′ g1′ f0′ qg′ →
              ((h′ ⊗ qf′) ⊗ g1′)
                ⊕ (f0′ ⊗ (h′ ⊗ qg′))
              ⊜ h′ ⊗ ((qf′ ⊗ g1′) ⊕ (f0′ ⊗ qg′)))
            BishopP.≃-refl h qf g1 f0 qg))
  ; Factor.quotientConvergesOnNullSequences = λ {perturbation} perturbationConverges →
      let
        qfConvergent : BishopSequence._isConvergent
          (λ index → Factor.quotient F (perturbation index))
        qfConvergent =
          df , Factor.quotientConvergesOnNullSequences F perturbationConverges

        shiftedGConvergent : BishopSequence._isConvergent
          (λ index → g (Bishop._+_ point (perturbation index)))
        shiftedGConvergent =
          g point , factorDerivativeSequentialContinuity G perturbationConverges

        leftProductConvergent : BishopSequence._isConvergent
          (λ index →
            Bishop._*_
              (Factor.quotient F (perturbation index))
              (g (Bishop._+_ point (perturbation index))))
        leftProductConvergent =
          Bishop._*_ df (g point) ,
          BishopSequence.xₙyₙ→x₀y₀ qfConvergent shiftedGConvergent

        qgConvergent : BishopSequence._isConvergent
          (λ index → Factor.quotient G (perturbation index))
        qgConvergent =
          dg , Factor.quotientConvergesOnNullSequences G perturbationConverges

        rightProductConvergent : BishopSequence._isConvergent
          (λ index →
            Bishop._*_
              (f point)
              (Factor.quotient G (perturbation index)))
        rightProductConvergent =
          Bishop._*_ (f point) dg ,
          BishopSequence.xₙyₙ→x₀y₀
            (f point , PowerFactor.constantConverges (f point))
            qgConvergent
      in
      BishopSequence.xₙ+yₙ→x₀+y₀
        leftProductConvergent rightProductConvergent
  }

record Status : Set where
  field
    identityRuleOwned : Bool
    differentiabilityImpliesSequentialContinuityOwned : Bool
    productRuleOwned : Bool

    identityRuleOwnedIsTrue : identityRuleOwned ≡ true
    differentiabilityImpliesSequentialContinuityOwnedIsTrue :
      differentiabilityImpliesSequentialContinuityOwned ≡ true
    productRuleOwnedIsTrue : productRuleOwned ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { identityRuleOwned = true
  ; differentiabilityImpliesSequentialContinuityOwned = true
  ; productRuleOwned = true
  ; identityRuleOwnedIsTrue = refl
  ; differentiabilityImpliesSequentialContinuityOwnedIsTrue = refl
  ; productRuleOwnedIsTrue = refl
  }
