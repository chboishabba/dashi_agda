module DASHI.Moonshine.GoldenRatioBishopQuadraticFactorisationBidiExact where

------------------------------------------------------------------------
-- EXACT BISHOP-REAL FACTORISATION OF THE GOLDEN-RATIO QUADRATIC DEFECT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGoldenRatioCarrierExact as Phi
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio

------------------------------------------------------------------------
-- 1. Conjugate root on the same vendored Bishop carrier.
------------------------------------------------------------------------

bishopPsi : BishopReal.ℝ
bishopPsi =
  BishopReal._*_ Phi.half
    (BishopReal._-_ Phi.one Phi.sqrtFive)

------------------------------------------------------------------------
-- 2. Exact factorisation.
------------------------------------------------------------------------

factorExpanded :
  (r : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._-_ r Phi.bishopPhi)
      (BishopReal._-_ r bishopPsi))
    (BishopReal._-_
      (BishopReal._-_ (BishopReal._*_ r r) r)
      (BishopReal._*_
        (BishopReal._*_ Phi.half Phi.half)
        (BishopReal._-_ (BishopReal._*_ Phi.sqrtFive Phi.sqrtFive) Phi.one)))
factorExpanded r =
  let open BishopP.ℝ-Solver
  in solve 4
    (λ h o s x →
      ((x ⊖ (h ⊗ (o ⊕ s))) ⊗ (x ⊖ (h ⊗ (o ⊖ s))))
      ⊜
      (((x ⊗ x) ⊖ x) ⊖ ((h ⊗ h) ⊗ ((s ⊗ s) ⊖ o))))
    BishopP.≃-refl
    Phi.half Phi.one Phi.sqrtFive r

replaceConjugateSquare :
  (r : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal._-_ (BishopReal._*_ r r) r)
      (BishopReal._*_
        (BishopReal._*_ Phi.half Phi.half)
        (BishopReal._-_ (BishopReal._*_ Phi.sqrtFive Phi.sqrtFive) Phi.one)))
    (BishopReal._-_
      (BishopReal._-_ (BishopReal._*_ r r) r)
      (BishopReal._*_
        (BishopReal._*_ Phi.half Phi.half)
        (BishopReal._-_ Phi.five Phi.one)))
replaceConjugateSquare r =
  BishopP.+-congʳ
    (BishopReal._-_ (BishopReal._*_ r r) r)
    (BishopP.-‿cong
      (BishopP.*-cong BishopP.≃-refl
        (BishopP.+-congʳ
          (BishopReal._*_ Phi.sqrtFive Phi.sqrtFive)
          Phi.sqrtFiveSquaresToFive)))

closedConstantReduction :
  (r : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal._-_ (BishopReal._*_ r r) r)
      (BishopReal._*_
        (BishopReal._*_ Phi.half Phi.half)
        (BishopReal._-_ Phi.five Phi.one)))
    (BishopReal._-_
      (BishopReal._-_ (BishopReal._*_ r r) r)
      Phi.one)
closedConstantReduction r =
  let open BishopP.ℝ-Solver
  in solve 4
    (λ h o f x →
      (((x ⊗ x) ⊖ x) ⊖ ((h ⊗ h) ⊗ (f ⊖ o)))
      ⊜
      (((x ⊗ x) ⊖ x) ⊖ o))
    BishopP.≃-refl
    Phi.half Phi.one Phi.five r

bishopPhiPsiFactorisation :
  (r : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._-_ r Phi.bishopPhi)
      (BishopReal._-_ r bishopPsi))
    (BishopReal._-_
      (BishopReal._-_ (BishopReal._*_ r r) r)
      Phi.one)
bishopPhiPsiFactorisation r =
  BishopP.≃-trans
    (factorExpanded r)
    (BishopP.≃-trans
      (replaceConjugateSquare r)
      (closedConstantReduction r))

------------------------------------------------------------------------
-- 3. Producers for the two remaining non-ring coordinates.
------------------------------------------------------------------------

record ConjugateFactorLowerBoundProducer : Set₁ where
  field
    lowerBound : BishopReal.ℝ
    lowerBoundPositive : BishopReal._<_ BishopReal.0ℝ lowerBound
    ratioMinusPsiBound :
      (n : Nat) →
      BishopReal._≤_
        lowerBound
        (BishopReal.∣_∣
          (BishopReal._-_
            (Ratio.balancedFRACTRANBishopRatioSequence n)
            bishopPsi))

record NormOneReciprocalSquareProducer : Set₁ where
  field
    defectAsReciprocalSquare :
      (n : Nat) →
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._-_
            (BishopReal._*_
              (Ratio.balancedFRACTRANBishopRatioSequence n)
              (Ratio.balancedFRACTRANBishopRatioSequence n))
            (Ratio.balancedFRACTRANBishopRatioSequence n))
          Phi.one)
        (BishopReal._⋆
          (+ 1 /
            (Ratio.positiveLo (Ratio.iteratePositiveMacro n)
             * Ratio.positiveLo (Ratio.iteratePositiveMacro n))))

------------------------------------------------------------------------
-- 4. Frontier.
------------------------------------------------------------------------

data BishopQuadraticFactorisationResidual : Set where
  missingNormOneReciprocalSquareWeld : BishopQuadraticFactorisationResidual
  missingUniformConjugateFactorLowerBound : BishopQuadraticFactorisationResidual
  missingReciprocalSquareBishopConvergence : BishopQuadraticFactorisationResidual
  missingFinalRatioConvergenceToBishopPhi : BishopQuadraticFactorisationResidual

record BishopQuadraticFactorisationFrontier : Set where
  constructor bishop-quadratic-factorisation-frontier
  field
    conjugateRootConstructed : Bool
    exactPhiPsiFactorisation : Bool
    normOneReciprocalSquareWelded : Bool
    uniformConjugateLowerBoundPaid : Bool
    reciprocalSquareConvergencePaid : Bool
    finalRatioConvergencePaid : Bool
    firstResidual : BishopQuadraticFactorisationResidual

canonicalBishopQuadraticFactorisationFrontier :
  BishopQuadraticFactorisationFrontier
canonicalBishopQuadraticFactorisationFrontier =
  bishop-quadratic-factorisation-frontier
    true true false false false false
    missingNormOneReciprocalSquareWeld
