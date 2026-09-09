module DASHI.Moonshine.GoldenRatioBishopQuadraticFactorisationBidiExact where

------------------------------------------------------------------------
-- EXACT BISHOP-REAL FACTORISATION OF THE GOLDEN-RATIO QUADRATIC DEFECT
--
-- The balanced-FRACTRAN ratio sequence and bishopPhi already live on the same
-- vendored Bishop real carrier.  This owner factors the remaining analytic
-- error through the conjugate algebraic root
--
--   psi_B = (1 - sqrt(5))/2.
--
-- No convergence theorem is claimed here.  The purpose is to reduce the old
-- opaque "quadratic defect -> Bishop error bound" residual to a single order
-- estimate on the conjugate factor.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGoldenRatioCarrierExact as Phi

------------------------------------------------------------------------
-- 1. Conjugate root on the same carrier.
------------------------------------------------------------------------

bishopPsi : BishopReal.ℝ
bishopPsi =
  BishopReal._*_ Phi.half
    (BishopReal._-_ Phi.one Phi.sqrtFive)

------------------------------------------------------------------------
-- 2. Algebraic factorisation.
--
-- First expand both roots while retaining sqrtFive^2, then use the already
-- machine-checked sqrtFive^2 ~= 5 receipt, and finally normalize the closed
-- rational constants half/one/five on the Bishop carrier.
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
-- 3. Exact BIDI boundary for the remaining convergence proof.
------------------------------------------------------------------------

record ConjugateFactorLowerBoundProducer : Set₁ where
  field
    lowerBound : BishopReal.ℝ
    lowerBoundPositive : BishopReal._<_ BishopReal.0ℝ lowerBound
    ratioMinusPsiBound :
      (n : Agda.Builtin.Nat.Nat) →
      BishopReal._≤_
        lowerBound
        (BishopReal.∣_∣
          (BishopReal._-_
            DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact.balancedFRACTRANBishopRatioSequence n
            bishopPsi))

record NormOneReciprocalSquareProducer : Set₁ where
  field
    defectAsReciprocalSquare :
      (n : Agda.Builtin.Nat.Nat) →
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._-_
            (BishopReal._*_
              DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact.balancedFRACTRANBishopRatioSequence n
              DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact.balancedFRACTRANBishopRatioSequence n)
            DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact.balancedFRACTRANBishopRatioSequence n)
          Phi.one)
        (BishopReal._⋆
          (Data.Integer.Base.+ 1 Data.Rational.Unnormalised./
            (DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact.positiveLo
              (DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact.iteratePositiveMacro n)
             Agda.Builtin.Nat.*
             DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact.positiveLo
              (DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact.iteratePositiveMacro n))))

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
    conjugateRootConstructed : Agda.Builtin.Bool.Bool
    exactPhiPsiFactorisation : Agda.Builtin.Bool.Bool
    normOneReciprocalSquareWelded : Agda.Builtin.Bool.Bool
    uniformConjugateLowerBoundPaid : Agda.Builtin.Bool.Bool
    reciprocalSquareConvergencePaid : Agda.Builtin.Bool.Bool
    finalRatioConvergencePaid : Agda.Builtin.Bool.Bool
    firstResidual : BishopQuadraticFactorisationResidual

canonicalBishopQuadraticFactorisationFrontier :
  BishopQuadraticFactorisationFrontier
canonicalBishopQuadraticFactorisationFrontier =
  bishop-quadratic-factorisation-frontier
    Agda.Builtin.Bool.true Agda.Builtin.Bool.true
    Agda.Builtin.Bool.false Agda.Builtin.Bool.false
    Agda.Builtin.Bool.false Agda.Builtin.Bool.false
    missingNormOneReciprocalSquareWeld
