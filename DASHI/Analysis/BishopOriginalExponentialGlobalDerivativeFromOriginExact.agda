{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalExponentialGlobalDerivativeFromOriginExact where

------------------------------------------------------------------------
-- K04d LOG: GLOBAL DIFFERENTIATION FROM A SINGLE SOURCE-ORIGIN LEMMA
--
-- The ORIGINAL Bishop exponential already has a source-written,
-- all-real Cauchy-product identity
--
--    exp_B(x+h) ~= exp_B(x) * exp_B(h).
--
-- A factor-derivative witness at zero suffices to prove the full
-- original Bishop derivative, at EVERY x:
--
--    exp'_B(x) ~= exp_B(x).
--
-- The actual proof below constructs the quotient function and its
-- convergence, rather than requesting a generic differentiation-
-- under-an-infinite-sum authority. It uses no second exponential,
-- generic real, postulate, or nonzero division.
--
-- Exactly ONE residual source-specific exponential analytic target:
--   BishopFactorDerivativeAt Exp.bishopExp 0 1.
-- This is naturally obtained from the first-order factorial Taylor
-- remainder at the origin. The module does NOT assume the full LOG
-- identity, or claim that the origin witness is already supplied.
------------------------------------------------------------------------

import Real as R
import RealProperties as RP
import Sequence as Seq
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCauchyProductExact as Product
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpZero

-- Exact source equality: the origin derivative's increment is the
-- full original exp_B(h)-1, with no replacement evaluation function.
originalExpOriginIncrement :
  (h : R.ℝ) →
  R._≃_
    (R._-_ (Exp.bishopExp h) R.1ℝ)
    (R._-_
      (Exp.bishopExp (R._+_ R.0ℝ h))
      (Exp.bishopExp R.0ℝ))
originalExpOriginIncrement h =
  RP.+-cong
    (ExpCong.bishopExpCongruent
      (RP.≃-symm (RP.+-identityˡ h)))
    (RP.-‿cong (RP.≃-symm ExpZero.bishopExpZero))

-- A single origin derivative witness extends to ALL original Bishop
-- arguments by the actual source Cauchy product. No derivative-of-limit
-- interchange at a general point is needed.
originalBishopExpGlobalFactorDerivativeFromOrigin :
  Factor.BishopFactorDerivativeAt
    Exp.bishopExp R.0ℝ R.1ℝ →
  (x : R.ℝ) →
  Factor.BishopFactorDerivativeAt
    Exp.bishopExp x (Exp.bishopExp x)
originalBishopExpGlobalFactorDerivativeFromOrigin origin x = record
  { Factor.quotient = λ h →
      R._*_ (Exp.bishopExp x) (Factor.quotient origin h)
  ; Factor.incrementFactorisation = λ h →
      let
        e = Exp.bishopExp x
        eh = Exp.bishopExp h
        q = Factor.quotient origin h
        open RP.ℝ-Solver
      in
      RP.≃-trans
        (RP.+-cong (Product.bishopExpAdd x h) RP.≃-refl)
        (RP.≃-trans
          (solve 2
            (λ a b →
              (a ⊗ b) ⊖ a
              ⊜ a ⊗ (b ⊖ Κ 1ℚᵘ))
            RP.≃-refl e eh)
          (RP.≃-trans
            (RP.*-cong RP.≃-refl
              (RP.≃-trans
                (originalExpOriginIncrement h)
                (Factor.incrementFactorisation origin h)))
            (solve 3
              (λ a h′ q′ →
                a ⊗ (h′ ⊗ q′)
                ⊜ h′ ⊗ (a ⊗ q′))
              RP.≃-refl e h q)))
  ; Factor.quotientConvergesOnNullSequences =
      λ {perturbation} perturbationConverges →
        Seq.xₙ→x∧x≃y⇒xₙ→y
          (Seq.xₙyₙ→x₀y₀
            (Exp.bishopExp x ,
              Power.constantConverges (Exp.bishopExp x))
            (R.1ℝ ,
              Factor.quotientConvergesOnNullSequences
                origin perturbationConverges))
          (RP.*-identityʳ (Exp.bishopExp x))
  }
