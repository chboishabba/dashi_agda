module DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact where

------------------------------------------------------------------------
-- EMBEDDED NAT RECIPROCAL SQUARE = BASEL TERM
--
-- For k = n+1, identify the constructive reciprocal square of the embedded Nat
-- with the exact Basel sequence term already used by the convergence owner:
--
--   inverseSquare (natReal (n+1))  ~=  baselTerm n.
--
-- This is the literal compatibility bridge needed by the k-major Erdős sum.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 1ℚᵘ; _/_; _*_; _≃_; *≡*)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopInverseSquareProductExact as InverseProduct
import DASHI.Foundations.BishopNatRealPositiveExact as NatPositive
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed
open import DASHI.Physics.YangMills.CompactLieProofLevel

reciprocalNatRational : Nat → ℚᵘ
reciprocalNatRational n = + 1 / suc n

reciprocalNatCancels :
  ∀ n →
  (reciprocalNatRational n ℚ.* NatEmbed.natAsRational (suc n))
  ℚ.≃ 1ℚᵘ
reciprocalNatCancels n = ℚ.*≡* refl

reciprocalNatSquareIsBaselRational :
  ∀ n →
  (reciprocalNatRational n ℚ.* reciprocalNatRational n)
  ℚ.≃ Basel.baselRationalTerm n
reciprocalNatSquareIsBaselRational n = ℚ.*≡* refl

embeddedReciprocalNatCancels :
  ∀ n →
  BishopReal._≃_
    (BishopReal._*_
      (Basel.embed (reciprocalNatRational n))
      (Iterated.natReal (suc n)))
    BishopReal.1ℝ
embeddedReciprocalNatCancels n =
  BishopP.≃-trans
    (BishopP.≃-symm
      (BishopP.⋆-distrib-*
        (reciprocalNatRational n)
        (NatEmbed.natAsRational (suc n))))
    (BishopP.⋆-cong (reciprocalNatCancels n))

natRealInverseIsEmbeddedReciprocal :
  ∀ n →
  BishopReal._≃_
    (InverseProduct.inverse
      (Iterated.natReal (suc n))
      (Reciprocal.xNonzero
        (NatPositive.natRealSuccessorStrictlyPositive n)))
    (Basel.embed (reciprocalNatRational n))
natRealInverseIsEmbeddedReciprocal n =
  InverseProduct.inverseFromCancellation
    (Iterated.natReal (suc n))
    (Basel.embed (reciprocalNatRational n))
    (Reciprocal.xNonzero
      (NatPositive.natRealSuccessorStrictlyPositive n))
    (embeddedReciprocalNatCancels n)

natRealSuccessorInverseSquareIsBaselTerm :
  ∀ n →
  BishopReal._≃_
    (Reciprocal.inverseSquare
      (Iterated.natReal (suc n))
      (Reciprocal.xNonzero
        (NatPositive.natRealSuccessorStrictlyPositive n)))
    (Basel.baselTerm n)
natRealSuccessorInverseSquareIsBaselTerm n =
  BishopP.≃-trans
    (BishopP.*-cong
      (natRealInverseIsEmbeddedReciprocal n)
      (natRealInverseIsEmbeddedReciprocal n))
    (BishopP.≃-trans
      (BishopP.≃-symm
        (BishopP.⋆-distrib-*
          (reciprocalNatRational n)
          (reciprocalNatRational n)))
      (BishopP.⋆-cong
        (reciprocalNatSquareIsBaselRational n)))

bishopNatRealReciprocalSquareBaselLevel : ProofLevel
bishopNatRealReciprocalSquareBaselLevel = machineChecked
