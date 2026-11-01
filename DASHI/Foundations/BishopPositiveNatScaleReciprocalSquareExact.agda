module DASHI.Foundations.BishopPositiveNatScaleReciprocalSquareExact where

------------------------------------------------------------------------
-- POSITIVE NAT-SCALE RECIPROCAL SQUARE
--
-- For x>0 and k>=0,
--
--   inverseSquare (natScale (k+1) x)
--     ~= baselTerm k * inverseSquare x.
--
-- This is the generic analytic normalization needed by the Erdos k-major
-- blocks.  No partition-specific factor-pair witness enters here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopInverseSquareProductExact as ProductInverse
import DASHI.Foundations.BishopNatRealPositiveExact as NatPositive
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatBasel
open import DASHI.Physics.YangMills.CompactLieProofLevel

natScaleSuccessorStrictlyPositive :
  ∀ {x} →
  BishopReal._<_ BishopReal.0ℝ x →
  ∀ k →
  BishopReal._<_ BishopReal.0ℝ (Iterated.natScale (suc k) x)
natScaleSuccessorStrictlyPositive xPositive k =
  BishopP.posx⇒0<x
    (Iterated.natScalePositiveSuccessor
      (BishopP.0<x⇒posx xPositive)
      k)

natScaleSuccessorProductPositive :
  ∀ {x} →
  BishopReal._<_ BishopReal.0ℝ x →
  ∀ k →
  BishopReal._<_ BishopReal.0ℝ
    (BishopReal._*_
      (Iterated.natReal (suc k))
      x)
natScaleSuccessorProductPositive xPositive k =
  ProductInverse.productPositive
    (NatPositive.natRealSuccessorStrictlyPositive k)
    xPositive

natScaleSuccessorInverseSquareAsProduct :
  ∀ {x} →
  (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  ∀ k →
  BishopReal._≃_
    (Reciprocal.inverseSquare
      (Iterated.natScale (suc k) x)
      (Reciprocal.xNonzero
        (natScaleSuccessorStrictlyPositive xPositive k)))
    (Reciprocal.inverseSquare
      (BishopReal._*_
        (Iterated.natReal (suc k)) x)
      (ProductInverse.productNonzero
        (NatPositive.natRealSuccessorStrictlyPositive k)
        xPositive))
natScaleSuccessorInverseSquareAsProduct {x} xPositive k =
  ProductInverse.inverseSquareCongruentPositive
    (natScaleSuccessorStrictlyPositive xPositive k)
    (natScaleSuccessorProductPositive xPositive k)
    (Iterated.natScaleAsEmbeddedNatMul (suc k) x)

natScaleSuccessorReciprocalSquare :
  ∀ {x} →
  (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  ∀ k →
  BishopReal._≃_
    (Reciprocal.inverseSquare
      (Iterated.natScale (suc k) x)
      (Reciprocal.xNonzero
        (natScaleSuccessorStrictlyPositive xPositive k)))
    (BishopReal._*_
      (Basel.baselTerm k)
      (Reciprocal.inverseSquare x (Reciprocal.xNonzero xPositive)))
natScaleSuccessorReciprocalSquare {x} xPositive k =
  BishopP.≃-trans
    (natScaleSuccessorInverseSquareAsProduct xPositive k)
    (BishopP.≃-trans
      (ProductInverse.inverseSquareProduct
        (NatPositive.natRealSuccessorStrictlyPositive k)
        xPositive)
      (BishopP.*-congʳ
        (NatBasel.natRealSuccessorInverseSquareIsBaselTerm k)))

bishopPositiveNatScaleReciprocalSquareLevel : ProofLevel
bishopPositiveNatScaleReciprocalSquareLevel = machineChecked
