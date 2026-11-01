module DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorSymmetricSlotsRound195Exact where

------------------------------------------------------------------------
-- ROUND195 / TWO-DIFFERENCE FORCE REOPENS TO THE SYMMETRIC THREE-SLOT FORM
--
-- R190 keeps the useful two-difference representation
--
--   c_k (B_k-B_q) + c_p (B_p-B_q).
--
-- For the ACTUAL critical coefficients
--
--   c_k = r_k(r_p-r_q),
--   c_p = r_p(r_q-r_k),
--   c_q = r_q(r_k-r_p),
--
-- R138 proves c_k+c_p+c_q=0.  Therefore, even for COMPLEX forcing amplitudes,
-- the two-difference owner is exactly the symmetric three-slot owner
--
--   c_k B_k + c_p B_p + c_q B_q.
--
-- This matters for R193: the negative q-slot pieces from the KQ and PQ
-- channels are not independent losses; after recombination they become the
-- single c_q q-slot contribution.  The external forcing can therefore be
-- analysed as one cyclic three-slot critical commutator on each residual
-- forcing cell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorTangentRound190Exact as R190

complexCriticalSlotProduction :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
complexCriticalSlotProduction {F = F} rk rp rq bK bP bQ =
  C3.complexAdd
    (C3.complexMultiply
      (C3.realEmbed F (R138.criticalRadialCoefficientK rk rp rq)) bK)
    (C3.complexAdd
      (C3.complexMultiply
        (C3.realEmbed F (R138.criticalRadialCoefficientP rk rp rq)) bP)
      (C3.complexMultiply
        (C3.realEmbed F (R138.criticalRadialCoefficientQ rk rp rq)) bQ))

criticalTwoDifferenceIsComplexThreeSlot :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq : C3.Carrier F)
    (bK bP bQ : C3.Complex F) →
  R190.weightedTwoChannel
    (R138.criticalRadialCoefficientK rk rp rq)
    (R138.criticalRadialCoefficientP rk rp rq)
    (C3.complexSubtract bK bQ)
    (C3.complexSubtract bP bQ)
  ≡ complexCriticalSlotProduction rk rp rq bK bP bQ
criticalTwoDifferenceIsComplexThreeSlot {F = F}
    rk rp rq
    (C3.complex bKr bKi)
    (C3.complex bPr bPi)
    (C3.complex bQr bQi) =
  Algebra.complexExt
    (S.solve 6
      (λ rk rp rq bk bp bq →
        (((rk S.⊗ (rp S.⊕ (S.⊝ rq))) S.⊗ (bk S.⊕ (S.⊝ bq)))
          S.⊕ ((rp S.⊗ (rq S.⊕ (S.⊝ rk))) S.⊗ (bp S.⊕ (S.⊝ bq))))
        S.⊜
        (((rk S.⊗ (rp S.⊕ (S.⊝ rq))) S.⊗ bk)
          S.⊕ (((rp S.⊗ (rq S.⊕ (S.⊝ rk))) S.⊗ bp)
            S.⊕ ((rq S.⊗ (rk S.⊕ (S.⊝ rp))) S.⊗ bq))))
      refl rk rp rq bKr bPr bQr)
    (S.solve 6
      (λ rk rp rq bk bp bq →
        (((rk S.⊗ (rp S.⊕ (S.⊝ rq))) S.⊗ (bk S.⊕ (S.⊝ bq)))
          S.⊕ ((rp S.⊗ (rq S.⊕ (S.⊝ rk))) S.⊗ (bp S.⊕ (S.⊝ bq))))
        S.⊜
        (((rk S.⊗ (rp S.⊕ (S.⊝ rq))) S.⊗ bk)
          S.⊕ (((rp S.⊗ (rq S.⊕ (S.⊝ rk))) S.⊗ bp)
            S.⊕ ((rq S.⊗ (rk S.⊕ (S.⊝ rp))) S.⊗ bq))))
      refl rk rp rq bKi bPi bQi)
  where module S = Algebra.Solver F

round195ComplexThreeSlotReopeningClosed : Bool
round195ComplexThreeSlotReopeningClosed = true

round195NegativeQPiecesNeedSeparatePayment : Bool
round195NegativeQPiecesNeedSeparatePayment = false

round195CyclicThreeSlotExternalCellAnalysisReady : Bool
round195CyclicThreeSlotExternalCellAnalysisReady = true

round195PackageAClosed : Bool
round195PackageAClosed = false

round195ClayPromotion : Bool
round195ClayPromotion = false
