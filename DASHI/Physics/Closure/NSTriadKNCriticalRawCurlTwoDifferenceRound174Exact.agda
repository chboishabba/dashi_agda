module DASHI.Physics.Closure.NSTriadKNCriticalRawCurlTwoDifferenceRound174Exact where

------------------------------------------------------------------------
-- ROUND174 / COMPLETE RAW-CURL PRODUCTION AS TWO DIFFERENCE OWNERS
--
-- Round169/171 give the complete critical production in the symmetric form
--
--   (r_p-r_q) C_k + (r_q-r_k) C_p + (r_k-r_p) C_q.
--
-- The coefficients sum to zero.  Reopen around the q-slot BEFORE estimates:
--
--   = (r_p-r_q) (C_k-C_q)
--     + (r_q-r_k) (C_p-C_q).
--
-- This is the useful HH allocation.  The first owner already has the small
-- radial gap |r_p-r_q| <= r_k.  The second has a large coefficient but its
-- p/q raw-curl slot difference is exactly the dual-defect object of R172--173,
-- and therefore carries the complementary low-output geometry.  No absolute
-- value, shell count, or auxiliary matching is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNCriticalRawCurlRadialGapRound169Exact as R169

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

twoDifferenceProduction :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
twoDifferenceProduction {F = F} rk rp rq cK cP cQ =
  C3.add F
    (C3.multiply F (sub rp rq) (sub cK cQ))
    (C3.multiply F (sub rq rk) (sub cP cQ))

rawCurlGapProductionIsTwoDifferenceProduction :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq cK cP cQ : C3.Carrier F) →
  R169.rawCurlGapProduction rk rp rq cK cP cQ
  ≡ twoDifferenceProduction rk rp rq cK cP cQ
rawCurlGapProductionIsTwoDifferenceProduction {F = F} rk rp rq cK cP cQ =
  R.solve 6
    (λ rk rp rq ck cp cq →
      (((rp R.⊕ (R.⊝ rq)) R.⊗ ck)
        R.⊕ (((rq R.⊕ (R.⊝ rk)) R.⊗ cp)
          R.⊕ ((rk R.⊕ (R.⊝ rp)) R.⊗ cq)))
      R.⊜
      (((rp R.⊕ (R.⊝ rq)) R.⊗ (ck R.⊕ (R.⊝ cq)))
        R.⊕ ((rq R.⊕ (R.⊝ rk)) R.⊗ (cp R.⊕ (R.⊝ cq)))))
    refl rk rp rq cK cP cQ
  where module R = Field.Solver F

round174CompleteProductionTwoDifferenceReopeningClosed : Bool
round174CompleteProductionTwoDifferenceReopeningClosed = true

round174FirstOwnerCarriesRadialGapCoefficient : Bool
round174FirstOwnerCarriesRadialGapCoefficient = true

round174SecondOwnerIsPQRawCurlDifference : Bool
round174SecondOwnerIsPQRawCurlDifference = true

round174AnyAbsoluteValueIntroduced : Bool
round174AnyAbsoluteValueIntroduced = false

round174SpatiallyCriticalTwoOwnerL2PaymentClosed : Bool
round174SpatiallyCriticalTwoOwnerL2PaymentClosed = false

round174PackageAClosed : Bool
round174PackageAClosed = false

round174CompleteProductionTwoDifferenceReopeningClosedIsTrue :
  round174CompleteProductionTwoDifferenceReopeningClosed ≡ true
round174CompleteProductionTwoDifferenceReopeningClosedIsTrue = refl

round174PackageAClosedIsFalse : round174PackageAClosed ≡ false
round174PackageAClosedIsFalse = refl
