module DASHI.Physics.Closure.NSTriadKNCriticalRawCurlRadialGapRound169Exact where

------------------------------------------------------------------------
-- ROUND169 / COMPLETE CRITICAL PRODUCTION IN RAW-CURL RADIAL-GAP FORM
--
-- R138 writes the signed critical production as
--
--   c_k B_k + c_p B_p + c_q B_q,
--
-- and R147 proves c_j * inv(r_j) equals the opposite radial difference.
-- Therefore whenever B_j = inv(r_j) C_j, the whole production is exactly
--
--   (r_p-r_q) C_k + (r_q-r_k) C_p + (r_k-r_p) C_q.
--
-- This symmetric form is preferable for the companion search: every remaining
-- coefficient is a first radial difference and every C_j is an UNNORMALIZED
-- curl insertion.  No inverse radius remains in the critical coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlRadiusCancellationRound147Exact as R147

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

rawCurlGapProduction :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
rawCurlGapProduction {F = F} rk rp rq ck cp cq =
  C3.add F
    (C3.multiply F (sub rp rq) ck)
    (C3.add F
      (C3.multiply F (sub rq rk) cp)
      (C3.multiply F (sub rk rp) cq))

normalizedSlotProductionFromRaw :
  ∀ {r} {F : C3.RealField r} →
  R147.ReciprocalRadiusTriple F →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
normalizedSlotProductionFromRaw {F = F} R ck cp cq =
  R138.helicitySlotProduction
    (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)
    (C3.multiply F (R147.inverseK R) ck)
    (C3.multiply F (R147.inverseP R) cp)
    (C3.multiply F (R147.inverseQ R) cq)

normalizedSlotProductionIsRawCurlGapProduction :
  ∀ {r} {F : C3.RealField r}
    (R : R147.ReciprocalRadiusTriple F)
    (ck cp cq : C3.Carrier F) →
  normalizedSlotProductionFromRaw R ck cp cq
  ≡ rawCurlGapProduction
      (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)
      ck cp cq
normalizedSlotProductionIsRawCurlGapProduction {F = F} R ck cp cq =
  trans regroup substitute
  where
  cK = R138.criticalRadialCoefficientK
    (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)
  cP = R138.criticalRadialCoefficientP
    (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)
  cQ = R138.criticalRadialCoefficientQ
    (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)

  regroup :
    R138.helicitySlotProduction
      (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)
      (C3.multiply F (R147.inverseK R) ck)
      (C3.multiply F (R147.inverseP R) cp)
      (C3.multiply F (R147.inverseQ R) cq)
    ≡
    C3.add F
      (C3.multiply F (C3.multiply F cK (R147.inverseK R)) ck)
      (C3.add F
        (C3.multiply F (C3.multiply F cP (R147.inverseP R)) cp)
        (C3.multiply F (C3.multiply F cQ (R147.inverseQ R)) cq))
  regroup =
    S.solve 9
      (λ ck cp cq ik ip iq x y z →
        ((x S.⊗ (ik S.⊗ ck))
          S.⊕ ((y S.⊗ (ip S.⊗ cp)) S.⊕ (z S.⊗ (iq S.⊗ cq))))
        S.⊜
        (((x S.⊗ ik) S.⊗ ck)
          S.⊕ (((y S.⊗ ip) S.⊗ cp) S.⊕ ((z S.⊗ iq) S.⊗ cq))))
      refl ck cp cq
      (R147.inverseK R) (R147.inverseP R) (R147.inverseQ R)
      cK cP cQ
    where module S = Field.Solver F

  substitute :
    C3.add F
      (C3.multiply F (C3.multiply F cK (R147.inverseK R)) ck)
      (C3.add F
        (C3.multiply F (C3.multiply F cP (R147.inverseP R)) cp)
        (C3.multiply F (C3.multiply F cQ (R147.inverseQ R)) cq))
    ≡ rawCurlGapProduction
        (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)
        ck cp cq
  substitute =
    cong₂ (C3.add F)
      (cong (λ coefficient → C3.multiply F coefficient ck)
        (R147.criticalKTimesInverseIsOppositeRadialGap R))
      (cong₂ (C3.add F)
        (cong (λ coefficient → C3.multiply F coefficient cp)
          (R147.criticalPTimesInverseIsOppositeRadialGap R))
        (cong (λ coefficient → C3.multiply F coefficient cq)
          (R147.criticalQTimesInverseIsOppositeRadialGap R)))

round169CriticalProductionRawCurlGapFormClosed : Bool
round169CriticalProductionRawCurlGapFormClosed = true

round169NormalizedCurlRadiusSurvivesInCoefficient : Bool
round169NormalizedCurlRadiusSurvivesInCoefficient = false

round169RawCurlQuadraticCompanionBudgetClosed : Bool
round169RawCurlQuadraticCompanionBudgetClosed = false

round169PackageAClosed : Bool
round169PackageAClosed = false

round169CriticalProductionRawCurlGapFormClosedIsTrue :
  round169CriticalProductionRawCurlGapFormClosed ≡ true
round169CriticalProductionRawCurlGapFormClosedIsTrue = refl

round169PackageAClosedIsFalse : round169PackageAClosed ≡ false
round169PackageAClosedIsFalse = refl
