module DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlRadiusCancellationRound147Exact where

------------------------------------------------------------------------
-- ROUND147 / THE CRITICAL RADIAL WEIGHT CANCELS THE NORMALIZED-CURL RADIUS
--
-- Sources:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Zhen Lei; Fang-Hua Lin; Yi Zhou, ARMA 218 (2015),
--   DOI 10.1007/s00205-015-0884-8.
--
-- Round144 expresses the eight-channel critical production through normalized
-- curl insertions S_j = |j|^-1 curl_j with radial coefficients
--
--   c_k = r_k(r_p-r_q),
--   c_p = r_p(r_q-r_k),
--   c_q = r_q(r_k-r_p).
--
-- The critical radius multiplying each slot is EXACTLY the radius inverted by
-- S_j.  With proof-bearing inverse laws r_j inv_j = 1, the products collapse:
--
--   c_k inv_k = r_p-r_q,
--   c_p inv_p = r_q-r_k,
--   c_q inv_q = r_k-r_p.
--
-- This is important analytically: after the Walsh/slot cancellation the
-- normalized-curl denominator is not an additional high-frequency loss.  The
-- remaining coefficients are only pairwise radial differences.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

record ReciprocalRadiusTriple
    {r} (F : C3.RealField r) : Set r where
  constructor reciprocal-radius-triple
  field
    radiusK radiusP radiusQ : C3.Carrier F
    inverseK inverseP inverseQ : C3.Carrier F
    radiusInverseK : C3.multiply F radiusK inverseK ≡ C3.one F
    radiusInverseP : C3.multiply F radiusP inverseP ≡ C3.one F
    radiusInverseQ : C3.multiply F radiusQ inverseQ ≡ C3.one F

open ReciprocalRadiusTriple public

cancelRadiusInverseAgainstFactor :
  ∀ {r} {F : C3.RealField r}
    (radius inverse factor : C3.Carrier F) →
  C3.multiply F radius inverse ≡ C3.one F →
  C3.multiply F (C3.multiply F radius factor) inverse ≡ factor
cancelRadiusInverseAgainstFactor {F = F} radius inverse factor inverseLaw =
  trans
    (R.solve 3
      (λ r f i → (r R.⊗ f) R.⊗ i R.⊜ (r R.⊗ i) R.⊗ f)
      refl radius factor inverse)
    (trans
      (cong (λ product → C3.multiply F product factor) inverseLaw)
      (C3.multiplyOneLeft F factor))
  where module R = Field.Solver F

criticalKTimesInverseIsOppositeRadialGap :
  ∀ {r} {F : C3.RealField r}
    (R : ReciprocalRadiusTriple F) →
  C3.multiply F
    (R138.criticalRadialCoefficientK
      (radiusK R) (radiusP R) (radiusQ R))
    (inverseK R)
  ≡ sub (radiusP R) (radiusQ R)
criticalKTimesInverseIsOppositeRadialGap R =
  cancelRadiusInverseAgainstFactor
    (radiusK R) (inverseK R)
    (sub (radiusP R) (radiusQ R))
    (radiusInverseK R)

criticalPTimesInverseIsOppositeRadialGap :
  ∀ {r} {F : C3.RealField r}
    (R : ReciprocalRadiusTriple F) →
  C3.multiply F
    (R138.criticalRadialCoefficientP
      (radiusK R) (radiusP R) (radiusQ R))
    (inverseP R)
  ≡ sub (radiusQ R) (radiusK R)
criticalPTimesInverseIsOppositeRadialGap R =
  cancelRadiusInverseAgainstFactor
    (radiusP R) (inverseP R)
    (sub (radiusQ R) (radiusK R))
    (radiusInverseP R)

criticalQTimesInverseIsOppositeRadialGap :
  ∀ {r} {F : C3.RealField r}
    (R : ReciprocalRadiusTriple F) →
  C3.multiply F
    (R138.criticalRadialCoefficientQ
      (radiusK R) (radiusP R) (radiusQ R))
    (inverseQ R)
  ≡ sub (radiusK R) (radiusP R)
criticalQTimesInverseIsOppositeRadialGap R =
  cancelRadiusInverseAgainstFactor
    (radiusQ R) (inverseQ R)
    (sub (radiusK R) (radiusP R))
    (radiusInverseQ R)

round147CriticalRadiusCancelsNormalizedCurlDenominator : Bool
round147CriticalRadiusCancelsNormalizedCurlDenominator = true

round147RemainingSlotCoefficientsArePairwiseRadialDifferences : Bool
round147RemainingSlotCoefficientsArePairwiseRadialDifferences = true

round147PackageAClosed : Bool
round147PackageAClosed = false

round147CriticalRadiusCancelsNormalizedCurlDenominatorIsTrue :
  round147CriticalRadiusCancelsNormalizedCurlDenominator ≡ true
round147CriticalRadiusCancelsNormalizedCurlDenominatorIsTrue = refl

round147PackageAClosedIsFalse : round147PackageAClosed ≡ false
round147PackageAClosedIsFalse = refl
