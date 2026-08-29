module DASHI.Physics.Closure.NSTriadKNCriticalNetworkRadiusCancellationRound198Exact where

------------------------------------------------------------------------
-- ROUND198 / CRITICAL RADIUS CANCELLATION AT NETWORK-FORCING LEVEL
--
-- R196: complete forcing = c_k N_k^S + c_p N_p^S + c_q N_q^S.
-- R197: N_j^S = inv(r_j) N_j^curl.
-- R147: c_j inv(r_j) is exactly the opposite pairwise radial difference.
--
-- Composing the three owners gives the complete NETWORK forcing in raw-curl
-- radial-gap form:
--
--   Fcrit
--    = (r_p-r_q) N_k^curl
--      + (r_q-r_k) N_p^curl
--      + (r_k-r_p) N_q^curl.
--
-- Thus the normalized-curl denominator disappears even after the full NS
-- network forcing is inserted.  No hidden high-frequency radius survives.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlRadiusCancellationRound147Exact as R147
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorSymmetricSlotsRound195Exact as R195

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

realEmbedProduct :
  ∀ {r} {F : C3.RealField r} (a b : C3.Carrier F) →
  C3.complexMultiply (C3.realEmbed F a) (C3.realEmbed F b)
  ≡ C3.realEmbed F (C3.multiply F a b)
realEmbedProduct {F = F} a b =
  Field.complexExt
    (S.solve 2
      (λ a b →
        (a S.⊗ b) S.⊕ (S.⊝ ((S.Κ (C3.zero F)) S.⊗ (S.Κ (C3.zero F))))
        S.⊜ a S.⊗ b)
      refl a b)
    (S.solve 2
      (λ a b →
        (a S.⊗ (S.Κ (C3.zero F)))
          S.⊕ ((S.Κ (C3.zero F)) S.⊗ b)
        S.⊜ S.Κ (C3.zero F))
      refl a b)
  where module S = Field.Solver F

scaledCriticalKCancel :
  ∀ {r} {F : C3.RealField r}
    (R : R147.ReciprocalRadiusTriple F) (z : C3.Complex F) →
  C3.complexMultiply
    (C3.realEmbed F
      (R138.criticalRadialCoefficientK
        (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)))
    (C3.complexMultiply (C3.realEmbed F (R147.inverseK R)) z)
  ≡ C3.complexMultiply
      (C3.realEmbed F (sub (R147.radiusP R) (R147.radiusQ R))) z
scaledCriticalKCancel {F = F} R z =
  trans
    (sym (Field.complexMultiplyAssociative
      (C3.realEmbed F
        (R138.criticalRadialCoefficientK
          (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)))
      (C3.realEmbed F (R147.inverseK R)) z))
    (cong (λ scalar → C3.complexMultiply scalar z)
      (trans
        (realEmbedProduct
          (R138.criticalRadialCoefficientK
            (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R))
          (R147.inverseK R))
        (cong (C3.realEmbed F)
          (R147.criticalKTimesInverseIsOppositeRadialGap R))))

scaledCriticalPCancel :
  ∀ {r} {F : C3.RealField r}
    (R : R147.ReciprocalRadiusTriple F) (z : C3.Complex F) →
  C3.complexMultiply
    (C3.realEmbed F
      (R138.criticalRadialCoefficientP
        (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)))
    (C3.complexMultiply (C3.realEmbed F (R147.inverseP R)) z)
  ≡ C3.complexMultiply
      (C3.realEmbed F (sub (R147.radiusQ R) (R147.radiusK R))) z
scaledCriticalPCancel {F = F} R z =
  trans
    (sym (Field.complexMultiplyAssociative
      (C3.realEmbed F
        (R138.criticalRadialCoefficientP
          (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)))
      (C3.realEmbed F (R147.inverseP R)) z))
    (cong (λ scalar → C3.complexMultiply scalar z)
      (trans
        (realEmbedProduct
          (R138.criticalRadialCoefficientP
            (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R))
          (R147.inverseP R))
        (cong (C3.realEmbed F)
          (R147.criticalPTimesInverseIsOppositeRadialGap R))))

scaledCriticalQCancel :
  ∀ {r} {F : C3.RealField r}
    (R : R147.ReciprocalRadiusTriple F) (z : C3.Complex F) →
  C3.complexMultiply
    (C3.realEmbed F
      (R138.criticalRadialCoefficientQ
        (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)))
    (C3.complexMultiply (C3.realEmbed F (R147.inverseQ R)) z)
  ≡ C3.complexMultiply
      (C3.realEmbed F (sub (R147.radiusK R) (R147.radiusP R))) z
scaledCriticalQCancel {F = F} R z =
  trans
    (sym (Field.complexMultiplyAssociative
      (C3.realEmbed F
        (R138.criticalRadialCoefficientQ
          (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)))
      (C3.realEmbed F (R147.inverseQ R)) z))
    (cong (λ scalar → C3.complexMultiply scalar z)
      (trans
        (realEmbedProduct
          (R138.criticalRadialCoefficientQ
            (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R))
          (R147.inverseQ R))
        (cong (C3.realEmbed F)
          (R147.criticalQTimesInverseIsOppositeRadialGap R))))

rawNetworkGapProduction :
  ∀ {r} {F : C3.RealField r} →
  R147.ReciprocalRadiusTriple F →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
rawNetworkGapProduction {F = F} R nK nP nQ =
  C3.complexAdd
    (C3.complexMultiply
      (C3.realEmbed F (sub (R147.radiusP R) (R147.radiusQ R))) nK)
    (C3.complexAdd
      (C3.complexMultiply
        (C3.realEmbed F (sub (R147.radiusQ R) (R147.radiusK R))) nP)
      (C3.complexMultiply
        (C3.realEmbed F (sub (R147.radiusK R) (R147.radiusP R))) nQ))

criticalNetworkSlotsCancelToRawGaps :
  ∀ {r} {F : C3.RealField r}
    (R : R147.ReciprocalRadiusTriple F)
    (nK nP nQ : C3.Complex F) →
  R195.complexCriticalSlotProduction
    (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)
    (C3.complexMultiply (C3.realEmbed F (R147.inverseK R)) nK)
    (C3.complexMultiply (C3.realEmbed F (R147.inverseP R)) nP)
    (C3.complexMultiply (C3.realEmbed F (R147.inverseQ R)) nQ)
  ≡ rawNetworkGapProduction R nK nP nQ
criticalNetworkSlotsCancelToRawGaps R nK nP nQ =
  cong₂ C3.complexAdd
    (scaledCriticalKCancel R nK)
    (cong₂ C3.complexAdd
      (scaledCriticalPCancel R nP)
      (scaledCriticalQCancel R nQ))

round198NetworkRadiusCancellationClosed : Bool
round198NetworkRadiusCancellationClosed = true

round198RawNetworkCoefficientsOnlyRadialDifferences : Bool
round198RawNetworkCoefficientsOnlyRadialDifferences = true

round198HighRadiusFromNormalizedCurlSurvives : Bool
round198HighRadiusFromNormalizedCurlSurvives = false

round198PackageAClosed : Bool
round198PackageAClosed = false

round198ClayPromotion : Bool
round198ClayPromotion = false
