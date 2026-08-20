module DASHI.Physics.Closure.NSTriadKNWaleffeNetworkForcingRealQuarticHomogeneityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND106 MAKE-OR-BREAK / LITERAL QUARTIC HOMOGENEITY
--
-- The full Galerkin nonlinearity scales quadratically under a REAL amplitude
-- rescaling u -> a u.  Scale the three velocity slots by a and the three
-- nonlinear forcing slots by a^2.  Then exactly
--
--   F_net(a u_k,a u_p,a u_q; a^2 f_k,a^2 f_p,a^2 f_q)
--     = a^4 F_net(u_k,u_p,u_q;f_k,f_p,f_q).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityQuadraticHomogeneityRound94Exact as Quadratic
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross

realScale :
  ∀ {r} (F : C3.RealField r) → C3.Carrier F → C3.Complex F
realScale F a = C3.realEmbed F a

squareScale :
  ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Complex F
squareScale {F = F} a =
  C3.complexMultiply (realScale F a) (realScale F a)

fourthScale :
  ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Complex F
fourthScale {F = F} a =
  C3.complexMultiply (squareScale a) (squareScale a)

scaleVelocity :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Complex3 F → C3.Complex3 F
scaleVelocity {F = F} a = C3.complex3Scale (realScale F a)

scaleQuadraticForcing :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Complex3 F → C3.Complex3 F
scaleQuadraticForcing a = C3.complex3Scale (squareScale a)

realScaleConjugate :
  ∀ {r} (F : C3.RealField r) (a : C3.Carrier F) →
  C3.complexConjugate (realScale F a) ≡ realScale F a
realScaleConjugate F a = C3.realEmbedConjugate F a

squareScaleConjugate :
  ∀ {r} {F : C3.RealField r} (a : C3.Carrier F) →
  C3.complexConjugate (squareScale a) ≡ squareScale a
squareScaleConjugate {F = F} a =
  trans
    (Hermitian.complexConjugateMultiply (realScale F a) (realScale F a))
    (cong₂ C3.complexMultiply
      (realScaleConjugate F a)
      (realScaleConjugate F a))

crossTwoLinearScales :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F) (u v : C3.Complex3 F) →
  Cross.complex3Cross (scaleVelocity a u) (scaleVelocity a v)
  ≡ C3.complex3Scale (squareScale a) (Cross.complex3Cross u v)
crossTwoLinearScales {F = F} a u v =
  let s = realScale F a
  in
  trans
    (Tangent.crossScaleLeft s u (C3.complex3Scale s v))
    (trans
      (cong (C3.complex3Scale s)
        (Tangent.crossScaleRight s u v))
      (Quadratic.nestedScale s s (Cross.complex3Cross u v)))

crossQuadraticLinearScales :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F) (u v : C3.Complex3 F) →
  Cross.complex3Cross
    (scaleQuadraticForcing a u)
    (scaleVelocity a v)
  ≡ C3.complex3Scale
      (C3.complexMultiply (squareScale a) (realScale F a))
      (Cross.complex3Cross u v)
crossQuadraticLinearScales {F = F} a u v =
  let s = realScale F a
      s2 = squareScale a
  in
  trans
    (Tangent.crossScaleLeft s2 u (C3.complex3Scale s v))
    (trans
      (cong (C3.complex3Scale s2)
        (Tangent.crossScaleRight s u v))
      (Quadratic.nestedScale s2 s (Cross.complex3Cross u v)))

crossLinearQuadraticScales :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F) (u v : C3.Complex3 F) →
  Cross.complex3Cross
    (scaleVelocity a u)
    (scaleQuadraticForcing a v)
  ≡ C3.complex3Scale
      (C3.complexMultiply (realScale F a) (squareScale a))
      (Cross.complex3Cross u v)
crossLinearQuadraticScales {F = F} a u v =
  let s = realScale F a
      s2 = squareScale a
  in
  trans
    (Tangent.crossScaleLeft s u (C3.complex3Scale s2 v))
    (trans
      (cong (C3.complex3Scale s)
        (Tangent.crossScaleRight s2 u v))
      (Quadratic.nestedScale s s2 (Cross.complex3Cross u v)))

firstForcingSlotQuartic :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F)
    (fK uP uQ : C3.Complex3 F) →
  C3.hermitianPairing3
    (scaleQuadraticForcing a fK)
    (Cross.complex3Cross (scaleVelocity a uP) (scaleVelocity a uQ))
  ≡ C3.complexMultiply (fourthScale a)
      (C3.hermitianPairing3 fK (Cross.complex3Cross uP uQ))
firstForcingSlotQuartic {F = F} a fK uP uQ =
  let s2 = squareScale a
      X = Cross.complex3Cross uP uQ
      base = C3.hermitianPairing3 fK X
  in
  trans
    (cong (C3.hermitianPairing3 (scaleQuadraticForcing a fK))
      (crossTwoLinearScales a uP uQ))
    (trans
      (Scaling.hermitianPairingScaleLeft s2 fK (C3.complex3Scale s2 X))
      (trans
        (cong
          (λ left → C3.complexMultiply left
            (C3.hermitianPairing3 fK (C3.complex3Scale s2 X)))
          (squareScaleConjugate a))
        (trans
          (cong (C3.complexMultiply s2)
            (Scaling.hermitianPairingScaleRight s2 fK X))
          (R.solve 2
            (λ s2 base →
              s2 R.⊗ (s2 R.⊗ base) R.⊜ (s2 R.⊗ s2) R.⊗ base)
            refl s2 base))))
  where module R = Ring.Solver F

secondForcingSlotQuartic :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F)
    (uK fP uQ : C3.Complex3 F) →
  C3.hermitianPairing3
    (scaleVelocity a uK)
    (Cross.complex3Cross (scaleQuadraticForcing a fP) (scaleVelocity a uQ))
  ≡ C3.complexMultiply (fourthScale a)
      (C3.hermitianPairing3 uK (Cross.complex3Cross fP uQ))
secondForcingSlotQuartic {F = F} a uK fP uQ =
  let s = realScale F a
      s2 = squareScale a
      s3 = C3.complexMultiply s2 s
      X = Cross.complex3Cross fP uQ
      base = C3.hermitianPairing3 uK X
  in
  trans
    (cong (C3.hermitianPairing3 (scaleVelocity a uK))
      (crossQuadraticLinearScales a fP uQ))
    (trans
      (Scaling.hermitianPairingScaleLeft s uK (C3.complex3Scale s3 X))
      (trans
        (cong
          (λ left → C3.complexMultiply left
            (C3.hermitianPairing3 uK (C3.complex3Scale s3 X)))
          (realScaleConjugate F a))
        (trans
          (cong (C3.complexMultiply s)
            (Scaling.hermitianPairingScaleRight s3 uK X))
          (R.solve 3
            (λ s s2 base →
              s R.⊗ ((s2 R.⊗ s) R.⊗ base)
              R.⊜ (s2 R.⊗ s2) R.⊗ base)
            refl s s2 base))))
  where module R = Ring.Solver F

thirdForcingSlotQuartic :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F)
    (uK uP fQ : C3.Complex3 F) →
  C3.hermitianPairing3
    (scaleVelocity a uK)
    (Cross.complex3Cross (scaleVelocity a uP) (scaleQuadraticForcing a fQ))
  ≡ C3.complexMultiply (fourthScale a)
      (C3.hermitianPairing3 uK (Cross.complex3Cross uP fQ))
thirdForcingSlotQuartic {F = F} a uK uP fQ =
  let s = realScale F a
      s2 = squareScale a
      s3 = C3.complexMultiply s s2
      X = Cross.complex3Cross uP fQ
      base = C3.hermitianPairing3 uK X
  in
  trans
    (cong (C3.hermitianPairing3 (scaleVelocity a uK))
      (crossLinearQuadraticScales a uP fQ))
    (trans
      (Scaling.hermitianPairingScaleLeft s uK (C3.complex3Scale s3 X))
      (trans
        (cong
          (λ left → C3.complexMultiply left
            (C3.hermitianPairing3 uK (C3.complex3Scale s3 X)))
          (realScaleConjugate F a))
        (trans
          (cong (C3.complexMultiply s)
            (Scaling.hermitianPairingScaleRight s3 uK X))
          (R.solve 3
            (λ s s2 base →
              s R.⊗ ((s R.⊗ s2) R.⊗ base)
              R.⊜ (s2 R.⊗ s2) R.⊗ base)
            refl s s2 base))))
  where module R = Ring.Solver F

networkForcingRealQuarticHomogeneous :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  Tangent.networkForcing
    (scaleVelocity a uK) (scaleVelocity a uP) (scaleVelocity a uQ)
    (scaleQuadraticForcing a fK)
    (scaleQuadraticForcing a fP)
    (scaleQuadraticForcing a fQ)
  ≡ C3.complexMultiply (fourthScale a)
      (Tangent.networkForcing uK uP uQ fK fP fQ)
networkForcingRealQuarticHomogeneous {F = F} a uK uP uQ fK fP fQ =
  let
    FK = C3.hermitianPairing3 fK (Cross.complex3Cross uP uQ)
    FP = C3.hermitianPairing3 uK (Cross.complex3Cross fP uQ)
    FQ = C3.hermitianPairing3 uK (Cross.complex3Cross uP fQ)
    s4 = fourthScale a
  in
  trans
    (cong₂ C3.complexAdd
      (cong₂ C3.complexAdd
        (firstForcingSlotQuartic a fK uP uQ)
        (secondForcingSlotQuartic a uK fP uQ))
      (thirdForcingSlotQuartic a uK uP fQ))
    (sym
      (Ring.complexDistributeLeft s4 (C3.complexAdd FK FP) FQ))

round106LiteralWaleffeNetworkForcingRealQuarticHomogeneityClosed : Bool
round106LiteralWaleffeNetworkForcingRealQuarticHomogeneityClosed = true

round106FrequencyGapWeightsCannotChangeAmplitudeDegree : Bool
round106FrequencyGapWeightsCannotChangeAmplitudeDegree = true

round106LiteralWaleffeNetworkForcingRealQuarticHomogeneityClosedIsTrue :
  round106LiteralWaleffeNetworkForcingRealQuarticHomogeneityClosed ≡ true
round106LiteralWaleffeNetworkForcingRealQuarticHomogeneityClosedIsTrue = refl

round106FrequencyGapWeightsCannotChangeAmplitudeDegreeIsTrue :
  round106FrequencyGapWeightsCannotChangeAmplitudeDegree ≡ true
round106FrequencyGapWeightsCannotChangeAmplitudeDegreeIsTrue = refl
