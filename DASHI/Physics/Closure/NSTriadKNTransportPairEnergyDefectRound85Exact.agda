module DASHI.Physics.Closure.NSTriadKNTransportPairEnergyDefectRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND85 / PAIRWISE ENERGY FORM OF THE TRANSPORT ADJOINT DEFECT
--
-- Suppose two reverse transport coefficients obey
--
--   conjugate(T_qk) + T_kq = D_kq.
--
-- For vector amplitudes u_k,u_q, exact Hermitian algebra gives
--
--   Re( <u_k,T_kq u_q> + <u_q,T_qk u_k> )
--     = Re <u_k,D_kq u_q>.
--
-- This is the pairwise finite-Fourier form of
--
--   T* + T = D.
--
-- It deliberately does NOT assume D=0.  The divergence-free Round40 skew
-- theorem is the D=0 specialization; for the Round85 pressure advector,
-- D=-h with h=-Delta p=-2Q.  No matrix enumeration or shell closure is assumed
-- here: after this lemma, global assembly is purely a reverse-pair partition
-- problem rather than additional complex algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling

scaledPairingRight :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
scaledPairingRight scalar left right =
  C3.hermitianPairing3 left (C3.complex3Scale scalar right)

forwardEnergy :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
forwardEnergy = scaledPairingRight

reverseEnergy :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
reverseEnergy reverseCoefficient left right =
  scaledPairingRight reverseCoefficient right left

defectEnergy :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
defectEnergy = scaledPairingRight

reverseEnergyConjugate :
  ∀ {r} {F : C3.RealField r}
    (reverseCoefficient : C3.Complex F)
    (left right : C3.Complex3 F) →
  C3.complexConjugate (reverseEnergy reverseCoefficient left right)
  ≡ C3.complexMultiply
      (C3.complexConjugate reverseCoefficient)
      (C3.hermitianPairing3 left right)
reverseEnergyConjugate reverseCoefficient left right =
  trans
    (cong C3.complexConjugate
      (Scaling.hermitianPairingScaleRight
        reverseCoefficient right left))
    (trans
      (Field.complexConjugateMultiply
        reverseCoefficient (C3.hermitianPairing3 right left))
      (cong
        (C3.complexMultiply (C3.complexConjugate reverseCoefficient))
        (Hermitian.hermitianPairingConjugateSymmetric right left)))

forwardEnergyMeaning :
  ∀ {r} {F : C3.RealField r}
    (coefficient : C3.Complex F)
    (left right : C3.Complex3 F) →
  forwardEnergy coefficient left right
  ≡ C3.complexMultiply coefficient (C3.hermitianPairing3 left right)
forwardEnergyMeaning coefficient left right =
  Scaling.hermitianPairingScaleRight coefficient left right

defectEnergyMeaning :
  ∀ {r} {F : C3.RealField r}
    (defect : C3.Complex F)
    (left right : C3.Complex3 F) →
  defectEnergy defect left right
  ≡ C3.complexMultiply defect (C3.hermitianPairing3 left right)
defectEnergyMeaning defect left right =
  Scaling.hermitianPairingScaleRight defect left right

pairEnergyDefectExact :
  ∀ {r} {F : C3.RealField r}
    (forward reverse defect : C3.Complex F)
    (left right : C3.Complex3 F) →
  C3.complexAdd (C3.complexConjugate reverse) forward ≡ defect →
  C3.real
    (C3.complexAdd
      (forwardEnergy forward left right)
      (reverseEnergy reverse left right))
  ≡ C3.real (defectEnergy defect left right)
pairEnergyDefectExact {F = F}
    forward reverse defect left right adjointDefect =
  let
    pairing = C3.hermitianPairing3 left right
    forwardProduct = C3.complexMultiply forward pairing
    reverseProduct = C3.complexMultiply (C3.complexConjugate reverse) pairing

    reverseReal :
      C3.real (reverseEnergy reverse left right)
      ≡ C3.real reverseProduct
    reverseReal =
      trans
        (sym
          (Hermitian.complexRealPartConjugateInvariant
            (reverseEnergy reverse left right)))
        (cong C3.real (reverseEnergyConjugate reverse left right))

    forwardReal :
      C3.real (forwardEnergy forward left right)
      ≡ C3.real forwardProduct
    forwardReal = cong C3.real (forwardEnergyMeaning forward left right)

    sumRealMeaning :
      C3.real
        (C3.complexAdd
          (forwardEnergy forward left right)
          (reverseEnergy reverse left right))
      ≡ C3.add F
          (C3.real (forwardEnergy forward left right))
          (C3.real (reverseEnergy reverse left right))
    sumRealMeaning = refl

    productSumReal :
      C3.add F (C3.real forwardProduct) (C3.real reverseProduct)
      ≡ C3.real (C3.complexAdd forwardProduct reverseProduct)
    productSumReal = refl

    defectRealMeaning :
      C3.real (defectEnergy defect left right)
      ≡ C3.real (C3.complexMultiply defect pairing)
    defectRealMeaning = cong C3.real (defectEnergyMeaning defect left right)

    coefficientCollapse :
      C3.complexAdd forwardProduct reverseProduct
      ≡ C3.complexMultiply defect pairing
    coefficientCollapse =
      trans
        (sym
          (Field.complexMultiplyDistributesRight
            forward (C3.complexConjugate reverse) pairing))
        (cong
          (λ coefficient → C3.complexMultiply coefficient pairing)
          (trans
            (Field.complexAddCommutative forward (C3.complexConjugate reverse))
            adjointDefect))
  in
  trans
    sumRealMeaning
    (trans
      (cong₂ (C3.add F) forwardReal reverseReal)
      (trans
        productSumReal
        (trans
          (cong C3.real coefficientCollapse)
          (sym defectRealMeaning))))

round85TransportPairEnergyDefectConstructed : Bool
round85TransportPairEnergyDefectConstructed = true

round85TransportPairEnergyDefectConstructedIsTrue :
  round85TransportPairEnergyDefectConstructed ≡ true
round85TransportPairEnergyDefectConstructedIsTrue = refl
