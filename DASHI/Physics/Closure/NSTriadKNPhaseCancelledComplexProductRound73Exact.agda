module DASHI.Physics.Closure.NSTriadKNPhaseCancelledComplexProductRound73Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: DASHI repository contributors.
-- Exact phase-cancellation algebra on the repository C3 complex carrier.
-- DOI: not applicable to repository-original finite algebra.
--
-- ROUND73 / PHASE-CANCELLED PRODUCT BRIDGE
--
-- The literal ordered interaction now factors as a COMPLEX source product
--
--   z * w
--
-- before the final real-part map.  It is incorrect in general to replace this
-- by Re(z)Re(w).  A physically meaningful sufficient condition is instead a
-- shared cancelling phase:
--
--   z = x theta,
--   w = y conjugate(theta),
--   theta conjugate(theta) = 1,
--
-- with real amplitudes x,y.  Then exact commutative complex algebra gives
--
--   z w = realEmbed(x y),
--
-- and therefore realPart(z w) is the same real product.
--
-- This is the precise source shape needed to turn the new Round73 complex
-- transport/high-response factorization into rational Q/W factors when the
-- underlying real field is the rational carrier.  The PDE theorem constructing
-- such phase alignment from LH/HL velocity/polarisation geometry remains open.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as ComplexRing
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as Leray

record PhaseCancelledProduct
    {r : Level} {F : C3.RealField r}
    (left right : C3.Complex F) : Set r where
  field
    leftAmplitude rightAmplitude : C3.Carrier F
    phase : C3.Complex F

    leftMeaning :
      left ≡ C3.complexMultiply
        (C3.realEmbed F leftAmplitude) phase

    rightMeaning :
      right ≡ C3.complexMultiply
        (C3.realEmbed F rightAmplitude)
        (C3.complexConjugate phase)

    phaseCancels :
      C3.complexMultiply phase (C3.complexConjugate phase)
      ≡ C3.complexOne F

open PhaseCancelledProduct public

phaseCancelledProductExact :
  ∀ {r} {F : C3.RealField r}
    {left right : C3.Complex F} →
  (witness : PhaseCancelledProduct left right) →
  C3.complexMultiply left right
  ≡ C3.realEmbed F
      (C3.multiply F
        (leftAmplitude witness)
        (rightAmplitude witness))
phaseCancelledProductExact {F = F} {left} {right} witness =
  let
    x = C3.realEmbed F (leftAmplitude witness)
    y = C3.realEmbed F (rightAmplitude witness)
    theta = phase witness
    thetaBar = C3.complexConjugate theta

    regroup :
      C3.complexMultiply
        (C3.complexMultiply x theta)
        (C3.complexMultiply y thetaBar)
      ≡
      C3.complexMultiply
        (C3.complexMultiply x y)
        (C3.complexMultiply theta thetaBar)
    regroup =
      trans
        (Scaling.complexMultiplyAssociative x theta
          (C3.complexMultiply y thetaBar))
        (trans
          (cong (C3.complexMultiply x)
            (trans
              (sym (Scaling.complexMultiplyAssociative theta y thetaBar))
              (trans
                (cong
                  (λ first → C3.complexMultiply first thetaBar)
                  (Algebra.complexMultiplyCommutative theta y))
                (Scaling.complexMultiplyAssociative y theta thetaBar))))
          (sym
            (Scaling.complexMultiplyAssociative
              x y (C3.complexMultiply theta thetaBar))))
  in
  trans
    (Algebra.cong₂ C3.complexMultiply
      (leftMeaning witness) (rightMeaning witness))
    (trans
      regroup
      (trans
        (Algebra.cong₂ C3.complexMultiply
          (Leray.realEmbedMultiply
            (leftAmplitude witness) (rightAmplitude witness))
          (phaseCancels witness))
        (ComplexRing.complexMultiplyOneRight
          (C3.realEmbed F
            (C3.multiply F
              (leftAmplitude witness)
              (rightAmplitude witness))))))

phaseCancelledRealPartExact :
  ∀ {r} {F : C3.RealField r}
    {left right : C3.Complex F} →
  (witness : PhaseCancelledProduct left right) →
  C3.complexRealPart (C3.complexMultiply left right)
  ≡ C3.realEmbed F
      (C3.multiply F
        (leftAmplitude witness)
        (rightAmplitude witness))
phaseCancelledRealPartExact {F = F} witness =
  trans
    (cong C3.complexRealPart (phaseCancelledProductExact witness))
    refl

round73PhaseCancelledProductCompilesToRealAmplitudeProduct : Bool
round73PhaseCancelledProductCompilesToRealAmplitudeProduct = true

round73PhysicalLHHLPhaseCancellationConstructed : Bool
round73PhysicalLHHLPhaseCancellationConstructed = false

round73PhaseCancelledProductCompilesToRealAmplitudeProductIsTrue :
  round73PhaseCancelledProductCompilesToRealAmplitudeProduct ≡ true
round73PhaseCancelledProductCompilesToRealAmplitudeProductIsTrue = refl

round73PhysicalLHHLPhaseCancellationConstructedIsFalse :
  round73PhysicalLHHLPhaseCancellationConstructed ≡ false
round73PhysicalLHHLPhaseCancellationConstructedIsFalse = refl
