module DASHI.Physics.Closure.NSTriadKNHelicityWalshPhysicalCyclicSlotsRound141Exact where

------------------------------------------------------------------------
-- ROUND141 / COMPLETE THE PHYSICAL WALSH-MOMENT WELD
--
-- Sources:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Constantin--Majda, CMP 115 (1988), DOI 10.1007/BF01218019.
--
-- Round140 proves the k-slot identity.  This file proves the p/q companions,
-- retaining the SAME geometric amplitude Re<u_k,u_p x u_q>; no illicit cyclic
-- permutation of a complex Hermitian triple product is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent
import DASHI.Physics.Closure.NSTriadKNHelicityWalshMomentRound139Exact as R139
import DASHI.Physics.Closure.NSTriadKNHelicityWalshPhysicalAmplitudeRound140Exact as R140

crossNegateLeft :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  Cross.complex3Cross (C3.complex3Negate u) v
  ≡ C3.complex3Negate (Cross.complex3Cross u v)
crossNegateLeft {F = F} u v =
  trans
    (cong (λ value → Cross.complex3Cross value v)
      (sym (Additive.complex3ScaleMinusOne u)))
    (trans
      (Tangent.crossScaleLeft (Additive.minusOne F) u v)
      (Additive.complex3ScaleMinusOne (Cross.complex3Cross u v)))

crossNegateRight :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  Cross.complex3Cross u (C3.complex3Negate v)
  ≡ C3.complex3Negate (Cross.complex3Cross u v)
crossNegateRight {F = F} u v =
  trans
    (cong (Cross.complex3Cross u)
      (sym (Additive.complex3ScaleMinusOne v)))
    (trans
      (Tangent.crossScaleRight (Additive.minusOne F) u v)
      (Additive.complex3ScaleMinusOne (Cross.complex3Cross u v)))

amplitudeSubtractP :
  ∀ {r} {F : C3.RealField r}
    (k a b q : C3.Complex3 F) →
  R140.complexAmplitude k (C3.complex3Subtract a b) q
  ≡ C3.complexSubtract
      (R140.complexAmplitude k a q)
      (R140.complexAmplitude k b q)
amplitudeSubtractP k a b q =
  trans
    (R140.amplitudeAddP k a (C3.complex3Negate b) q)
    (cong (C3.complexAdd (R140.complexAmplitude k a q))
      (trans
        (cong (C3.hermitianPairing3 k) (crossNegateLeft b q))
        (Additive.hermitianPairingNegateRight k (Cross.complex3Cross b q))))

amplitudeSubtractQ :
  ∀ {r} {F : C3.RealField r}
    (k p a b : C3.Complex3 F) →
  R140.complexAmplitude k p (C3.complex3Subtract a b)
  ≡ C3.complexSubtract
      (R140.complexAmplitude k p a)
      (R140.complexAmplitude k p b)
amplitudeSubtractQ k p a b =
  trans
    (R140.amplitudeAddQ k p a (C3.complex3Negate b))
    (cong (C3.complexAdd (R140.complexAmplitude k p a))
      (trans
        (cong (C3.hermitianPairing3 k) (crossNegateRight p b))
        (Additive.hermitianPairingNegateRight k (Cross.complex3Cross p b))))

totalK diffP diffQ :
  ∀ {r} {F : C3.RealField r} → R140.HelicityComponents F → C3.Complex3 F
totalK H = C3.complex3Add (R140.kPlus H) (R140.kMinus H)
diffP H = C3.complex3Subtract (R140.pPlus H) (R140.pMinus H)
diffQ H = C3.complex3Subtract (R140.qPlus H) (R140.qMinus H)

slotMomentPIsPhysicalDifferenceAmplitude :
  ∀ {r} {F : C3.RealField r} (H : R140.HelicityComponents F) →
  R139.slotMomentP (R140.physicalEightAmplitudes H)
  ≡ R140.realAmplitude (totalK H) (diffP H) (R140.totalQ H)
slotMomentPIsPhysicalDifferenceAmplitude {F = F} H =
  sym (cong C3.real complexExpansion)
  where
  aPPP = R140.complexAmplitude (R140.kPlus H)  (R140.pPlus H)  (R140.qPlus H)
  aMPP = R140.complexAmplitude (R140.kMinus H) (R140.pPlus H)  (R140.qPlus H)
  aPMP = R140.complexAmplitude (R140.kPlus H)  (R140.pMinus H) (R140.qPlus H)
  aPPM = R140.complexAmplitude (R140.kPlus H)  (R140.pPlus H)  (R140.qMinus H)
  aMMP = R140.complexAmplitude (R140.kMinus H) (R140.pMinus H) (R140.qPlus H)
  aMPM = R140.complexAmplitude (R140.kMinus H) (R140.pPlus H)  (R140.qMinus H)
  aPMM = R140.complexAmplitude (R140.kPlus H)  (R140.pMinus H) (R140.qMinus H)
  aMMM = R140.complexAmplitude (R140.kMinus H) (R140.pMinus H) (R140.qMinus H)

  expanded :
    R140.complexAmplitude (totalK H) (diffP H) (R140.totalQ H)
    ≡ C3.complexAdd
        (C3.complexSubtract (C3.complexAdd aPPP aPPM) (C3.complexAdd aPMP aPMM))
        (C3.complexSubtract (C3.complexAdd aMPP aMPM) (C3.complexAdd aMMP aMMM))
  expanded =
    trans
      (R140.amplitudeAddK
        (R140.kPlus H) (R140.kMinus H) (diffP H) (R140.totalQ H))
      (cong₂ C3.complexAdd
        (trans
          (amplitudeSubtractP
            (R140.kPlus H) (R140.pPlus H) (R140.pMinus H) (R140.totalQ H))
          (cong₂ C3.complexSubtract
            (R140.amplitudeAddQ (R140.kPlus H) (R140.pPlus H)
              (R140.qPlus H) (R140.qMinus H))
            (R140.amplitudeAddQ (R140.kPlus H) (R140.pMinus H)
              (R140.qPlus H) (R140.qMinus H))))
        (trans
          (amplitudeSubtractP
            (R140.kMinus H) (R140.pPlus H) (R140.pMinus H) (R140.totalQ H))
          (cong₂ C3.complexSubtract
            (R140.amplitudeAddQ (R140.kMinus H) (R140.pPlus H)
              (R140.qPlus H) (R140.qMinus H))
            (R140.amplitudeAddQ (R140.kMinus H) (R140.pMinus H)
              (R140.qPlus H) (R140.qMinus H)))))

  complexExpansion :
    R140.complexAmplitude (totalK H) (diffP H) (R140.totalQ H)
    ≡ C3.complexSubtract
        (C3.complexAdd aPPP (C3.complexAdd aMPP (C3.complexAdd aPPM aMPM)))
        (C3.complexAdd aPMP (C3.complexAdd aMMP (C3.complexAdd aPMM aMMM)))
  complexExpansion =
    trans expanded
      (R.solve 8
        (λ appp ampp apmp appm ammp ampm apmm ammm →
          (((appp R.⊕ appm) R.⊕ (R.⊝ (apmp R.⊕ apmm)))
            R.⊕ ((ampp R.⊕ ampm) R.⊕ (R.⊝ (ammp R.⊕ ammm))))
          R.⊜
          ((appp R.⊕ (ampp R.⊕ (appm R.⊕ ampm)))
            R.⊕ (R.⊝ (apmp R.⊕ (ammp R.⊕ (apmm R.⊕ ammm))))))
        refl aPPP aMPP aPMP aPPM aMMP aMPM aPMM aMMM)
    where module R = Ring.Solver F

slotMomentQIsPhysicalDifferenceAmplitude :
  ∀ {r} {F : C3.RealField r} (H : R140.HelicityComponents F) →
  R139.slotMomentQ (R140.physicalEightAmplitudes H)
  ≡ R140.realAmplitude (totalK H) (R140.totalP H) (diffQ H)
slotMomentQIsPhysicalDifferenceAmplitude {F = F} H =
  sym (cong C3.real complexExpansion)
  where
  aPPP = R140.complexAmplitude (R140.kPlus H)  (R140.pPlus H)  (R140.qPlus H)
  aMPP = R140.complexAmplitude (R140.kMinus H) (R140.pPlus H)  (R140.qPlus H)
  aPMP = R140.complexAmplitude (R140.kPlus H)  (R140.pMinus H) (R140.qPlus H)
  aPPM = R140.complexAmplitude (R140.kPlus H)  (R140.pPlus H)  (R140.qMinus H)
  aMMP = R140.complexAmplitude (R140.kMinus H) (R140.pMinus H) (R140.qPlus H)
  aMPM = R140.complexAmplitude (R140.kMinus H) (R140.pPlus H)  (R140.qMinus H)
  aPMM = R140.complexAmplitude (R140.kPlus H)  (R140.pMinus H) (R140.qMinus H)
  aMMM = R140.complexAmplitude (R140.kMinus H) (R140.pMinus H) (R140.qMinus H)

  expanded :
    R140.complexAmplitude (totalK H) (R140.totalP H) (diffQ H)
    ≡ C3.complexAdd
        (C3.complexAdd
          (C3.complexSubtract aPPP aPPM)
          (C3.complexSubtract aPMP aPMM))
        (C3.complexAdd
          (C3.complexSubtract aMPP aMPM)
          (C3.complexSubtract aMMP aMMM))
  expanded =
    trans
      (R140.amplitudeAddK
        (R140.kPlus H) (R140.kMinus H) (R140.totalP H) (diffQ H))
      (cong₂ C3.complexAdd
        (trans
          (R140.amplitudeAddP
            (R140.kPlus H) (R140.pPlus H) (R140.pMinus H) (diffQ H))
          (cong₂ C3.complexAdd
            (amplitudeSubtractQ (R140.kPlus H) (R140.pPlus H)
              (R140.qPlus H) (R140.qMinus H))
            (amplitudeSubtractQ (R140.kPlus H) (R140.pMinus H)
              (R140.qPlus H) (R140.qMinus H))))
        (trans
          (R140.amplitudeAddP
            (R140.kMinus H) (R140.pPlus H) (R140.pMinus H) (diffQ H))
          (cong₂ C3.complexAdd
            (amplitudeSubtractQ (R140.kMinus H) (R140.pPlus H)
              (R140.qPlus H) (R140.qMinus H))
            (amplitudeSubtractQ (R140.kMinus H) (R140.pMinus H)
              (R140.qPlus H) (R140.qMinus H)))))

  complexExpansion :
    R140.complexAmplitude (totalK H) (R140.totalP H) (diffQ H)
    ≡ C3.complexSubtract
        (C3.complexAdd aPPP (C3.complexAdd aMPP (C3.complexAdd aPMP aMMP)))
        (C3.complexAdd aPPM (C3.complexAdd aMPM (C3.complexAdd aPMM aMMM)))
  complexExpansion =
    trans expanded
      (R.solve 8
        (λ appp ampp apmp appm ammp ampm apmm ammm →
          (((appp R.⊕ (R.⊝ appm)) R.⊕ (apmp R.⊕ (R.⊝ apmm)))
            R.⊕ ((ampp R.⊕ (R.⊝ ampm)) R.⊕ (ammp R.⊕ (R.⊝ ammm))))
          R.⊜
          ((appp R.⊕ (ampp R.⊕ (apmp R.⊕ ammp)))
            R.⊕ (R.⊝ (appm R.⊕ (ampm R.⊕ (apmm R.⊕ ammm))))))
        refl aPPP aMPP aPMP aPPM aMMP aMPM aPMM aMMM)
    where module R = Ring.Solver F

round141WalshPMomentPhysicalHelicityDifferenceClosed : Bool
round141WalshPMomentPhysicalHelicityDifferenceClosed = true

round141WalshQMomentPhysicalHelicityDifferenceClosed : Bool
round141WalshQMomentPhysicalHelicityDifferenceClosed = true

round141AllThreePhysicalWalshMomentWeldsClosed : Bool
round141AllThreePhysicalWalshMomentWeldsClosed = true

round141PackageAClosed : Bool
round141PackageAClosed = false

round141AllThreePhysicalWalshMomentWeldsClosedIsTrue :
  round141AllThreePhysicalWalshMomentWeldsClosed ≡ true
round141AllThreePhysicalWalshMomentWeldsClosedIsTrue = refl

round141PackageAClosedIsFalse : round141PackageAClosed ≡ false
round141PackageAClosedIsFalse = refl
