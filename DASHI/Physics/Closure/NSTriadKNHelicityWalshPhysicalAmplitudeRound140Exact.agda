module DASHI.Physics.Closure.NSTriadKNHelicityWalshPhysicalAmplitudeRound140Exact where

------------------------------------------------------------------------
-- ROUND140 / FIRST PHYSICAL WALSH-MOMENT WELD
--
-- Sources:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Constantin--Majda, CMP 115 (1988), DOI 10.1007/BF01218019.
--
-- Round139 reduces the eight helicity channels to three signed first Walsh
-- moments.  This focused file proves the k-slot identification on the literal
-- Complex3 triple product:
--
--   M_k = Re < u_k^+ - u_k^- ,
--              (u_p^+ + u_p^-) x (u_q^+ + u_q^-) >.
--
-- The p/q cyclic companions are intentionally left for the next owner rather
-- than overloading this validation surface.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent
import DASHI.Physics.Closure.NSTriadKNHelicityWalshMomentRound139Exact as R139

complexAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
complexAmplitude = Tangent.complexAmplitude

realAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Carrier F
realAmplitude uK uP uQ = C3.real (complexAmplitude uK uP uQ)

amplitudeAddK :
  ∀ {r} {F : C3.RealField r}
    (a b p q : C3.Complex3 F) →
  complexAmplitude (C3.complex3Add a b) p q
  ≡ C3.complexAdd (complexAmplitude a p q) (complexAmplitude b p q)
amplitudeAddK a b p q =
  Additive.hermitianPairingAddLeft a b (Cross.complex3Cross p q)

amplitudeAddP :
  ∀ {r} {F : C3.RealField r}
    (k a b q : C3.Complex3 F) →
  complexAmplitude k (C3.complex3Add a b) q
  ≡ C3.complexAdd (complexAmplitude k a q) (complexAmplitude k b q)
amplitudeAddP k a b q =
  trans
    (cong (C3.hermitianPairing3 k) (Tangent.crossAddLeft a b q))
    (Additive.hermitianPairingAddRight k
      (Cross.complex3Cross a q) (Cross.complex3Cross b q))

amplitudeAddQ :
  ∀ {r} {F : C3.RealField r}
    (k p a b : C3.Complex3 F) →
  complexAmplitude k p (C3.complex3Add a b)
  ≡ C3.complexAdd (complexAmplitude k p a) (complexAmplitude k p b)
amplitudeAddQ k p a b =
  trans
    (cong (C3.hermitianPairing3 k) (Tangent.crossAddRight p a b))
    (Additive.hermitianPairingAddRight k
      (Cross.complex3Cross p a) (Cross.complex3Cross p b))

amplitudeSubtractK :
  ∀ {r} {F : C3.RealField r}
    (a b p q : C3.Complex3 F) →
  complexAmplitude (C3.complex3Subtract a b) p q
  ≡ C3.complexSubtract (complexAmplitude a p q) (complexAmplitude b p q)
amplitudeSubtractK a b p q =
  trans
    (amplitudeAddK a (C3.complex3Negate b) p q)
    (cong (C3.complexAdd (complexAmplitude a p q))
      (Additive.hermitianPairingNegateLeft b (Cross.complex3Cross p q)))

record HelicityComponents {r} (F : C3.RealField r) : Set r where
  constructor helicity-components
  field
    kPlus kMinus pPlus pMinus qPlus qMinus : C3.Complex3 F

open HelicityComponents public

totalP totalQ diffK :
  ∀ {r} {F : C3.RealField r} → HelicityComponents F → C3.Complex3 F
totalP H = C3.complex3Add (pPlus H) (pMinus H)
totalQ H = C3.complex3Add (qPlus H) (qMinus H)
diffK H = C3.complex3Subtract (kPlus H) (kMinus H)

physicalEightAmplitudes :
  ∀ {r} {F : C3.RealField r} →
  HelicityComponents F → R139.EightHelicityAmplitudes F
physicalEightAmplitudes H =
  R139.eight-helicity-amplitudes
    (realAmplitude (kPlus H)  (pPlus H)  (qPlus H))
    (realAmplitude (kMinus H) (pPlus H)  (qPlus H))
    (realAmplitude (kPlus H)  (pMinus H) (qPlus H))
    (realAmplitude (kPlus H)  (pPlus H)  (qMinus H))
    (realAmplitude (kMinus H) (pMinus H) (qPlus H))
    (realAmplitude (kMinus H) (pPlus H)  (qMinus H))
    (realAmplitude (kPlus H)  (pMinus H) (qMinus H))
    (realAmplitude (kMinus H) (pMinus H) (qMinus H))

expandPQ :
  ∀ {r} {F : C3.RealField r}
    (k pP pM qP qM : C3.Complex3 F) →
  complexAmplitude k
    (C3.complex3Add pP pM)
    (C3.complex3Add qP qM)
  ≡ C3.complexAdd
      (C3.complexAdd
        (complexAmplitude k pP qP)
        (complexAmplitude k pP qM))
      (C3.complexAdd
        (complexAmplitude k pM qP)
        (complexAmplitude k pM qM))
expandPQ k pP pM qP qM =
  trans
    (amplitudeAddP k pP pM (C3.complex3Add qP qM))
    (cong₂ C3.complexAdd
      (amplitudeAddQ k pP qP qM)
      (amplitudeAddQ k pM qP qM))

slotMomentKIsPhysicalDifferenceAmplitude :
  ∀ {r} {F : C3.RealField r} (H : HelicityComponents F) →
  R139.slotMomentK (physicalEightAmplitudes H)
  ≡ realAmplitude (diffK H) (totalP H) (totalQ H)
slotMomentKIsPhysicalDifferenceAmplitude H =
  sym (cong C3.real complexIdentity)
  where
  plusExpand =
    expandPQ (kPlus H) (pPlus H) (pMinus H) (qPlus H) (qMinus H)
  minusExpand =
    expandPQ (kMinus H) (pPlus H) (pMinus H) (qPlus H) (qMinus H)

  complexIdentity :
    complexAmplitude (diffK H) (totalP H) (totalQ H)
    ≡ C3.complexSubtract
        (C3.complexAdd
          (C3.complexAdd
            (complexAmplitude (kPlus H) (pPlus H) (qPlus H))
            (complexAmplitude (kPlus H) (pPlus H) (qMinus H)))
          (C3.complexAdd
            (complexAmplitude (kPlus H) (pMinus H) (qPlus H))
            (complexAmplitude (kPlus H) (pMinus H) (qMinus H))))
        (C3.complexAdd
          (C3.complexAdd
            (complexAmplitude (kMinus H) (pPlus H) (qPlus H))
            (complexAmplitude (kMinus H) (pPlus H) (qMinus H)))
          (C3.complexAdd
            (complexAmplitude (kMinus H) (pMinus H) (qPlus H))
            (complexAmplitude (kMinus H) (pMinus H) (qMinus H))))
  complexIdentity =
    trans
      (amplitudeSubtractK (kPlus H) (kMinus H) (totalP H) (totalQ H))
      (cong₂ C3.complexSubtract plusExpand minusExpand)

round140WalshKMomentPhysicalHelicityDifferenceClosed : Bool
round140WalshKMomentPhysicalHelicityDifferenceClosed = true

round140WalshPMomentPhysicalHelicityDifferenceClosed : Bool
round140WalshPMomentPhysicalHelicityDifferenceClosed = false

round140WalshQMomentPhysicalHelicityDifferenceClosed : Bool
round140WalshQMomentPhysicalHelicityDifferenceClosed = false

round140PackageAClosed : Bool
round140PackageAClosed = false

round140WalshKMomentPhysicalHelicityDifferenceClosedIsTrue :
  round140WalshKMomentPhysicalHelicityDifferenceClosed ≡ true
round140WalshKMomentPhysicalHelicityDifferenceClosedIsTrue = refl

round140PackageAClosedIsFalse : round140PackageAClosed ≡ false
round140PackageAClosedIsFalse = refl
