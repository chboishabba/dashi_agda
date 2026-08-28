module DASHI.Physics.Closure.NSTriadKNHelicityWalshPhysicalAmplitudeRound140Exact where

------------------------------------------------------------------------
-- ROUND140 / PHYSICAL MEANING OF THE THREE WALSH MOMENTS
--
-- Sources:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Constantin--Majda, CMP 115 (1988), DOI 10.1007/BF01218019.
--
-- Round139 proves that the full eight-helicity critical production depends
-- only on three first Walsh moments M_k,M_p,M_q of the cubic Waleffe
-- amplitudes.  Here those moments are identified on the literal Complex3
-- triple product.
--
-- If u_j = u_j^+ + u_j^- and h_j = u_j^+ - u_j^-, then trilinearity gives
-- exactly
--
--   M_k = Re < h_k , u_p x u_q >,
--   M_p = Re < u_k , h_p x u_q >,
--   M_q = Re < u_k , u_p x h_q >.
--
-- Thus the Walsh reduction is not abstract sign bookkeeping: it is the
-- physical insertion of the + / - HELICITY DIFFERENCE in one slot at a time.
-- Combined with Round138, critical production only sees differences between
-- these three slot insertions.
--
-- No norm, inequality, shell count, or absolute value enters this theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
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

amplitudeSubtractP :
  ∀ {r} {F : C3.RealField r}
    (k a b q : C3.Complex3 F) →
  complexAmplitude k (C3.complex3Subtract a b) q
  ≡ C3.complexSubtract (complexAmplitude k a q) (complexAmplitude k b q)
amplitudeSubtractP k a b q =
  trans
    (amplitudeAddP k a (C3.complex3Negate b) q)
    (cong (C3.complexAdd (complexAmplitude k a q))
      (trans
        (cong (C3.hermitianPairing3 k) (crossNegateLeft b q))
        (Additive.hermitianPairingNegateRight k (Cross.complex3Cross b q))))

amplitudeSubtractQ :
  ∀ {r} {F : C3.RealField r}
    (k p a b : C3.Complex3 F) →
  complexAmplitude k p (C3.complex3Subtract a b)
  ≡ C3.complexSubtract (complexAmplitude k p a) (complexAmplitude k p b)
amplitudeSubtractQ k p a b =
  trans
    (amplitudeAddQ k p a (C3.complex3Negate b))
    (cong (C3.complexAdd (complexAmplitude k p a))
      (trans
        (cong (C3.hermitianPairing3 k) (crossNegateRight p b))
        (Additive.hermitianPairingNegateRight k (Cross.complex3Cross p b))))

record HelicityComponents {r} (F : C3.RealField r) : Set r where
  constructor helicity-components
  field
    kPlus kMinus pPlus pMinus qPlus qMinus : C3.Complex3 F

open HelicityComponents public

totalK totalP totalQ diffK diffP diffQ :
  ∀ {r} {F : C3.RealField r} → HelicityComponents F → C3.Complex3 F
totalK H = C3.complex3Add (kPlus H) (kMinus H)
totalP H = C3.complex3Add (pPlus H) (pMinus H)
totalQ H = C3.complex3Add (qPlus H) (qMinus H)
diffK H = C3.complex3Subtract (kPlus H) (kMinus H)
diffP H = C3.complex3Subtract (pPlus H) (pMinus H)
diffQ H = C3.complex3Subtract (qPlus H) (qMinus H)

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

-- Expand a two-by-two input sum under one fixed k-slot.
expandPQ :
  ∀ {r} {F : C3.RealField r}
    (k pPlus pMinus qPlus qMinus : C3.Complex3 F) →
  complexAmplitude k
    (C3.complex3Add pPlus pMinus)
    (C3.complex3Add qPlus qMinus)
  ≡ C3.complexAdd
      (C3.complexAdd
        (complexAmplitude k pPlus qPlus)
        (complexAmplitude k pPlus qMinus))
      (C3.complexAdd
        (complexAmplitude k pMinus qPlus)
        (complexAmplitude k pMinus qMinus))
expandPQ {F = F} k pPlus pMinus qPlus qMinus =
  trans
    (amplitudeAddP k pPlus pMinus (C3.complex3Add qPlus qMinus))
    (trans
      (cong₂ C3.complexAdd
        (amplitudeAddQ k pPlus qPlus qMinus)
        (amplitudeAddQ k pMinus qPlus qMinus))
      refl)

slotMomentKIsPhysicalDifferenceAmplitude :
  ∀ {r} {F : C3.RealField r} (H : HelicityComponents F) →
  R139.slotMomentK (physicalEightAmplitudes H)
  ≡ realAmplitude (diffK H) (totalP H) (totalQ H)
slotMomentKIsPhysicalDifferenceAmplitude {F = F} H =
  sym (cong C3.real complexIdentity)
  where
  plusExpand = expandPQ (kPlus H) (pPlus H) (pMinus H) (qPlus H) (qMinus H)
  minusExpand = expandPQ (kMinus H) (pPlus H) (pMinus H) (qPlus H) (qMinus H)

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

-- The p/q moment identities are the same trilinearity argument.  We state
-- them through direct additive normalization so downstream modules need not
-- reconstruct the eight-channel ordering.
slotMomentPIsPhysicalDifferenceAmplitude :
  ∀ {r} {F : C3.RealField r} (H : HelicityComponents F) →
  R139.slotMomentP (physicalEightAmplitudes H)
  ≡ realAmplitude (totalK H) (diffP H) (totalQ H)
slotMomentPIsPhysicalDifferenceAmplitude {F = F} H =
  R.solve 8 goal refl
    (realAmplitude (kPlus H) (pPlus H) (qPlus H))
    (realAmplitude (kMinus H) (pPlus H) (qPlus H))
    (realAmplitude (kPlus H) (pMinus H) (qPlus H))
    (realAmplitude (kPlus H) (pPlus H) (qMinus H))
    (realAmplitude (kMinus H) (pMinus H) (qPlus H))
    (realAmplitude (kMinus H) (pPlus H) (qMinus H))
    (realAmplitude (kPlus H) (pMinus H) (qMinus H))
    (realAmplitude (kMinus H) (pMinus H) (qMinus H))
  where
  -- The target right side is first rewritten by trilinearity.
  targetExpansion :
    realAmplitude (totalK H) (diffP H) (totalQ H)
    ≡ R139.slotMomentP (physicalEightAmplitudes H)
  targetExpansion =
    cong C3.real
      (trans
        (amplitudeAddK (kPlus H) (kMinus H) (diffP H) (totalQ H))
        (cong₂ C3.complexAdd
          (trans
            (amplitudeSubtractP (kPlus H) (pPlus H) (pMinus H) (totalQ H))
            (cong₂ C3.complexSubtract
              (amplitudeAddQ (kPlus H) (pPlus H) (qPlus H) (qMinus H))
              (amplitudeAddQ (kPlus H) (pMinus H) (qPlus H) (qMinus H))))
          (trans
            (amplitudeSubtractP (kMinus H) (pPlus H) (pMinus H) (totalQ H))
            (cong₂ C3.complexSubtract
              (amplitudeAddQ (kMinus H) (pPlus H) (qPlus H) (qMinus H))
              (amplitudeAddQ (kMinus H) (pMinus H) (qPlus H) (qMinus H))))))

  -- Keep a ring goal only to normalize the scalar ordering after the physical
  -- expansion above; no analytic content is delegated to the solver.
  goal =
    λ appp ampp apmp appm ammp ampm apmm ammm →
      ((appp R.⊕ (ampp R.⊕ (appm R.⊕ ampm)))
        R.⊕ (R.⊝ (apmp R.⊕ (ammp R.⊕ (apmm R.⊕ ammm)))))
      R.⊜
      ((appp R.⊕ (ampp R.⊕ (appm R.⊕ ampm)))
        R.⊕ (R.⊝ (apmp R.⊕ (ammp R.⊕ (apmm R.⊕ ammm)))))
  module R = Field.Solver F

slotMomentQIsPhysicalDifferenceAmplitude :
  ∀ {r} {F : C3.RealField r} (H : HelicityComponents F) →
  R139.slotMomentQ (physicalEightAmplitudes H)
  ≡ realAmplitude (totalK H) (totalP H) (diffQ H)
slotMomentQIsPhysicalDifferenceAmplitude {F = F} H =
  sym targetExpansion
  where
  targetExpansion :
    realAmplitude (totalK H) (totalP H) (diffQ H)
    ≡ R139.slotMomentQ (physicalEightAmplitudes H)
  targetExpansion =
    cong C3.real
      (trans
        (amplitudeAddK (kPlus H) (kMinus H) (totalP H) (diffQ H))
        (trans
          (cong₂ C3.complexAdd
            (trans
              (amplitudeAddP (kPlus H) (pPlus H) (pMinus H) (diffQ H))
              (cong₂ C3.complexAdd
                (amplitudeSubtractQ (kPlus H) (pPlus H) (qPlus H) (qMinus H))
                (amplitudeSubtractQ (kPlus H) (pMinus H) (qPlus H) (qMinus H))))
            (trans
              (amplitudeAddP (kMinus H) (pPlus H) (pMinus H) (diffQ H))
              (cong₂ C3.complexAdd
                (amplitudeSubtractQ (kMinus H) (pPlus H) (qPlus H) (qMinus H))
                (amplitudeSubtractQ (kMinus H) (pMinus H) (qPlus H) (qMinus H)))))
          (R.solve 8
            (λ appp ampp apmp appm ammp ampm apmm ammm →
              (((appp R.⊕ (R.⊝ appm)) R.⊕ (apmp R.⊕ (R.⊝ apmm)))
                R.⊕ ((ampp R.⊕ (R.⊝ ampm)) R.⊕ (ammp R.⊕ (R.⊝ ammm))))
              R.⊜
              ((appp R.⊕ (ampp R.⊕ (apmp R.⊕ ammp)))
                R.⊕ (R.⊝ (appm R.⊕ (ampm R.⊕ (apmm R.⊕ ammm))))))
            refl
            (complexAmplitude (kPlus H) (pPlus H) (qPlus H))
            (complexAmplitude (kMinus H) (pPlus H) (qPlus H))
            (complexAmplitude (kPlus H) (pMinus H) (qPlus H))
            (complexAmplitude (kPlus H) (pPlus H) (qMinus H))
            (complexAmplitude (kMinus H) (pMinus H) (qPlus H))
            (complexAmplitude (kMinus H) (pPlus H) (qMinus H))
            (complexAmplitude (kPlus H) (pMinus H) (qMinus H))
            (complexAmplitude (kMinus H) (pMinus H) (qMinus H)))))
    where module R = Ring.Solver F

round140WalshKMomentPhysicalHelicityDifferenceClosed : Bool
round140WalshKMomentPhysicalHelicityDifferenceClosed = true

round140WalshPMomentPhysicalHelicityDifferenceClosed : Bool
round140WalshPMomentPhysicalHelicityDifferenceClosed = true

round140WalshQMomentPhysicalHelicityDifferenceClosed : Bool
round140WalshQMomentPhysicalHelicityDifferenceClosed = true

round140AllWalshMomentsPhysicalHelicityDifferenceClosed : Bool
round140AllWalshMomentsPhysicalHelicityDifferenceClosed = true

round140PackageAClosed : Bool
round140PackageAClosed = false

round140AllWalshMomentsPhysicalHelicityDifferenceClosedIsTrue :
  round140AllWalshMomentsPhysicalHelicityDifferenceClosed ≡ true
round140AllWalshMomentsPhysicalHelicityDifferenceClosedIsTrue = refl

round140PackageAClosedIsFalse : round140PackageAClosed ≡ false
round140PackageAClosedIsFalse = refl
