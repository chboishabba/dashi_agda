module DASHI.Physics.Closure.NSTriadKNHelicityWalshMomentRound139Exact where

------------------------------------------------------------------------
-- ROUND139 / WALSH COLLAPSE OF THE EIGHT HELICITY CHANNELS
--
-- Sources:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Constantin--Majda, CMP 115 (1988), DOI 10.1007/BF01218019.
--
-- Round135 gives the exact critical-production coefficient of each of the
-- eight helicity sign channels.  Instead of treating the six nonzero channels
-- separately, take the three first Walsh moments of their geometric amplitudes:
--
--   M_k = sum_{s_k,s_p,s_q} s_k A_{s_k s_p s_q},
--   M_p = sum_{s_k,s_p,s_q} s_p A_{s_k s_p s_q},
--   M_q = sum_{s_k,s_p,s_q} s_q A_{s_k s_p s_q}.
--
-- Then the COMPLETE eight-channel signed critical production is exactly
--
--   c_k M_k + c_p M_p + c_q M_q,
--
-- where the radial coefficients c_k,c_p,c_q are those of Round138 and sum to
-- zero.  Thus the helical sign decomposition is not six unrelated bad terms:
-- only three signed first moments survive, and Round138 immediately reduces
-- those to two slot differences.
--
-- This is finite commutative-ring algebra only.  The next physical weld is to
-- identify M_k,M_p,M_q with scalar triple products containing the difference
-- between the + and - helical components in the corresponding slot.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPhysicalHelicitySignExhaustionRound135Exact as R135
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

record EightHelicityAmplitudes {r} (F : C3.RealField r) : Set r where
  constructor eight-helicity-amplitudes
  field
    aPPP aMPP aPMP aPPM aMMP aMPM aPMM aMMM : C3.Carrier F

open EightHelicityAmplitudes public

sum4 :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
sum4 {F = F} a b c d = C3.add F a (C3.add F b (C3.add F c d))

slotMomentK :
  ∀ {r} {F : C3.RealField r} → EightHelicityAmplitudes F → C3.Carrier F
slotMomentK {F = F} A =
  sub
    (sum4 (aPPP A) (aPMP A) (aPPM A) (aPMM A))
    (sum4 (aMPP A) (aMMP A) (aMPM A) (aMMM A))

slotMomentP :
  ∀ {r} {F : C3.RealField r} → EightHelicityAmplitudes F → C3.Carrier F
slotMomentP {F = F} A =
  sub
    (sum4 (aPPP A) (aMPP A) (aPPM A) (aMPM A))
    (sum4 (aPMP A) (aMMP A) (aPMM A) (aMMM A))

slotMomentQ :
  ∀ {r} {F : C3.RealField r} → EightHelicityAmplitudes F → C3.Carrier F
slotMomentQ {F = F} A =
  sub
    (sum4 (aPPP A) (aMPP A) (aPMP A) (aMMP A))
    (sum4 (aPPM A) (aMPM A) (aPMM A) (aMMM A))

eightChannelCriticalProduction :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  EightHelicityAmplitudes F → C3.Carrier F
eightChannelCriticalProduction {F = F} rk rp rq A =
  C3.add F
    (R135.minorityNormalForm R135.plus R135.plus R135.plus
      rk rp rq (aPPP A))
    (C3.add F
      (R135.minorityNormalForm R135.minus R135.plus R135.plus
        rk rp rq (aMPP A))
      (C3.add F
        (R135.minorityNormalForm R135.plus R135.minus R135.plus
          rk rp rq (aPMP A))
        (C3.add F
          (R135.minorityNormalForm R135.plus R135.plus R135.minus
            rk rp rq (aPPM A))
          (C3.add F
            (R135.minorityNormalForm R135.minus R135.minus R135.plus
              rk rp rq (aMMP A))
            (C3.add F
              (R135.minorityNormalForm R135.minus R135.plus R135.minus
                rk rp rq (aMPM A))
              (C3.add F
                (R135.minorityNormalForm R135.plus R135.minus R135.minus
                  rk rp rq (aPMM A))
                (R135.minorityNormalForm R135.minus R135.minus R135.minus
                  rk rp rq (aMMM A))))))))

walshSlotCriticalProduction :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  EightHelicityAmplitudes F → C3.Carrier F
walshSlotCriticalProduction {F = F} rk rp rq A =
  R138.helicitySlotProduction rk rp rq
    (slotMomentK A) (slotMomentP A) (slotMomentQ A)

eightChannelsCollapseToFirstWalshMoments :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq : C3.Carrier F)
    (A : EightHelicityAmplitudes F) →
  eightChannelCriticalProduction rk rp rq A
  ≡ walshSlotCriticalProduction rk rp rq A
eightChannelsCollapseToFirstWalshMoments {F = F} rk rp rq A =
  R.solve 11
    (λ rk rp rq appp ampp apmp appm ammp ampm apmm ammm →
      -- Left: the two homochiral channels are zero and the six mixed
      -- coefficients are the Round135 normal forms.
      ((R.Κ (C3.zero F))
       R.⊕ (((((R.Κ (C3.one F) R.⊕ R.Κ (C3.one F)) R.⊗ rk)
              R.⊗ (rq R.⊕ (R.⊝ rp))) R.⊗ ampp)
       R.⊕ (((((R.Κ (C3.one F) R.⊕ R.Κ (C3.one F)) R.⊗ rp)
              R.⊗ (rk R.⊕ (R.⊝ rq))) R.⊗ apmp)
       R.⊕ (((((R.Κ (C3.one F) R.⊕ R.Κ (C3.one F)) R.⊗ rq)
              R.⊗ (rp R.⊕ (R.⊝ rk))) R.⊗ appm)
       R.⊕ ((R.⊝ ((((R.Κ (C3.one F) R.⊕ R.Κ (C3.one F)) R.⊗ rq)
              R.⊗ (rp R.⊕ (R.⊝ rk))) R.⊗ ammp))
       R.⊕ ((R.⊝ ((((R.Κ (C3.one F) R.⊕ R.Κ (C3.one F)) R.⊗ rp)
              R.⊗ (rk R.⊕ (R.⊝ rq))) R.⊗ ampm))
       R.⊕ ((R.⊝ ((((R.Κ (C3.one F) R.⊕ R.Κ (C3.one F)) R.⊗ rk)
              R.⊗ (rq R.⊕ (R.⊝ rp))) R.⊗ apmm))
       R.⊕ R.Κ (C3.zero F))))))))
      R.⊜
      -- Right: c_k M_k + c_p M_p + c_q M_q.
      (((rk R.⊗ (rp R.⊕ (R.⊝ rq))) R.⊗
        (((appp R.⊕ (apmp R.⊕ (appm R.⊕ apmm)))
          R.⊕ (R.⊝ (ampp R.⊕ (ammp R.⊕ (ampm R.⊕ ammm))))))
       R.⊕
       ((((rp R.⊗ (rq R.⊕ (R.⊝ rk))) R.⊗
        (((appp R.⊕ (ampp R.⊕ (appm R.⊕ ampm)))
          R.⊕ (R.⊝ (apmp R.⊕ (ammp R.⊕ (apmm R.⊕ ammm))))))
       R.⊕
       ((rq R.⊗ (rk R.⊕ (R.⊝ rp))) R.⊗
        (((appp R.⊕ (ampp R.⊕ (apmp R.⊕ ammp)))
          R.⊕ (R.⊝ (appm R.⊕ (ampm R.⊕ (apmm R.⊕ ammm)))))))))))
    refl rk rp rq
      (aPPP A) (aMPP A) (aPMP A) (aPPM A)
      (aMMP A) (aMPM A) (aPMM A) (aMMM A)
  where module R = Field.Solver F

round139EightHelicityChannelsCollapseToThreeWalshMoments : Bool
round139EightHelicityChannelsCollapseToThreeWalshMoments = true

round139HomochiralChannelsDisappearInsideWalshIdentity : Bool
round139HomochiralChannelsDisappearInsideWalshIdentity = true

round139WalshMomentsPhysicalHelicityDifferenceWeldClosed : Bool
round139WalshMomentsPhysicalHelicityDifferenceWeldClosed = false

round139PackageAClosed : Bool
round139PackageAClosed = false

round139EightHelicityChannelsCollapseToThreeWalshMomentsIsTrue :
  round139EightHelicityChannelsCollapseToThreeWalshMoments ≡ true
round139EightHelicityChannelsCollapseToThreeWalshMomentsIsTrue = refl

round139PackageAClosedIsFalse : round139PackageAClosed ≡ false
round139PackageAClosedIsFalse = refl
