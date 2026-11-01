module DASHI.Physics.Closure.NSTriadKNRotationalPairRawDirectionalRound324Exact where

------------------------------------------------------------------------
-- ROUND324 / ROTATIONAL PAIR = i * R172 RAW DIRECTIONAL SLOT KERNEL
--
-- The physical curl convention is
--
--   curl_p(u) = i (p x u).
--
-- Therefore the symmetrised rotational pair is
--
--   [i(p x a)] x b + [i(q x b)] x a
--     = i [ (p x a) x b - a x (q x b) ].
--
-- The bracket is literally R172.rawDirectionalSlotKernel.  This is the exact
-- carrier bridge needed to route R120/R106's helical multiplier-difference
-- vector into the R172--R177 physical dual-defect geometry without using the
-- still-open R232 helical-basis/angular-symbol weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as Scalar
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeSelectedSwapAntisymmetryRound118Exact as R118
import DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact as R172

rotationalPairIsIRawDirectionalSlotKernel :
  ∀ {r} {F : C3.RealField r}
    (waveP waveQ uP uQ : C3.Complex3 F) →
  Conv.rotationalPair waveP waveQ uP uQ
  ≡
  C3.complex3Scale (C3.complexI F)
    (R172.rawDirectionalSlotKernel waveP waveQ uP uQ)
rotationalPairIsIRawDirectionalSlotKernel {F = F} waveP waveQ uP uQ =
  let
    i = C3.complexI F
    A = Cross.complex3Cross (Cross.complex3Cross waveP uP) uQ
    B = Cross.complex3Cross uP (Cross.complex3Cross waveQ uQ)
    Bswap = Cross.complex3Cross (Cross.complex3Cross waveQ uQ) uP

    expand :
      Conv.rotationalPair waveP waveQ uP uQ
      ≡ C3.complex3Add
          (C3.complex3Scale i A)
          (C3.complex3Scale i Bswap)
    expand =
      cong₂ C3.complex3Add
        (R94.crossScaleLeft i (Cross.complex3Cross waveP uP) uQ)
        (R94.crossScaleLeft i (Cross.complex3Cross waveQ uQ) uP)

    swapSecond :
      C3.complex3Scale i Bswap
      ≡ C3.complex3Negate (C3.complex3Scale i B)
    swapSecond =
      trans
        (cong (C3.complex3Scale i)
          (R118.crossAnticommutative
            uP (Cross.complex3Cross waveQ uQ)))
        (Scalar.complex3ScaleNegate i B)

    asSubtract :
      C3.complex3Add
        (C3.complex3Scale i A)
        (C3.complex3Scale i Bswap)
      ≡ C3.complex3Subtract
          (C3.complex3Scale i A)
          (C3.complex3Scale i B)
    asSubtract = cong (C3.complex3Add (C3.complex3Scale i A)) swapSecond

    factorI :
      C3.complex3Subtract
        (C3.complex3Scale i A)
        (C3.complex3Scale i B)
      ≡ C3.complex3Scale i (C3.complex3Subtract A B)
    factorI = sym (Scalar.complex3ScaleSubtract i A B)
  in
  trans expand (trans asSubtract factorI)

round324RotationalPairIsIRawDirectionalKernel : Bool
round324RotationalPairIsIRawDirectionalKernel = true

round324UsesR232AngularBasisWeld : Bool
round324UsesR232AngularBasisWeld = false

round324PhysicalDualDefectEstimateClosed : Bool
round324PhysicalDualDefectEstimateClosed = false

round324PackageAClosed : Bool
round324PackageAClosed = false

round324ClayPromotion : Bool
round324ClayPromotion = false

round324PackageAClosedIsFalse : round324PackageAClosed ≡ false
round324PackageAClosedIsFalse = refl

round324ClayPromotionIsFalse : round324ClayPromotion ≡ false
round324ClayPromotionIsFalse = refl
