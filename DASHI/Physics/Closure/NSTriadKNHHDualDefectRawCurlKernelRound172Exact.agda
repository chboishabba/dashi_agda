module DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact where

------------------------------------------------------------------------
-- ROUND172 / RAW-CURL p/q SLOT DIFFERENCE = ANGULAR DEFECT + RADIAL DEFECT
--
-- The complete critical production is now in raw-curl radial-gap form (R171).
-- For the dangerous p/q difference, write p=r_p P and q=r_q Q.  Pure
-- bilinearity gives
--
--   (p x a) x b - a x (q x b)
--     = r_p [ (P x a) x b - a x (Q x b) ]
--       + (r_p-r_q) [ a x (Q x b) ].
--
-- The bracket in the first term is exactly R145.slotKernel, hence factors
-- through the anti-parallel defect P+Q.  The second term already carries the
-- radial defect.  Thus the RAW curl difference has the desired two-channel
-- geometry BEFORE any norm estimate: every term contains either the angular
-- defect or the radial defect.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

  realScale : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Complex3 F → C3.Complex3 F
  realScale {F = F} scalar value =
    C3.complex3Scale (C3.realEmbed F scalar) value

rawDirectionalSlotKernel :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
rawDirectionalSlotKernel p q a b =
  C3.complex3Subtract
    (Cross.complex3Cross (Cross.complex3Cross p a) b)
    (Cross.complex3Cross a (Cross.complex3Cross q b))

rawDirectionalSlotKernelDualDefect :
  ∀ {r} {F : C3.RealField r}
    (rp rq : C3.Carrier F)
    (P Q a b : C3.Complex3 F) →
  rawDirectionalSlotKernel (realScale rp P) (realScale rq Q) a b
  ≡
  C3.complex3Add
    (realScale rp (R145.slotKernel P Q a b))
    (realScale (sub rp rq)
      (Cross.complex3Cross a (Cross.complex3Cross Q b)))
rawDirectionalSlotKernelDualDefect {F = F} rp rq P Q a b =
  trans expand regroup
  where
  A = Cross.complex3Cross (Cross.complex3Cross P a) b
  B = Cross.complex3Cross a (Cross.complex3Cross Q b)

  expand :
    rawDirectionalSlotKernel (realScale rp P) (realScale rq Q) a b
    ≡ C3.complex3Subtract (realScale rp A) (realScale rq B)
  expand =
    cong₂ C3.complex3Subtract
      (trans
        (cong (λ v → Cross.complex3Cross v b)
          (R94.crossScaleLeft (C3.realEmbed F rp) P a))
        (R94.crossScaleLeft (C3.realEmbed F rp)
          (Cross.complex3Cross P a) b))
      (trans
        (cong (Cross.complex3Cross a)
          (R94.crossScaleLeft (C3.realEmbed F rq) Q b))
        (R94.crossScaleRight (C3.realEmbed F rq) a
          (Cross.complex3Cross Q b)))

  regroup :
    C3.complex3Subtract (realScale rp A) (realScale rq B)
    ≡
    C3.complex3Add
      (realScale rp (C3.complex3Subtract A B))
      (realScale (sub rp rq) B)
  regroup =
    vectorRing rp rq A B

  vectorRing :
    (x y : C3.Carrier F) (u v : C3.Complex3 F) →
    C3.complex3Subtract (realScale x u) (realScale y v)
    ≡ C3.complex3Add
        (realScale x (C3.complex3Subtract u v))
        (realScale (sub x y) v)
  vectorRing x y
      (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
    Field.complex3Ext
      (coordinate x y ux vx)
      (coordinate x y uy vy)
      (coordinate x y uz vz)

  coordinate :
    (x y : C3.Carrier F) (u v : C3.Complex F) →
    C3.complexSubtract
      (C3.complexMultiply (C3.realEmbed F x) u)
      (C3.complexMultiply (C3.realEmbed F y) v)
    ≡ C3.complexAdd
        (C3.complexMultiply (C3.realEmbed F x) (C3.complexSubtract u v))
        (C3.complexMultiply (C3.realEmbed F (sub x y)) v)
  coordinate x y u v =
    R.solve 4
      (λ x y u v →
        ((x R.⊗ u) R.⊕ (R.⊝ (y R.⊗ v)))
        R.⊜
        ((x R.⊗ (u R.⊕ (R.⊝ v)))
          R.⊕ ((x R.⊕ (R.⊝ y)) R.⊗ v)))
      refl (C3.realEmbed F x) (C3.realEmbed F y) u v
    where module R = Ring.Solver F

round172RawCurlDifferenceDualDefectClosed : Bool
round172RawCurlDifferenceDualDefectClosed = true

round172EveryRawDifferenceTermCarriesRadialOrAngularDefect : Bool
round172EveryRawDifferenceTermCarriesRadialOrAngularDefect = true

round172DualDefectL2PaymentClosed : Bool
round172DualDefectL2PaymentClosed = false

round172PackageAClosed : Bool
round172PackageAClosed = false

round172RawCurlDifferenceDualDefectClosedIsTrue :
  round172RawCurlDifferenceDualDefectClosed ≡ true
round172RawCurlDifferenceDualDefectClosedIsTrue = refl

round172PackageAClosedIsFalse : round172PackageAClosed ≡ false
round172PackageAClosedIsFalse = refl
