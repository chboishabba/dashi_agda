module DASHI.Physics.Closure.NSTriadKNHHDualDefectFactorizationRound173Exact where

------------------------------------------------------------------------
-- ROUND173 / COMPLETE ALGEBRAIC HH DUAL-DEFECT FACTORIZATION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact as R172

sub : ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
sub {F = F} x y = C3.add F x (C3.negate F y)

realScale : ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Complex3 F → C3.Complex3 F
realScale {F = F} scalar value =
  C3.complex3Scale (C3.realEmbed F scalar) value

rawDirectionalSlotKernelFactorsThroughDualDefects :
  ∀ {r} {F : C3.RealField r}
    (rp rq : C3.Carrier F)
    (P Q a b : C3.Complex3 F)
    (T : R145.TransverseHighPair P Q a b) →
  R172.rawDirectionalSlotKernel
    (realScale rp P) (realScale rq Q) a b
  ≡
  C3.complex3Add
    (realScale rp
      (C3.complex3Subtract
        (C3.complex3Add
          (C3.complex3Scale
            (C3.bilinearDot3 (R145.antiParallelDefect P Q) b) a)
          (C3.complex3Scale
            (C3.bilinearDot3 a (R145.antiParallelDefect P Q)) b))
        (C3.complex3Scale
          (C3.bilinearDot3 a b)
          (R145.antiParallelDefect P Q))))
    (realScale (sub rp rq)
      (Cross.complex3Cross a (Cross.complex3Cross Q b)))
rawDirectionalSlotKernelFactorsThroughDualDefects rp rq P Q a b T =
  trans
    (R172.rawDirectionalSlotKernelDualDefect rp rq P Q a b)
    (cong
      (λ angular →
        C3.complex3Add
          (realScale rp angular)
          (realScale (sub rp rq)
            (Cross.complex3Cross a (Cross.complex3Cross Q b))))
      (R145.slotKernelFactorsThroughAntiParallelDefect P Q a b T))

round173HHAlgebraicIntermediateAngleResidualExists : Bool
round173HHAlgebraicIntermediateAngleResidualExists = false

round173RawCurlHHFactorizationThroughTwoExactDefects : Bool
round173RawCurlHHFactorizationThroughTwoExactDefects = true

round173SpatiallyCriticalDualDefectL2BoundClosed : Bool
round173SpatiallyCriticalDualDefectL2BoundClosed = false

round173PackageAClosed : Bool
round173PackageAClosed = false

round173RawCurlHHFactorizationThroughTwoExactDefectsIsTrue :
  round173RawCurlHHFactorizationThroughTwoExactDefects ≡ true
round173RawCurlHHFactorizationThroughTwoExactDefectsIsTrue = refl

round173PackageAClosedIsFalse : round173PackageAClosed ≡ false
round173PackageAClosedIsFalse = refl
