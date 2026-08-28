module DASHI.Physics.Closure.NSTriadKNHHDualDefectFactorizationRound173Exact where

------------------------------------------------------------------------
-- ROUND173 / COMPLETE ALGEBRAIC HH DUAL-DEFECT FACTORIZATION
--
-- Compose Round172 with Round145.  For transverse high inputs the raw p/q curl
-- slot difference is a sum of exactly TWO owners:
--
--   angular owner = r_p * K(P,Q,a,b),    K factors through Sigma=P+Q,
--   radial owner  = (r_p-r_q) * [a x (Q x b)].
--
-- Therefore no term survives when both defects vanish, and there is no
-- intermediate-angle residual at the algebraic level.  The remaining task is
-- purely quantitative: obtain the spatially critical finite-l2 bound for these
-- two owners and sum it on the literal Bony/residual carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact as R172

rawDirectionalSlotKernelFactorsThroughDualDefects :
  ∀ {r} {F : C3.RealField r}
    (rp rq : C3.Carrier F)
    (P Q a b : C3.Complex3 F)
    (T : R145.TransverseHighPair P Q a b) →
  R172.rawDirectionalSlotKernel
    (R172.realScale rp P) (R172.realScale rq Q) a b
  ≡
  C3.complex3Add
    (R172.realScale rp
      (C3.complex3Subtract
        (C3.complex3Add
          (C3.complex3Scale
            (C3.bilinearDot3 (R145.antiParallelDefect P Q) b) a)
          (C3.complex3Scale
            (C3.bilinearDot3 a (R145.antiParallelDefect P Q)) b))
        (C3.complex3Scale
          (C3.bilinearDot3 a b)
          (R145.antiParallelDefect P Q))))
    (R172.realScale (R172.sub rp rq)
      (Cross.complex3Cross a (Cross.complex3Cross Q b)))
rawDirectionalSlotKernelFactorsThroughDualDefects rp rq P Q a b T =
  trans
    (R172.rawDirectionalSlotKernelDualDefect rp rq P Q a b)
    (cong
      (λ angular →
        C3.complex3Add
          (R172.realScale rp angular)
          (R172.realScale (R172.sub rp rq)
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
