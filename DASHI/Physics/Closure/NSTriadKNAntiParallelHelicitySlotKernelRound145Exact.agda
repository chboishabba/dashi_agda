module DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact where

------------------------------------------------------------------------
-- ROUND145 / ANTI-PARALLEL FACTORIZATION OF THE HIGH-HIGH HELICITY-SLOT KERNEL
--
-- Sources:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Constantin--Majda, CMP 115 (1988), DOI 10.1007/BF01218019.
--
-- The p/q normalized-curl slot difference has vector kernel
--
--   (P x a) x b - a x (Q x b).
--
-- Exact BAC-CAB algebra gives
--
--   a(P.b) + b(a.Q) - (P+Q)(a.b).
--
-- If a.P=0 and b.Q=0, the first two scalar factors can be replaced by
-- (P+Q).b and a.(P+Q).  Thus every term factors through the anti-parallel
-- defect Sigma=P+Q.  The endpoint Sigma=0 is then a separate zero-normalizing
-- corollary; this file deliberately does not mark that corollary closed until
-- a kernel receipt checks the zero normalization on the exact C3 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross

antiParallelDefect :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
antiParallelDefect = C3.complex3Add

slotKernel :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
slotKernel P Q a b =
  C3.complex3Subtract
    (Cross.complex3Cross (Cross.complex3Cross P a) b)
    (Cross.complex3Cross a (Cross.complex3Cross Q b))

slotKernelBacCabIdentity :
  ∀ {r} {F : C3.RealField r}
    (P Q a b : C3.Complex3 F) →
  slotKernel P Q a b
  ≡
  C3.complex3Subtract
    (C3.complex3Add
      (C3.complex3Scale (C3.bilinearDot3 P b) a)
      (C3.complex3Scale (C3.bilinearDot3 a Q) b))
    (C3.complex3Scale
      (C3.bilinearDot3 a b)
      (antiParallelDefect P Q))
slotKernelBacCabIdentity {F = F}
    (C3.complex3 px py pz)
    (C3.complex3 qx qy qz)
    (C3.complex3 ax ay az)
    (C3.complex3 bx by bz) =
  Field.complex3Ext
    (R.solve 12 goalX refl px py pz qx qy qz ax ay az bx by bz)
    (R.solve 12 goalY refl px py pz qx qy qz ax ay az bx by bz)
    (R.solve 12 goalZ refl px py pz qx qy qz ax ay az bx by bz)
  where
  module R = Ring.Solver F
  dot = λ x y z X Y Z → ((x R.⊗ X) R.⊕ (y R.⊗ Y)) R.⊕ (z R.⊗ Z)
  goalX = λ px py pz qx qy qz ax ay az bx by bz →
    ((((py R.⊗ az) R.⊕ (R.⊝ (pz R.⊗ ay))) R.⊗ bz
       R.⊕ (R.⊝ (((pz R.⊗ ax) R.⊕ (R.⊝ (px R.⊗ az))) R.⊗ by)))
     R.⊕
     (R.⊝
       (ay R.⊗ ((qz R.⊗ bx) R.⊕ (R.⊝ (qx R.⊗ bz)))
        R.⊕ (R.⊝ (az R.⊗ ((qy R.⊗ bz) R.⊕ (R.⊝ (qz R.⊗ by))))))))
    R.⊜
    (((ax R.⊗ dot px py pz bx by bz)
       R.⊕ (bx R.⊗ dot ax ay az qx qy qz))
      R.⊕ (R.⊝ ((px R.⊕ qx) R.⊗ dot ax ay az bx by bz)))
  goalY = λ px py pz qx qy qz ax ay az bx by bz →
    ((((pz R.⊗ ax) R.⊕ (R.⊝ (px R.⊗ az))) R.⊗ bx
       R.⊕ (R.⊝ (((px R.⊗ ay) R.⊕ (R.⊝ (py R.⊗ ax))) R.⊗ bz)))
     R.⊕
     (R.⊝
       (az R.⊗ ((qx R.⊗ by) R.⊕ (R.⊝ (qy R.⊗ bx)))
        R.⊕ (R.⊝ (ax R.⊗ ((qz R.⊗ bx) R.⊕ (R.⊝ (qx R.⊗ bz))))))))
    R.⊜
    (((ay R.⊗ dot px py pz bx by bz)
       R.⊕ (by R.⊗ dot ax ay az qx qy qz))
      R.⊕ (R.⊝ ((py R.⊕ qy) R.⊗ dot ax ay az bx by bz)))
  goalZ = λ px py pz qx qy qz ax ay az bx by bz →
    ((((px R.⊗ ay) R.⊕ (R.⊝ (py R.⊗ ax))) R.⊗ by
       R.⊕ (R.⊝ (((py R.⊗ az) R.⊕ (R.⊝ (pz R.⊗ ay))) R.⊗ bx)))
     R.⊕
     (R.⊝
       (ax R.⊗ ((qy R.⊗ bz) R.⊕ (R.⊝ (qz R.⊗ by)))
        R.⊕ (R.⊝ (ay R.⊗ ((qx R.⊗ by) R.⊕ (R.⊝ (qy R.⊗ bx))))))))
    R.⊜
    (((az R.⊗ dot px py pz bx by bz)
       R.⊕ (bz R.⊗ dot ax ay az qx qy qz))
      R.⊕ (R.⊝ ((pz R.⊕ qz) R.⊗ dot ax ay az bx by bz)))

record TransverseHighPair
    {r} {F : C3.RealField r}
    (P Q a b : C3.Complex3 F) : Set r where
  constructor transverse-high-pair
  field
    aTransverseP : C3.bilinearDot3 a P ≡ C3.complexZero F
    bTransverseQ : C3.bilinearDot3 b Q ≡ C3.complexZero F

open TransverseHighPair public

slotKernelFactorsThroughAntiParallelDefect :
  ∀ {r} {F : C3.RealField r}
    (P Q a b : C3.Complex3 F) →
  TransverseHighPair P Q a b →
  slotKernel P Q a b
  ≡
  C3.complex3Subtract
    (C3.complex3Add
      (C3.complex3Scale
        (C3.bilinearDot3 (antiParallelDefect P Q) b) a)
      (C3.complex3Scale
        (C3.bilinearDot3 a (antiParallelDefect P Q)) b))
    (C3.complex3Scale
      (C3.bilinearDot3 a b)
      (antiParallelDefect P Q))
slotKernelFactorsThroughAntiParallelDefect {F = F} P Q a b T =
  trans
    (slotKernelBacCabIdentity P Q a b)
    (cong₂ C3.complex3Subtract
      (cong₂ C3.complex3Add
        (cong (λ scalar → C3.complex3Scale scalar a)
          (trans
            (Additive.bilinearDot3LeftAdd P Q b)
            (cong (C3.complexAdd (C3.bilinearDot3 P b))
              (trans
                (Algebra.bilinearDot3Commutative Q b)
                (bTransverseQ T)))))
        (cong (λ scalar → C3.complex3Scale scalar b)
          (trans
            (Algebra.bilinearDot3RightAdd a P Q)
            (cong (λ left → C3.complexAdd left (C3.bilinearDot3 a Q))
              (aTransverseP T)))))
      refl)

round145HighHighSlotKernelAntiParallelFactorizationClosed : Bool
round145HighHighSlotKernelAntiParallelFactorizationClosed = true

round145AntiParallelEndpointZeroNormalizationClosed : Bool
round145AntiParallelEndpointZeroNormalizationClosed = false

round145IntraShellL2AggregationClosed : Bool
round145IntraShellL2AggregationClosed = false

round145PackageAClosed : Bool
round145PackageAClosed = false

round145HighHighSlotKernelAntiParallelFactorizationClosedIsTrue :
  round145HighHighSlotKernelAntiParallelFactorizationClosed ≡ true
round145HighHighSlotKernelAntiParallelFactorizationClosedIsTrue = refl

round145AntiParallelEndpointZeroNormalizationClosedIsFalse :
  round145AntiParallelEndpointZeroNormalizationClosed ≡ false
round145AntiParallelEndpointZeroNormalizationClosedIsFalse = refl

round145PackageAClosedIsFalse : round145PackageAClosed ≡ false
round145PackageAClosedIsFalse = refl
