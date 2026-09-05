module DASHI.Physics.Plasma.MHDComplex3VectorTripleProductExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; _≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Plasma.MHDDoubledInductionVectorKernelWeldExact as Kernel

------------------------------------------------------------------------
-- GENERIC COMPLEX3 VECTOR TRIPLE PRODUCT
------------------------------------------------------------------------

vectorTripleProduct :
  ∀ {r : Level} {F : C3.RealField r}
    (a b c : C3.Complex3 F) →
  Cross.complex3Cross a (Cross.complex3Cross b c)
  ≡
  C3.complex3Subtract
    (C3.complex3Scale (C3.bilinearDot3 a c) b)
    (C3.complex3Scale (C3.bilinearDot3 a b) c)
vectorTripleProduct {F = F}
    (C3.complex3 ax ay az)
    (C3.complex3 bx by bz)
    (C3.complex3 cx cy cz) =
  Field.complex3Ext
    (R.solve 9
      (λ ax ay az bx by bz cx cy cz →
        ((ay R.⊗ ((bz R.⊗ cx) R.⊕ (R.⊝ (bx R.⊗ cz))))
          R.⊕
          (R.⊝ (az R.⊗ ((bx R.⊗ cy) R.⊕ (R.⊝ (by R.⊗ cx))))))
        R.⊜
        (((((ax R.⊗ cx) R.⊕ (ay R.⊗ cy)) R.⊕ (az R.⊗ cz)) R.⊗ bx)
          R.⊕
          (R.⊝ (((((ax R.⊗ bx) R.⊕ (ay R.⊗ by)) R.⊕ (az R.⊗ bz)) R.⊗ cx)))))
      refl ax ay az bx by bz cx cy cz)
    (R.solve 9
      (λ ax ay az bx by bz cx cy cz →
        ((az R.⊗ ((by R.⊗ cx) R.⊕ (R.⊝ (bx R.⊗ cy))))
          R.⊕
          (R.⊝ (ax R.⊗ ((by R.⊗ cz) R.⊕ (R.⊝ (bz R.⊗ cy))))))
        R.⊜
        (((((ax R.⊗ cx) R.⊕ (ay R.⊗ cy)) R.⊕ (az R.⊗ cz)) R.⊗ by)
          R.⊕
          (R.⊝ (((((ax R.⊗ bx) R.⊕ (ay R.⊗ by)) R.⊕ (az R.⊗ bz)) R.⊗ cy)))))
      refl ax ay az bx by bz cx cy cz)
    (R.solve 9
      (λ ax ay az bx by bz cx cy cz →
        ((ax R.⊗ ((bx R.⊗ cy) R.⊕ (R.⊝ (by R.⊗ cx))))
          R.⊕
          (R.⊝ (ay R.⊗ ((bz R.⊗ cx) R.⊕ (R.⊝ (bx R.⊗ cz))))))
        R.⊜
        (((((ax R.⊗ cx) R.⊕ (ay R.⊗ cy)) R.⊕ (az R.⊗ cz)) R.⊗ bz)
          R.⊕
          (R.⊝ (((((ax R.⊗ bx) R.⊕ (ay R.⊗ by)) R.⊕ (az R.⊗ bz)) R.⊗ cz)))))
      refl ax ay az bx by bz cx cy cz)
  where module R = Ring.Solver F

------------------------------------------------------------------------
-- RESONANT/TRANSVERSE SPECIALIZATION USED BY IDEAL INDUCTION
------------------------------------------------------------------------

record ResonantInductionGeometry
    {r : Level} {F : C3.RealField r}
    (p q k u b : C3.Complex3 F) : Set r where
  constructor resonant-induction-geometry
  field
    outputWaveIsSum : k ≡ C3.complex3Add p q
    velocityTransverseAtP : C3.bilinearDot3 p u ≡ C3.complexZero F
    magneticTransverseAtQ : C3.bilinearDot3 q b ≡ C3.complexZero F

open ResonantInductionGeometry public

sumDotMagneticRelocatesToP :
  ∀ {r : Level} {F : C3.RealField r}
    (p q b : C3.Complex3 F) →
  C3.bilinearDot3 q b ≡ C3.complexZero F →
  C3.bilinearDot3 (C3.complex3Add p q) b
  ≡ C3.bilinearDot3 p b
sumDotMagneticRelocatesToP {F = F} p q b transverse =
  trans
    (Kernel.dotAddLeft p q b)
    (trans
      (cong (C3.complexAdd (C3.bilinearDot3 p b)) transverse)
      (Field.complexAddZeroRight (C3.bilinearDot3 p b)))

sumDotVelocityRelocatesToQ :
  ∀ {r : Level} {F : C3.RealField r}
    (p q u : C3.Complex3 F) →
  C3.bilinearDot3 p u ≡ C3.complexZero F →
  C3.bilinearDot3 (C3.complex3Add p q) u
  ≡ C3.bilinearDot3 q u
sumDotVelocityRelocatesToQ {F = F} p q u transverse =
  trans
    (Kernel.dotAddLeft p q u)
    (trans
      (cong (λ left → C3.complexAdd left (C3.bilinearDot3 q u)) transverse)
      (Field.complexAddZeroLeft (C3.bilinearDot3 q u)))

inductionKernelIsNegativeCurlCross :
  ∀ {r : Level} {F : C3.RealField r}
    (p q k u b : C3.Complex3 F)
    (G : ResonantInductionGeometry p q k u b) →
  C3.complex3Subtract
    (C3.complex3Scale (C3.bilinearDot3 u q) b)
    (C3.complex3Scale (C3.bilinearDot3 b p) u)
  ≡ C3.complex3Negate
      (Cross.complex3Cross k (Cross.complex3Cross u b))
inductionKernelIsNegativeCurlCross {F = F} p q k u b G
  rewrite outputWaveIsSum G
        | sumDotMagneticRelocatesToP p q b (magneticTransverseAtQ G)
        | sumDotVelocityRelocatesToQ p q u (velocityTransverseAtP G)
        | Algebra.bilinearDot3Commutative u q
        | Algebra.bilinearDot3Commutative b p
        | vectorTripleProduct (C3.complex3Add p q) u b =
  finalNegate
  where
  finalNegate :
    C3.complex3Subtract
      (C3.complex3Scale (C3.bilinearDot3 q u) b)
      (C3.complex3Scale (C3.bilinearDot3 p b) u)
    ≡
    C3.complex3Negate
      (C3.complex3Subtract
        (C3.complex3Scale (C3.bilinearDot3 p b) u)
        (C3.complex3Scale (C3.bilinearDot3 q u) b))
  finalNegate
      rewrite Field.complex3NegateSubtract
        (C3.complex3Scale (C3.bilinearDot3 p b) u)
        (C3.complex3Scale (C3.bilinearDot3 q u) b) = refl

record VectorTripleProductBoundary : Set where
  constructor vector-triple-product-boundary
  field
    generalComplex3TripleProductOwned : Bool
    generalComplex3TripleProductOwnedIsTrue : generalComplex3TripleProductOwned ≡ true

    resonantTransverseInductionCurlFormOwned : Bool
    resonantTransverseInductionCurlFormOwnedIsTrue :
      resonantTransverseInductionCurlFormOwned ≡ true

    hermitianCyclicPermutationUsed : Bool
    hermitianCyclicPermutationUsedIsFalse : hermitianCyclicPermutationUsed ≡ false

canonicalVectorTripleProductBoundary : VectorTripleProductBoundary
canonicalVectorTripleProductBoundary =
  vector-triple-product-boundary true refl true refl false refl
