module DASHI.Physics.Closure.NSTriadKNHHDualDefectUnconditionalPointwiseRound177Exact where

------------------------------------------------------------------------
-- ROUND177 / UNCONDITIONAL POINTWISE HH OUTPUT GAIN BY p/q SWAP
--
-- Round176 proves the low-output bound when r_p <= r_q.  The raw directional
-- slot kernel is invariant when (p,a) and (q,b) are swapped simultaneously.
-- The transverse hypotheses and radial/angular complementarity are likewise
-- symmetric.  Totality of the rational order therefore closes the other branch
-- without a new estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact as R172
import DASHI.Physics.Closure.NSTriadKNHHDualDefectFactorizationRound173Exact as R173
import DASHI.Physics.Closure.NSTriadKNHHDualDefectLeftAnchorRound176Exact as R176

F = R176.F

crossSwapNegate : (u v : C3.Complex3 F) →
  Cross.complex3Cross v u ≡ C3.complex3Negate (Cross.complex3Cross u v)
crossSwapNegate
    (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Field.complex3Ext
    (R.solve 4
      (λ uy uz vy vz →
        ((vy R.⊗ uz) R.⊕ (R.⊝ (vz R.⊗ uy)))
        R.⊜ R.⊝ ((uy R.⊗ vz) R.⊕ (R.⊝ (uz R.⊗ vy))))
      refl uy uz vy vz)
    (R.solve 4
      (λ uz ux vz vx →
        ((vz R.⊗ ux) R.⊕ (R.⊝ (vx R.⊗ uz)))
        R.⊜ R.⊝ ((uz R.⊗ vx) R.⊕ (R.⊝ (ux R.⊗ vz))))
      refl uz ux vz vx)
    (R.solve 4
      (λ ux uy vx vy →
        ((vx R.⊗ uy) R.⊕ (R.⊝ (vy R.⊗ ux)))
        R.⊜ R.⊝ ((ux R.⊗ vy) R.⊕ (R.⊝ (uy R.⊗ vx))))
      refl ux uy vx vy)
  where module R = Ring.Solver F

rawKernelSwapInvariant :
  (p q a b : C3.Complex3 F) →
  R172.rawDirectionalSlotKernel p q a b
  ≡ R172.rawDirectionalSlotKernel q p b a
rawKernelSwapInvariant p q a b =
  let
    A = Cross.complex3Cross (Cross.complex3Cross p a) b
    B = Cross.complex3Cross a (Cross.complex3Cross q b)

    swappedFirst :
      Cross.complex3Cross (Cross.complex3Cross q b) a
      ≡ C3.complex3Negate B
    swappedFirst = crossSwapNegate a (Cross.complex3Cross q b)

    swappedSecond :
      Cross.complex3Cross b (Cross.complex3Cross p a)
      ≡ C3.complex3Negate A
    swappedSecond = crossSwapNegate (Cross.complex3Cross p a) b
  in
  sym
    (trans
      (cong₂ C3.complex3Subtract swappedFirst swappedSecond)
      (vectorNegateSubtractSwap A B))
  where
  vectorNegateSubtractSwap :
    (A B : C3.Complex3 F) →
    C3.complex3Subtract (C3.complex3Negate B) (C3.complex3Negate A)
    ≡ C3.complex3Subtract A B
  vectorNegateSubtractSwap
      (C3.complex3 ax ay az) (C3.complex3 bx by bz) =
    Field.complex3Ext
      (coord ax bx) (coord ay by) (coord az bz)
    where
    coord : (a b : C3.Complex F) →
      C3.complexSubtract (C3.complexNegate b) (C3.complexNegate a)
      ≡ C3.complexSubtract a b
    coord a b =
      R.solve 2
        (λ a b → (R.⊝ b) R.⊕ (R.⊝ (R.⊝ a))
          R.⊜ a R.⊕ (R.⊝ b)) refl a b
      where module R = Ring.Solver F

antiParallelDefectSwap : (P Q : C3.Complex3 F) →
  R145.antiParallelDefect Q P ≡ R145.antiParallelDefect P Q
antiParallelDefectSwap
    (C3.complex3 px py pz) (C3.complex3 qx qy qz) =
  Field.complex3Ext
    (Field.complexAddCommutative qx px)
    (Field.complexAddCommutative qy py)
    (Field.complexAddCommutative qz pz)

transverseSwap :
  (P Q a b : C3.Complex3 F) →
  R145.TransverseHighPair P Q a b →
  R145.TransverseHighPair Q P b a
transverseSwap P Q a b T = record
  { R145.transverseA = R145.transverseB T
  ; R145.transverseB = R145.transverseA T
  }

swapData :
  (D : R176.LeftAnchorDualDefectData) →
  R176.LeftAnchorDualDefectData
swapData D = D

record SymmetricDualDefectData : Set where
  constructor symmetric-dual-defect-data
  field
    rp rq rk : ℚ
    P Q a b : C3.Complex3 F
    rpNN : 0 R176.≤ rp
    rqNN : 0 R176.≤ rq
    unitP : R176.norm P ≡ 1
    unitQ : R176.norm Q ≡ 1
    transverse : R145.TransverseHighPair P Q a b
    complement :
      R176.square (rp - rq)
        + rp * rq * R176.norm (R145.antiParallelDefect P Q)
      ≡ R176.square rk

open SymmetricDualDefectData public

rawKernel : SymmetricDualDefectData → C3.Complex3 F
rawKernel D =
  R172.rawDirectionalSlotKernel
    (R173.realScale (rp D) (P D))
    (R173.realScale (rq D) (Q D))
    (a D) (b D)

unconditionalPointwiseHHOutputBound :
  (D : SymmetricDualDefectData) →
  R176.norm (rawKernel D)
  ≤ R175.twentyFour * R176.square (rk D)
      * (R176.norm (a D) * R176.norm (b D))
unconditionalPointwiseHHOutputBound D with ℚP.≤-total (rp D) (rq D)
... | inj₁ rp≤rq =
  R176.leftAnchorRawKernelBelowTwentyFourOutput leftData
  where
  leftData : R176.LeftAnchorDualDefectData
  leftData = record
    { R176.rp = rp D
    ; R176.rq = rq D
    ; R176.rk = rk D
    ; R176.P = P D
    ; R176.Q = Q D
    ; R176.a = a D
    ; R176.b = b D
    ; R176.rpNN = rpNN D
    ; R176.rqNN = rqNN D
    ; R176.rpBelowRq = rp≤rq
    ; R176.unitQ = unitQ D
    ; R176.transverse = transverse D
    ; R176.complement = complement D
    }
... | inj₂ rq≤rp =
  subst
    (λ selected →
      R176.norm selected
      ≤ R175.twentyFour * R176.square (rk D)
          * (R176.norm (a D) * R176.norm (b D)))
    (sym kernelSwap)
    (subst
      (λ mass →
        R176.norm swappedKernel
        ≤ R175.twentyFour * R176.square (rk D) * mass)
      massSwap
      (R176.leftAnchorRawKernelBelowTwentyFourOutput rightData))
  where
  swappedKernel =
    R172.rawDirectionalSlotKernel
      (R173.realScale (rq D) (Q D))
      (R173.realScale (rp D) (P D))
      (b D) (a D)

  kernelSwap : rawKernel D ≡ swappedKernel
  kernelSwap = rawKernelSwapInvariant
    (R173.realScale (rp D) (P D))
    (R173.realScale (rq D) (Q D))
    (a D) (b D)

  massSwap : R176.norm (b D) * R176.norm (a D)
    ≡ R176.norm (a D) * R176.norm (b D)
  massSwap = ℚP.*-comm (R176.norm (b D)) (R176.norm (a D))

  complementSwap :
    R176.square (rq D - rp D)
      + rq D * rp D * R176.norm (R145.antiParallelDefect (Q D) (P D))
    ≡ R176.square (rk D)
  complementSwap =
    trans normalize (complement D)
    where
    normalize :
      R176.square (rq D - rp D)
        + rq D * rp D * R176.norm (R145.antiParallelDefect (Q D) (P D))
      ≡
      R176.square (rp D - rq D)
        + rp D * rq D * R176.norm (R145.antiParallelDefect (P D) (Q D))
    normalize rewrite antiParallelDefectSwap (P D) (Q D) =
      solve
        (rp D ∷ rq D ∷ R176.norm (R145.antiParallelDefect (P D) (Q D)) ∷ [])

  rightData : R176.LeftAnchorDualDefectData
  rightData = record
    { R176.rp = rq D
    ; R176.rq = rp D
    ; R176.rk = rk D
    ; R176.P = Q D
    ; R176.Q = P D
    ; R176.a = b D
    ; R176.b = a D
    ; R176.rpNN = rqNN D
    ; R176.rqNN = rpNN D
    ; R176.rpBelowRq = rq≤rp
    ; R176.unitQ = unitP D
    ; R176.transverse = transverseSwap (P D) (Q D) (a D) (b D) (transverse D)
    ; R176.complement = complementSwap
    }

round177UnconditionalPointwiseHHOutputBoundClosed : Bool
round177UnconditionalPointwiseHHOutputBoundClosed = true

round177UsesRadiusRatio : Bool
round177UsesRadiusRatio = false

round177UsesAnglePartition : Bool
round177UsesAnglePartition = false

round177GlobalCriticalBonyAggregationClosed : Bool
round177GlobalCriticalBonyAggregationClosed = false

round177PackageAClosed : Bool
round177PackageAClosed = false

round177UnconditionalPointwiseHHOutputBoundClosedIsTrue :
  round177UnconditionalPointwiseHHOutputBoundClosed ≡ true
round177UnconditionalPointwiseHHOutputBoundClosedIsTrue = refl

round177PackageAClosedIsFalse : round177PackageAClosed ≡ false
round177PackageAClosedIsFalse = refl
