module DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact where

------------------------------------------------------------------------
-- ROUND174 / RATIONAL L2 BOUND FOR THE HH QUADRATIC ANTI-PARALLEL KERNEL
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145

F : C3.RealField _
F = Rational.rationalRealField

two four twelve : ℚ
two = 1ℚ + 1ℚ
four = two + two
twelve = four + four + four

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

mod2 : C3.Complex F → ℚ
mod2 = L2.complexModulusSquared

normScale : (scalar : C3.Complex F) (v : C3.Complex3 F) →
  norm (C3.complex3Scale scalar v) ≡ mod2 scalar * norm v
normScale
    (C3.complex sr si)
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (sr ∷ si ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

normNegate : (v : C3.Complex3 F) → norm (C3.complex3Negate v) ≡ norm v
normNegate
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

normAddBelowTwo : (u v : C3.Complex3 F) →
  norm (C3.complex3Add u v) ≤ two * norm u + two * norm v
normAddBelowTwo
    (C3.complex3
      (C3.complex axr axi) (C3.complex ayr ayi) (C3.complex azr azi))
    (C3.complex3
      (C3.complex bxr bxi) (C3.complex byr byi) (C3.complex bzr bzi)) =
  let
    defect =
        Rational.square (axr - bxr) + Rational.square (axi - bxi)
      + Rational.square (ayr - byr) + Rational.square (ayi - byi)
      + Rational.square (azr - bzr) + Rational.square (azi - bzi)

    defectNN : 0ℚ ≤ defect
    defectNN =
      Rational.addNonnegative
        (Rational.addNonnegative
          (Rational.addNonnegative
            (Rational.addNonnegative
              (Rational.addNonnegative
                (Rational.squareNonnegative (axr - bxr))
                (Rational.squareNonnegative (axi - bxi)))
              (Rational.squareNonnegative (ayr - byr)))
            (Rational.squareNonnegative (ayi - byi)))
          (Rational.squareNonnegative (azr - bzr)))
        (Rational.squareNonnegative (azi - bzi))

    lower = norm
      (C3.complex3
        (C3.complex (axr + bxr) (axi + bxi))
        (C3.complex (ayr + byr) (ayi + byi))
        (C3.complex (azr + bzr) (azi + bzi)))

    withDefect : lower ≤ lower + defect
    withDefect =
      subst (lower ≤_) (sym (ℚP.+-identityʳ lower))
        (ℚP.+-mono-≤ ℚP.≤-refl defectNN)
  in
  subst (lower ≤_)
    (solve
      ( axr ∷ axi ∷ ayr ∷ ayi ∷ azr ∷ azi
      ∷ bxr ∷ bxi ∷ byr ∷ byi ∷ bzr ∷ bzi ∷ []))
    withDefect

normThreeBelowFourSum : (x y z : C3.Complex3 F) →
  norm (C3.complex3Add (C3.complex3Add x y) z)
  ≤ four * (norm x + norm y + norm z)
normThreeBelowFourSum x y z =
  let
    first = normAddBelowTwo (C3.complex3Add x y) z
    xy = normAddBelowTwo x y
    zNN = Separation.complex3NormSquaredNonnegative z
    oneNN : 0ℚ ≤ 1ℚ
    oneNN = Rational.squareNonnegative 1ℚ
    twoNN : 0ℚ ≤ two
    twoNN = Rational.addNonnegative oneNN oneNN

    scaledXY :
      two * norm (C3.complex3Add x y)
      ≤ two * (two * norm x + two * norm y)
    scaledXY =
      let instance tNN = nonNegative twoNN
      in ℚP.*-monoˡ-≤-nonNeg two xy

    combine :
      two * norm (C3.complex3Add x y) + two * norm z
      ≤ two * (two * norm x + two * norm y) + two * norm z
    combine = ℚP.+-mono-≤ scaledXY ℚP.≤-refl

    endpoint :
      two * (two * norm x + two * norm y) + two * norm z
      ≤ four * (norm x + norm y + norm z)
    endpoint =
      let
        zGap : 0ℚ ≤ two * norm z
        zGap = R96.productNonnegative twoNN zNN
        algebra :
          four * (norm x + norm y + norm z)
          ≡ (two * (two * norm x + two * norm y) + two * norm z)
             + two * norm z
        algebra = solve (norm x ∷ norm y ∷ norm z ∷ [])
        addGap :
          two * (two * norm x + two * norm y) + two * norm z
          ≤ (two * (two * norm x + two * norm y) + two * norm z)
             + two * norm z
        addGap =
          subst
            (λ left → left ≤
              (two * (two * norm x + two * norm y) + two * norm z)
                + two * norm z)
            (sym (ℚP.+-identityʳ
              (two * (two * norm x + two * norm y) + two * norm z)))
            (ℚP.+-mono-≤ ℚP.≤-refl zGap)
      in subst
          (λ upper →
            two * (two * norm x + two * norm y) + two * norm z ≤ upper)
          (sym algebra) addGap
  in ℚP.≤-trans first (ℚP.≤-trans combine endpoint)

scaleTermBound : (scalar : C3.Complex F) (v : C3.Complex3 F) (upper : ℚ) →
  mod2 scalar ≤ upper → 0ℚ ≤ norm v →
  norm (C3.complex3Scale scalar v) ≤ upper * norm v
scaleTermBound scalar v upper scalarBound vNN =
  subst
    (λ lower → lower ≤ upper * norm v)
    (sym (normScale scalar v))
    (let instance vNNI = nonNegative vNN
     in ℚP.*-monoʳ-≤-nonNeg (norm v) scalarBound)

kernelNormBelowTwelveAngularProduct :
  (P Q a b : C3.Complex3 F) →
  R145.TransverseHighPair P Q a b →
  norm (R145.slotKernel P Q a b)
  ≤ twelve * (norm (R145.antiParallelDefect P Q) * norm a * norm b)
kernelNormBelowTwelveAngularProduct P Q a b T =
  let
    sigma = R145.antiParallelDefect P Q
    x = C3.complex3Scale (C3.bilinearDot3 sigma b) a
    y = C3.complex3Scale (C3.bilinearDot3 a sigma) b
    z = C3.complex3Negate
      (C3.complex3Scale (C3.bilinearDot3 a b) sigma)

    aNN = Separation.complex3NormSquaredNonnegative a
    bNN = Separation.complex3NormSquaredNonnegative b
    sNN = Separation.complex3NormSquaredNonnegative sigma

    sb = R96.rationalBilinearDotCauchy sigma b
    as = R96.rationalBilinearDotCauchy a sigma
    ab = R96.rationalBilinearDotCauchy a b

    xBound : norm x ≤ (norm sigma * norm b) * norm a
    xBound = scaleTermBound (C3.bilinearDot3 sigma b) a
      (norm sigma * norm b) sb aNN

    yBound : norm y ≤ (norm a * norm sigma) * norm b
    yBound = scaleTermBound (C3.bilinearDot3 a sigma) b
      (norm a * norm sigma) as bNN

    zBase :
      norm (C3.complex3Scale (C3.bilinearDot3 a b) sigma)
      ≤ (norm a * norm b) * norm sigma
    zBase = scaleTermBound (C3.bilinearDot3 a b) sigma
      (norm a * norm b) ab sNN

    zBound : norm z ≤ (norm a * norm b) * norm sigma
    zBound = subst
      (λ lower → lower ≤ (norm a * norm b) * norm sigma)
      (sym (normNegate
        (C3.complex3Scale (C3.bilinearDot3 a b) sigma))) zBase

    three = normThreeBelowFourSum x y z

    sumBound :
      norm x + norm y + norm z
      ≤ (norm sigma * norm b) * norm a
        + (norm a * norm sigma) * norm b
        + (norm a * norm b) * norm sigma
    sumBound = ℚP.+-mono-≤ (ℚP.+-mono-≤ xBound yBound) zBound

    oneNN : 0ℚ ≤ 1ℚ
    oneNN = Rational.squareNonnegative 1ℚ
    twoNN = Rational.addNonnegative oneNN oneNN
    fourNN = Rational.addNonnegative twoNN twoNN
    scaled =
      let instance fNN = nonNegative fourNN
      in ℚP.*-monoˡ-≤-nonNeg four sumBound

    algebra :
      four *
        ((norm sigma * norm b) * norm a
          + (norm a * norm sigma) * norm b
          + (norm a * norm b) * norm sigma)
      ≡ twelve * (norm sigma * norm a * norm b)
    algebra = solve (norm sigma ∷ norm a ∷ norm b ∷ [])

    termSumBound :
      four * (norm x + norm y + norm z)
      ≤ twelve * (norm sigma * norm a * norm b)
    termSumBound = subst
      (λ upper → four * (norm x + norm y + norm z) ≤ upper)
      algebra scaled

    factorMeaning = R145.slotKernelFactorsThroughAntiParallelDefect P Q a b T
    rhsMeaning :
      C3.complex3Subtract
        (C3.complex3Add x y)
        (C3.complex3Scale (C3.bilinearDot3 a b) sigma)
      ≡ C3.complex3Add (C3.complex3Add x y) z
    rhsMeaning = refl
  in
  subst
    (λ selected → norm selected ≤
      twelve * (norm sigma * norm a * norm b))
    (sym (trans factorMeaning rhsMeaning))
    (ℚP.≤-trans three termSumBound)

round174QuadraticKernelAngularL2BoundClosed : Bool
round174QuadraticKernelAngularL2BoundClosed = true

round174KernelBoundHasCardinalityFactor : Bool
round174KernelBoundHasCardinalityFactor = false

round174KernelBoundUsesSquareRoot : Bool
round174KernelBoundUsesSquareRoot = false

round174GlobalBonySummationClosed : Bool
round174GlobalBonySummationClosed = false

round174PackageAClosed : Bool
round174PackageAClosed = false

round174QuadraticKernelAngularL2BoundClosedIsTrue :
  round174QuadraticKernelAngularL2BoundClosed ≡ true
round174QuadraticKernelAngularL2BoundClosedIsTrue = refl

round174PackageAClosedIsFalse : round174PackageAClosed ≡ false
round174PackageAClosedIsFalse = refl
