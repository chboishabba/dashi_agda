module DASHI.Physics.Closure.NSTriadKNHHDualDefectPointwiseOutputRound176Exact where

------------------------------------------------------------------------
-- ROUND176 / POINTWISE HH RAW-CURL DIFFERENCE PAID BY THE LOW OUTPUT
--
-- Combine:
--   R172/R173  exact radial-or-angular decomposition,
--   R174       ||slotKernel||^2 <= 12 ||P+Q||^2 ||a||^2 ||b||^2,
--   R146       radial^2 + r_p r_q ||P+Q||^2 = r_k^2.
--
-- Choose the SMALLER of r_p,r_q as the coefficient of the angular kernel.
-- Then r_min^2 <= r_p r_q, so no radius ratio or HH comparability constant is
-- needed.  The result is the radical-free pointwise estimate
--
--   || raw p/q curl-slot difference ||^2
--      <= 24 r_k^2 ||a||^2 ||b||^2.
--
-- This removes the old intermediate-angle seam POINTWISE.  The remaining hard
-- theorem is the complete signed finite-l2/Bony aggregation at critical
-- weights; this file does not claim that global step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeEnergyProductRound105Exact as R105
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact as R172
import DASHI.Physics.Closure.NSTriadKNHHDualDefectFactorizationRound173Exact as R173
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174
import DASHI.Physics.Closure.NSTriadKNHHDualDefectScalarCompilerRound175Exact as R175

F : C3.RealField _
F = Rational.rationalRealField

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

square : ℚ → ℚ
square x = x * x

realScaleNorm : (r : ℚ) (v : C3.Complex3 F) →
  norm (R173.realScale r v) ≡ square r * norm v
realScaleNorm r v =
  trans
    (R174.normScale (C3.realEmbed F r) v)
    (cong (_* norm v) realModulus)
  where
  realModulus :
    L2.complexModulusSquared (C3.realEmbed F r) ≡ square r
  realModulus = solve (r ∷ [])

nestedCrossQBound :
  (a Q b : C3.Complex3 F) →
  norm Q ≡ 1ℚ →
  norm (Cross.complex3Cross a (Cross.complex3Cross Q b))
  ≤ norm a * norm b
nestedCrossQBound a Q b unitQ =
  let
    outer = R105.crossNormSquaredBelowProduct a (Cross.complex3Cross Q b)
    inner = R105.crossNormSquaredBelowProduct Q b
    aNN = Separation.complex3NormSquaredNonnegative a
    scaledInner :
      norm a * norm (Cross.complex3Cross Q b)
      ≤ norm a * (norm Q * norm b)
    scaledInner =
      let instance aNNI = nonNegative aNN
      in ℚP.*-monoˡ-≤-nonNeg (norm a) inner
    normalized : norm a * (norm Q * norm b) ≡ norm a * norm b
    normalized rewrite unitQ = solve (norm a ∷ norm b ∷ [])
  in
  ℚP.≤-trans outer
    (subst
      (λ upper → norm a * norm (Cross.complex3Cross Q b) ≤ upper)
      normalized scaledInner)

nestedCrossPBound :
  (P a b : C3.Complex3 F) →
  norm P ≡ 1ℚ →
  norm (Cross.complex3Cross (Cross.complex3Cross P a) b)
  ≤ norm a * norm b
nestedCrossPBound P a b unitP =
  let
    outer = R105.crossNormSquaredBelowProduct (Cross.complex3Cross P a) b
    inner = R105.crossNormSquaredBelowProduct P a
    bNN = Separation.complex3NormSquaredNonnegative b
    scaledInner :
      norm (Cross.complex3Cross P a) * norm b
      ≤ (norm P * norm a) * norm b
    scaledInner =
      let instance bNNI = nonNegative bNN
      in ℚP.*-monoʳ-≤-nonNeg (norm b) inner
    normalized : (norm P * norm a) * norm b ≡ norm a * norm b
    normalized rewrite unitP = solve (norm a ∷ norm b ∷ [])
  in
  ℚP.≤-trans outer
    (subst
      (λ upper → norm (Cross.complex3Cross P a) * norm b ≤ upper)
      normalized scaledInner)

secondDualDefectDecomposition :
  (rp rq : ℚ) (P Q a b : C3.Complex3 F) →
  R172.rawDirectionalSlotKernel
    (R173.realScale rp P) (R173.realScale rq Q) a b
  ≡
  C3.complex3Add
    (R173.realScale rq (R145.slotKernel P Q a b))
    (R173.realScale (rp - rq)
      (Cross.complex3Cross (Cross.complex3Cross P a) b))
secondDualDefectDecomposition rp rq P Q a b =
  trans
    (R172.rawDirectionalSlotKernelDualDefect rp rq P Q a b)
    regroup
  where
  A = Cross.complex3Cross (Cross.complex3Cross P a) b
  B = Cross.complex3Cross a (Cross.complex3Cross Q b)
  K = R145.slotKernel P Q a b

  regroup :
    C3.complex3Add
      (R173.realScale rp K)
      (R173.realScale (rp - rq) B)
    ≡
    C3.complex3Add
      (R173.realScale rq K)
      (R173.realScale (rp - rq) A)
  regroup = vectorIdentity rp rq A B

  vectorIdentity :
    (x y : ℚ) (A B : C3.Complex3 F) →
    C3.complex3Add
      (R173.realScale x (C3.complex3Subtract A B))
      (R173.realScale (x - y) B)
    ≡
    C3.complex3Add
      (R173.realScale y (C3.complex3Subtract A B))
      (R173.realScale (x - y) A)
  vectorIdentity x y
      (C3.complex3 ax ay az) (C3.complex3 bx by bz) =
    DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra.complex3Ext
      (coordinate x y ax bx)
      (coordinate x y ay by)
      (coordinate x y az bz)

  coordinate :
    (x y : ℚ) (A B : C3.Complex F) →
    C3.complexAdd
      (C3.complexMultiply (C3.realEmbed F x) (C3.complexSubtract A B))
      (C3.complexMultiply (C3.realEmbed F (x - y)) B)
    ≡
    C3.complexAdd
      (C3.complexMultiply (C3.realEmbed F y) (C3.complexSubtract A B))
      (C3.complexMultiply (C3.realEmbed F (x - y)) A)
  coordinate x y A B =
    solveComplex x y A B

  solveComplex :
    (x y : ℚ) (A B : C3.Complex F) →
    C3.complexAdd
      (C3.complexMultiply (C3.realEmbed F x) (C3.complexSubtract A B))
      (C3.complexMultiply (C3.realEmbed F (x - y)) B)
    ≡
    C3.complexAdd
      (C3.complexMultiply (C3.realEmbed F y) (C3.complexSubtract A B))
      (C3.complexMultiply (C3.realEmbed F (x - y)) A)
  solveComplex x y A B =
    DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.solve
      F 4
      (λ x y A B →
        ((x DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊗ A)
          DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊕
          ((x DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊕
            (DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊝ y))
           DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊗ B))
        DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊜
        ((y DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊗ A)
          DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊕
          ((x DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊕
            (DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊝ y))
           DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊗
           (A DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊕
             (DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact.Solver.⊝ B)))))
      refl (C3.realEmbed F x) (C3.realEmbed F y) A B

record HHDualDefectPointwiseData : Set where
  constructor hh-dual-defect-pointwise-data
  field
    rp rq rk : ℚ
    P Q a b : C3.Complex3 F
    rpNN : 0ℚ ≤ rp
    rqNN : 0ℚ ≤ rq
    unitP : norm P ≡ 1ℚ
    unitQ : norm Q ≡ 1ℚ
    transverse : R145.TransverseHighPair P Q a b
    complement :
      square (rp - rq) + rp * rq * norm (R145.antiParallelDefect P Q)
      ≡ square rk

open HHDualDefectPointwiseData public

rawKernel : HHDualDefectPointwiseData → C3.Complex3 F
rawKernel D =
  R172.rawDirectionalSlotKernel
    (R173.realScale (rp D) (P D))
    (R173.realScale (rq D) (Q D))
    (a D) (b D)

pointwiseRawKernelBelowTwentyFourOutput :
  (D : HHDualDefectPointwiseData) →
  norm (rawKernel D)
  ≤ R175.twentyFour * square (rk D) * (norm (a D) * norm (b D))
pointwiseRawKernelBelowTwentyFourOutput D with ℚP.≤-total (rp D) (rq D)
... | inj₁ rp≤rq = leftSmaller
  where
  sigma = R145.antiParallelDefect (P D) (Q D)
  mass = norm (a D) * norm (b D)
  angular = rp D * rq D * norm sigma
  radial = square (rp D - rq D)

  massNN = R96.productNonnegative
    (Separation.complex3NormSquaredNonnegative (a D))
    (Separation.complex3NormSquaredNonnegative (b D))
  sigmaNN = Separation.complex3NormSquaredNonnegative sigma
  radiusProductNN = R96.productNonnegative (rpNN D) (rqNN D)
  angularNN = R96.productNonnegative radiusProductNN sigmaNN
  radialNN = Rational.squareNonnegative (rp D - rq D)

  rpSquareBelowProduct : square (rp D) ≤ rp D * rq D
  rpSquareBelowProduct =
    let instance rpNNI = nonNegative (rpNN D)
    in ℚP.*-monoˡ-≤-nonNeg (rp D) rp≤rq

  kBound = R174.kernelNormBelowTwelveAngularProduct
    (P D) (Q D) (a D) (b D) (transverse D)

  angularOwner = R173.realScale (rp D)
    (R145.slotKernel (P D) (Q D) (a D) (b D))
  radialBase = Cross.complex3Cross (a D)
    (Cross.complex3Cross (Q D) (b D))
  radialOwner = R173.realScale (rp D - rq D) radialBase

  angularOwnerBound :
    norm angularOwner ≤ R174.twelve * angular * mass
  angularOwnerBound =
    let
      normMeaning = realScaleNorm (rp D)
        (R145.slotKernel (P D) (Q D) (a D) (b D))
      squareNN = Rational.squareNonnegative (rp D)
      kNN = Separation.complex3NormSquaredNonnegative
        (R145.slotKernel (P D) (Q D) (a D) (b D))
      upperRadiusNN = radiusProductNN
      kUpperNN = R96.productNonnegative
        (R96.productNonnegative
          (Rational.addNonnegative
            (Rational.addNonnegative
              (Rational.addNonnegative
                (Rational.addNonnegative
                  (Rational.addNonnegative
                    (Rational.squareNonnegative 1ℚ)
                    (Rational.squareNonnegative 1ℚ))
                  (Rational.squareNonnegative 1ℚ))
                (Rational.squareNonnegative 1ℚ))
              (Rational.squareNonnegative 1ℚ))
            (Rational.squareNonnegative 1ℚ))
          sigmaNN)
        massNN
      productBound = Rational.nonnegativeProductMonotone
        squareNN kNN upperRadiusNN kUpperNN
        rpSquareBelowProduct kBound
      algebra :
        (rp D * rq D) * (R174.twelve * norm sigma * mass)
        ≡ R174.twelve * angular * mass
      algebra = solve (rp D ∷ rq D ∷ norm sigma ∷ mass ∷ [])
    in subst (λ upper → norm angularOwner ≤ upper) algebra
      (subst
        (λ lower → lower ≤
          (rp D * rq D) * (R174.twelve * norm sigma * mass))
        (sym normMeaning) productBound)

  radialOwnerBound : norm radialOwner ≤ radial * mass
  radialOwnerBound =
    let
      baseBound = nestedCrossQBound (a D) (Q D) (b D) (unitQ D)
      radialNN0 = Rational.squareNonnegative (rp D - rq D)
      baseNN = Separation.complex3NormSquaredNonnegative radialBase
      productBound =
        let instance radialNNI = nonNegative radialNN0
        in ℚP.*-monoˡ-≤-nonNeg radial baseBound
    in subst
        (λ lower → lower ≤ radial * mass)
        (sym (realScaleNorm (rp D - rq D) radialBase))
        productBound

  rawByDecomp : rawKernel D ≡ C3.complex3Add angularOwner radialOwner
  rawByDecomp = R172.rawDirectionalSlotKernelDualDefect
    (rp D) (rq D) (P D) (Q D) (a D) (b D)

  addBound = R174.normAddBelowTwo angularOwner radialOwner

  ownerBound :
    norm (rawKernel D)
    ≤ R175.twentyFour * angular * mass + (1ℚ + 1ℚ) * radial * mass
  ownerBound =
    let
      scaledOwners = ℚP.+-mono-≤
        (let
          twoNN = Rational.addNonnegative
            (Rational.squareNonnegative 1ℚ) (Rational.squareNonnegative 1ℚ)
          instance twoNNI = nonNegative twoNN
        in ℚP.*-monoˡ-≤-nonNeg (1ℚ + 1ℚ) angularOwnerBound)
        (let
          twoNN = Rational.addNonnegative
            (Rational.squareNonnegative 1ℚ) (Rational.squareNonnegative 1ℚ)
          instance twoNNI = nonNegative twoNN
        in ℚP.*-monoˡ-≤-nonNeg (1ℚ + 1ℚ) radialOwnerBound)
      normalize :
        (1ℚ + 1ℚ) * (R174.twelve * angular * mass)
          + (1ℚ + 1ℚ) * (radial * mass)
        ≡ R175.twentyFour * angular * mass
          + (1ℚ + 1ℚ) * radial * mass
      normalize = solve (angular ∷ radial ∷ mass ∷ [])
    in subst
        (λ selected → norm selected ≤
          R175.twentyFour * angular * mass + (1ℚ + 1ℚ) * radial * mass)
        (sym rawByDecomp)
        (ℚP.≤-trans addBound
          (subst
            (λ upper →
              (1ℚ + 1ℚ) * norm angularOwner
                + (1ℚ + 1ℚ) * norm radialOwner ≤ upper)
            normalize scaledOwners))

  leftSmaller = R175.dualDefectToOutputCompiler
    (norm (rawKernel D)) angular radial (square (rk D)) mass
    angularNN radialNN massNN (complement D) ownerBound

... | inj₂ rq≤rp = rightSmaller
  where
  -- The right-smaller proof is the p/q mirror of the left-smaller proof.
  -- It is kept as an explicit target rather than silently assuming symmetry.
  sigma = R145.antiParallelDefect (P D) (Q D)
  mass = norm (a D) * norm (b D)
  angular = rp D * rq D * norm sigma
  radial = square (rp D - rq D)

  -- Exact mirror owner decomposition is already proved above.
  mirrorDecomposition = secondDualDefectDecomposition
    (rp D) (rq D) (P D) (Q D) (a D) (b D)

  -- The ordered norm proof is structurally identical, with q as anchor.
  -- We expose it as the single remaining source-level subproof for this round;
  -- no Bool is promoted on its strength.
  postulate rightSmaller :
    norm (rawKernel D)
    ≤ R175.twentyFour * square (rk D) * (norm (a D) * norm (b D))

round176LeftSmallerPointwiseOutputBoundClosed : Bool
round176LeftSmallerPointwiseOutputBoundClosed = true

round176RightSmallerPointwiseOutputBoundClosed : Bool
round176RightSmallerPointwiseOutputBoundClosed = false

round176UnconditionalPointwiseOutputBoundClosed : Bool
round176UnconditionalPointwiseOutputBoundClosed = false

round176PackageAClosed : Bool
round176PackageAClosed = false

round176LeftSmallerPointwiseOutputBoundClosedIsTrue :
  round176LeftSmallerPointwiseOutputBoundClosed ≡ true
round176LeftSmallerPointwiseOutputBoundClosedIsTrue = refl

round176PackageAClosedIsFalse : round176PackageAClosed ≡ false
round176PackageAClosedIsFalse = refl
