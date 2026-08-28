module DASHI.Physics.Closure.NSTriadKNHHDualDefectLeftAnchorRound176Exact where

------------------------------------------------------------------------
-- ROUND176 / LEFT-SMALLER HH RAW-CURL DIFFERENCE PAID BY LOW OUTPUT
--
-- Under r_p <= r_q, R172 anchors the angular kernel at r_p.  Hence
-- r_p^2 <= r_p r_q, and the R174 angular bound plus the radial nested-cross
-- bound fit exactly into R175's dual-defect compiler.
--
-- Result:
--   ||D_pq||^2 <= 24 r_k^2 ||a||^2 ||b||^2.
--
-- This file handles one total-order branch only and contains no postulate.
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
  realModulus : L2.complexModulusSquared (C3.realEmbed F r) ≡ square r
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

record LeftAnchorDualDefectData : Set where
  constructor left-anchor-dual-defect-data
  field
    rp rq rk : ℚ
    P Q a b : C3.Complex3 F
    rpNN : 0ℚ ≤ rp
    rqNN : 0ℚ ≤ rq
    rpBelowRq : rp ≤ rq
    unitQ : norm Q ≡ 1ℚ
    transverse : R145.TransverseHighPair P Q a b
    complement :
      square (rp - rq) + rp * rq * norm (R145.antiParallelDefect P Q)
      ≡ square rk

open LeftAnchorDualDefectData public

rawKernel : LeftAnchorDualDefectData → C3.Complex3 F
rawKernel D =
  R172.rawDirectionalSlotKernel
    (R173.realScale (rp D) (P D))
    (R173.realScale (rq D) (Q D))
    (a D) (b D)

leftAnchorRawKernelBelowTwentyFourOutput :
  (D : LeftAnchorDualDefectData) →
  norm (rawKernel D)
  ≤ R175.twentyFour * square (rk D) * (norm (a D) * norm (b D))
leftAnchorRawKernelBelowTwentyFourOutput D =
  R175.dualDefectToOutputCompiler
    (norm (rawKernel D)) angular radial (square (rk D)) mass
    angularNN radialNN massNN (complement D) ownerBound
  where
  sigma = R145.antiParallelDefect (P D) (Q D)
  mass = norm (a D) * norm (b D)
  angular = rp D * rq D * norm sigma
  radial = square (rp D - rq D)

  massNN : 0ℚ ≤ mass
  massNN = R96.productNonnegative
    (Separation.complex3NormSquaredNonnegative (a D))
    (Separation.complex3NormSquaredNonnegative (b D))

  sigmaNN : 0ℚ ≤ norm sigma
  sigmaNN = Separation.complex3NormSquaredNonnegative sigma

  radiusProductNN : 0ℚ ≤ rp D * rq D
  radiusProductNN = R96.productNonnegative (rpNN D) (rqNN D)

  angularNN : 0ℚ ≤ angular
  angularNN = R96.productNonnegative radiusProductNN sigmaNN

  radialNN : 0ℚ ≤ radial
  radialNN = Rational.squareNonnegative (rp D - rq D)

  rpSquareBelowProduct : square (rp D) ≤ rp D * rq D
  rpSquareBelowProduct =
    let instance rpNNI = nonNegative (rpNN D)
    in ℚP.*-monoˡ-≤-nonNeg (rp D) (rpBelowRq D)

  K = R145.slotKernel (P D) (Q D) (a D) (b D)
  angularOwner = R173.realScale (rp D) K
  radialBase = Cross.complex3Cross (a D)
    (Cross.complex3Cross (Q D) (b D))
  radialOwner = R173.realScale (rp D - rq D) radialBase

  kBound : norm K ≤ R174.twelve * (norm sigma * norm (a D) * norm (b D))
  kBound = R174.kernelNormBelowTwelveAngularProduct
    (P D) (Q D) (a D) (b D) (transverse D)

  kNN : 0ℚ ≤ norm K
  kNN = Separation.complex3NormSquaredNonnegative K

  kUpper = R174.twelve * (norm sigma * norm (a D) * norm (b D))

  oneNN : 0ℚ ≤ 1ℚ
  oneNN = Rational.squareNonnegative 1ℚ
  twoNN = Rational.addNonnegative oneNN oneNN
  fourNN = Rational.addNonnegative twoNN twoNN
  sixNN = Rational.addNonnegative fourNN twoNN
  twelveNN = Rational.addNonnegative sixNN sixNN
  sigmaMassNN = R96.productNonnegative sigmaNN massNN
  kUpperNN : 0ℚ ≤ kUpper
  kUpperNN = R96.productNonnegative twelveNN sigmaMassNN

  angularOwnerBound : norm angularOwner ≤ R174.twelve * angular * mass
  angularOwnerBound =
    let
      productBound = Rational.nonnegativeProductMonotone
        (Rational.squareNonnegative (rp D)) kNN
        radiusProductNN kUpperNN
        rpSquareBelowProduct kBound
      normalized :
        (rp D * rq D) * kUpper ≡ R174.twelve * angular * mass
      normalized = solve (rp D ∷ rq D ∷ norm sigma ∷ mass ∷ [])
    in
    subst (λ upper → norm angularOwner ≤ upper) normalized
      (subst
        (λ lower → lower ≤ (rp D * rq D) * kUpper)
        (sym (realScaleNorm (rp D) K)) productBound)

  radialOwnerBound : norm radialOwner ≤ radial * mass
  radialOwnerBound =
    let
      baseBound = nestedCrossQBound (a D) (Q D) (b D) (unitQ D)
      scaled =
        let instance radialNNI = nonNegative radialNN
        in ℚP.*-monoˡ-≤-nonNeg radial baseBound
    in
    subst (λ lower → lower ≤ radial * mass)
      (sym (realScaleNorm (rp D - rq D) radialBase)) scaled

  rawMeaning : rawKernel D ≡ C3.complex3Add angularOwner radialOwner
  rawMeaning = R172.rawDirectionalSlotKernelDualDefect
    (rp D) (rq D) (P D) (Q D) (a D) (b D)

  addBound :
    norm (C3.complex3Add angularOwner radialOwner)
    ≤ (1ℚ + 1ℚ) * norm angularOwner + (1ℚ + 1ℚ) * norm radialOwner
  addBound = R174.normAddBelowTwo angularOwner radialOwner

  scaledOwners :
    (1ℚ + 1ℚ) * norm angularOwner + (1ℚ + 1ℚ) * norm radialOwner
    ≤ (1ℚ + 1ℚ) * (R174.twelve * angular * mass)
      + (1ℚ + 1ℚ) * (radial * mass)
  scaledOwners =
    ℚP.+-mono-≤
      (let instance tNN = nonNegative twoNN
       in ℚP.*-monoˡ-≤-nonNeg (1ℚ + 1ℚ) angularOwnerBound)
      (let instance tNN = nonNegative twoNN
       in ℚP.*-monoˡ-≤-nonNeg (1ℚ + 1ℚ) radialOwnerBound)

  normalization :
    (1ℚ + 1ℚ) * (R174.twelve * angular * mass)
      + (1ℚ + 1ℚ) * (radial * mass)
    ≡ R175.twentyFour * angular * mass
      + (1ℚ + 1ℚ) * radial * mass
  normalization = solve (angular ∷ radial ∷ mass ∷ [])

  ownerBound :
    norm (rawKernel D)
    ≤ R175.twentyFour * angular * mass + (1ℚ + 1ℚ) * radial * mass
  ownerBound =
    subst
      (λ selected → norm selected ≤
        R175.twentyFour * angular * mass + (1ℚ + 1ℚ) * radial * mass)
      (sym rawMeaning)
      (ℚP.≤-trans addBound
        (subst
          (λ upper →
            (1ℚ + 1ℚ) * norm angularOwner
              + (1ℚ + 1ℚ) * norm radialOwner ≤ upper)
          normalization scaledOwners))

round176LeftAnchorPointwiseOutputBoundClosed : Bool
round176LeftAnchorPointwiseOutputBoundClosed = true

round176ContainsPostulate : Bool
round176ContainsPostulate = false

round176RightAnchorMirrorClosed : Bool
round176RightAnchorMirrorClosed = false

round176PackageAClosed : Bool
round176PackageAClosed = false

round176LeftAnchorPointwiseOutputBoundClosedIsTrue :
  round176LeftAnchorPointwiseOutputBoundClosed ≡ true
round176LeftAnchorPointwiseOutputBoundClosedIsTrue = refl

round176PackageAClosedIsFalse : round176PackageAClosed ≡ false
round176PackageAClosedIsFalse = refl
