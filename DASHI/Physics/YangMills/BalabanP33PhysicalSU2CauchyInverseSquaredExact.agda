module DASHI.Physics.YangMills.BalabanP33PhysicalSU2CauchyInverseSquaredExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Augustin-Louis Cauchy, 1821 finite-sum inequality.
-- Hermann Amandus Schwarz, 1888 integral inequality.
-- No DOI applies to these classical results.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Apply the repository's exact finite rational Cauchy--Schwarz theorem to the
-- literal three-component side-four SU(2) coordinate list.  If
--
--   lambda ||x||^2 <= <x,y>
--
-- with lambda >= 0, then for nonzero x the finite ordered-field calculation
-- proves
--
--   lambda^2 ||x||^2 <= ||y||^2.
--
-- Taking x = H^{-1}y and lambda = 1/32 gives the squared inverse estimate
--
--   ||H^{-1}y||^2 <= 32^2 ||y||^2.
--
-- This route does not require an eigenbasis or a separately supplied spectral
-- decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (map)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; _/_; Positive; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

coordinatePairs :
  (Coordinates.PhysicalSU2Coordinate4 → ℚ) →
  (Coordinates.PhysicalSU2Coordinate4 → ℚ) →
  List FiniteL2.Pair
coordinatePairs left right =
  map (λ coordinate → left coordinate , right coordinate)
    Coordinates.physicalSU2Coordinates4

pairDotMapExact :
  ∀ {Index : Set} (indices : List Index)
    (left right : Index → ℚ) →
  FiniteL2.pairDot
    (map (λ index → left index , right index) indices)
  ≡ Sums.sumRational indices (λ index → left index * right index)
pairDotMapExact [] left right = refl
pairDotMapExact (index ∷ indices) left right
  rewrite pairDotMapExact indices left right = refl

leftNormMapExact :
  ∀ {Index : Set} (indices : List Index)
    (left right : Index → ℚ) →
  FiniteL2.leftNormSquared
    (map (λ index → left index , right index) indices)
  ≡ Sums.sumRational indices (λ index → left index * left index)
leftNormMapExact [] left right = refl
leftNormMapExact (index ∷ indices) left right
  rewrite leftNormMapExact indices left right = refl

rightNormMapExact :
  ∀ {Index : Set} (indices : List Index)
    (left right : Index → ℚ) →
  FiniteL2.rightNormSquared
    (map (λ index → left index , right index) indices)
  ≡ Sums.sumRational indices (λ index → right index * right index)
rightNormMapExact [] left right = refl
rightNormMapExact (index ∷ indices) left right
  rewrite rightNormMapExact indices left right = refl

physicalCoordinateCauchySchwarzSquared :
  ∀ left right →
  FiniteL2.square (Coordinates.physicalCoordinateDot left right)
  ≤ Coordinates.physicalSU2CoordinateNormSq left
      * Coordinates.physicalSU2CoordinateNormSq right
physicalCoordinateCauchySchwarzSquared left right =
  subst
    (λ dotValue →
      FiniteL2.square dotValue
      ≤ Coordinates.physicalSU2CoordinateNormSq left
          * Coordinates.physicalSU2CoordinateNormSq right)
    (pairDotMapExact
      Coordinates.physicalSU2Coordinates4 left right)
    (subst
      (λ leftNorm →
        FiniteL2.square
          (FiniteL2.pairDot (coordinatePairs left right))
        ≤ leftNorm * Coordinates.physicalSU2CoordinateNormSq right)
      (leftNormMapExact
        Coordinates.physicalSU2Coordinates4 left right)
      (subst
        (λ rightNorm →
          FiniteL2.square
            (FiniteL2.pairDot (coordinatePairs left right))
          ≤ FiniteL2.leftNormSquared (coordinatePairs left right)
              * rightNorm)
        (rightNormMapExact
          Coordinates.physicalSU2Coordinates4 left right)
        (FiniteL2.finiteCauchySchwarzSquared
          (coordinatePairs left right))))

productNonnegative : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
productNonnegative left right leftNonnegative rightNonnegative =
  let
    instance
      leftNN : NonNegative left
      leftNN = ℚ.nonNegative leftNonnegative
      rightNN : NonNegative right
      rightNN = ℚ.nonNegative rightNonnegative
  in
  ℚP.nonNegative⁻¹ (left * right)

squareMonotoneNonnegative : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → left ≤ right →
  left * left ≤ right * right
squareMonotoneNonnegative left right
    leftNonnegative rightNonnegative leftBelowRight =
  FiniteL2.nonnegativeProductMonotone
    leftNonnegative leftNonnegative
    rightNonnegative rightNonnegative
    leftBelowRight leftBelowRight

coercivityGivesPositiveInputInverseSquaredBound :
  ∀ lambda normXSq normYSq dotXY →
  0ℚ ≤ lambda →
  0ℚ < normXSq →
  0ℚ ≤ normYSq →
  lambda * normXSq ≤ dotXY →
  dotXY * dotXY ≤ normXSq * normYSq →
  (lambda * lambda) * normXSq ≤ normYSq
coercivityGivesPositiveInputInverseSquaredBound
    lambda normXSq normYSq dotXY
    lambdaNonnegative normXPositive normYNonnegative
    coercivity cauchy =
  let
    normXNonnegative : 0ℚ ≤ normXSq
    normXNonnegative = ℚP.<⇒≤ normXPositive

    lowerNonnegative : 0ℚ ≤ lambda * normXSq
    lowerNonnegative =
      productNonnegative lambda normXSq
        lambdaNonnegative normXNonnegative

    dotNonnegative : 0ℚ ≤ dotXY
    dotNonnegative = ℚP.≤-trans lowerNonnegative coercivity

    squaredCoercivity :
      (lambda * normXSq) * (lambda * normXSq)
      ≤ dotXY * dotXY
    squaredCoercivity =
      squareMonotoneNonnegative
        (lambda * normXSq) dotXY
        lowerNonnegative dotNonnegative coercivity

    uncancelled :
      normXSq * ((lambda * lambda) * normXSq)
      ≤ normXSq * normYSq
    uncancelled =
      subst
        (λ lower → lower ≤ normXSq * normYSq)
        (ℚRing.solve-∀ lambda normXSq)
        (ℚP.≤-trans squaredCoercivity cauchy)

    instance
      normXPositiveInstance : Positive normXSq
      normXPositiveInstance = ℚ.positive normXPositive
  in
  ℚP.*-cancelˡ-≤-pos normXSq uncancelled

coercivityGivesZeroInputInverseSquaredBound :
  ∀ lambda normXSq normYSq →
  normXSq ≡ 0ℚ →
  0ℚ ≤ normYSq →
  (lambda * lambda) * normXSq ≤ normYSq
coercivityGivesZeroInputInverseSquaredBound
    lambda .0ℚ normYSq refl normYNonnegative =
  subst
    (λ lower → lower ≤ normYSq)
    (ℚRing.solve-∀ lambda)
    normYNonnegative

physicalInverseSquaredBoundForPositivePreimage :
  ∀ matrix inverse lambda vector →
  (∀ coordinate →
    Coordinates.physicalMatrixApply matrix
      (Coordinates.physicalMatrixApply inverse vector) coordinate
    ≡ vector coordinate) →
  0ℚ ≤ lambda →
  0ℚ < Coordinates.physicalSU2CoordinateNormSq
    (Coordinates.physicalMatrixApply inverse vector) →
  lambda
    * Coordinates.physicalSU2CoordinateNormSq
        (Coordinates.physicalMatrixApply inverse vector)
  ≤ Coordinates.physicalCoordinateDot
      (Coordinates.physicalMatrixApply inverse vector)
      (Coordinates.physicalMatrixApply matrix
        (Coordinates.physicalMatrixApply inverse vector)) →
  (lambda * lambda)
    * Coordinates.physicalSU2CoordinateNormSq
        (Coordinates.physicalMatrixApply inverse vector)
  ≤ Coordinates.physicalSU2CoordinateNormSq vector
physicalInverseSquaredBoundForPositivePreimage
    matrix inverse lambda vector inverseRight
    lambdaNonnegative inverseVectorPositive coercivity =
  coercivityGivesPositiveInputInverseSquaredBound
    lambda
    (Coordinates.physicalSU2CoordinateNormSq
      (Coordinates.physicalMatrixApply inverse vector))
    (Coordinates.physicalSU2CoordinateNormSq vector)
    (Coordinates.physicalCoordinateDot
      (Coordinates.physicalMatrixApply inverse vector) vector)
    lambdaNonnegative
    inverseVectorPositive
    (let pairs = coordinatePairs vector vector
     in subst
          (λ selected → 0ℚ ≤ selected)
          (rightNormMapExact
            Coordinates.physicalSU2Coordinates4 vector vector)
          (FiniteL2.rightNormSquaredNonnegative pairs))
    (subst
      (λ right →
        lambda
          * Coordinates.physicalSU2CoordinateNormSq
              (Coordinates.physicalMatrixApply inverse vector)
        ≤ right)
      (Sums.sumRationalCong
        Coordinates.physicalSU2Coordinates4
        (λ coordinate →
          Coordinates.physicalMatrixApply inverse vector coordinate
          * Coordinates.physicalMatrixApply matrix
              (Coordinates.physicalMatrixApply inverse vector) coordinate)
        (λ coordinate →
          Coordinates.physicalMatrixApply inverse vector coordinate
          * vector coordinate)
        (λ coordinate →
          cong
            (Coordinates.physicalMatrixApply inverse vector coordinate *_)
            (inverseRight coordinate)))
      coercivity)
    (physicalCoordinateCauchySchwarzSquared
      (Coordinates.physicalMatrixApply inverse vector) vector)

thirtyTwoSquared : ℚ
thirtyTwoSquared = + 1024 / 1

thirtyTwoSquaredNonnegative : 0ℚ ≤ thirtyTwoSquared
thirtyTwoSquaredNonnegative = ℚP.nonNegative⁻¹ thirtyTwoSquared

p33SquaredRescalingExact : ∀ normSq →
  thirtyTwoSquared
    * ((P33.p33PhysicalFloor * P33.p33PhysicalFloor) * normSq)
  ≡ normSq
p33SquaredRescalingExact = ℚRing.solve-∀

rescaleP33SquaredInverseBound : ∀ inverseNormSq vectorNormSq →
  (P33.p33PhysicalFloor * P33.p33PhysicalFloor) * inverseNormSq
    ≤ vectorNormSq →
  inverseNormSq ≤ thirtyTwoSquared * vectorNormSq
rescaleP33SquaredInverseBound inverseNormSq vectorNormSq bound =
  let
    instance
      scaleNN : NonNegative thirtyTwoSquared
      scaleNN = ℚ.nonNegative thirtyTwoSquaredNonnegative

    scaled :
      thirtyTwoSquared
        * ((P33.p33PhysicalFloor * P33.p33PhysicalFloor) * inverseNormSq)
      ≤ thirtyTwoSquared * vectorNormSq
    scaled = ℚP.*-monoˡ-≤-nonNeg thirtyTwoSquared bound
  in
  subst
    (λ lower → lower ≤ thirtyTwoSquared * vectorNormSq)
    (p33SquaredRescalingExact inverseNormSq)
    scaled

p33PhysicalInverseSquaredBoundForPositivePreimage :
  ∀ matrix inverse vector →
  (∀ coordinate →
    Coordinates.physicalMatrixApply matrix
      (Coordinates.physicalMatrixApply inverse vector) coordinate
    ≡ vector coordinate) →
  0ℚ < Coordinates.physicalSU2CoordinateNormSq
    (Coordinates.physicalMatrixApply inverse vector) →
  P33.p33PhysicalFloor
    * Coordinates.physicalSU2CoordinateNormSq
        (Coordinates.physicalMatrixApply inverse vector)
  ≤ Coordinates.physicalCoordinateDot
      (Coordinates.physicalMatrixApply inverse vector)
      (Coordinates.physicalMatrixApply matrix
        (Coordinates.physicalMatrixApply inverse vector)) →
  Coordinates.physicalSU2CoordinateNormSq
      (Coordinates.physicalMatrixApply inverse vector)
  ≤ thirtyTwoSquared
      * Coordinates.physicalSU2CoordinateNormSq vector
p33PhysicalInverseSquaredBoundForPositivePreimage
    matrix inverse vector inverseRight inverseVectorPositive coercivity =
  rescaleP33SquaredInverseBound
    (Coordinates.physicalSU2CoordinateNormSq
      (Coordinates.physicalMatrixApply inverse vector))
    (Coordinates.physicalSU2CoordinateNormSq vector)
    (physicalInverseSquaredBoundForPositivePreimage
      matrix inverse P33.p33PhysicalFloor vector
      inverseRight
      (ℚP.nonNegative⁻¹ P33.p33PhysicalFloor)
      inverseVectorPositive
      coercivity)

physicalSU2FiniteCauchySchwarzLevel : ProofLevel
physicalSU2FiniteCauchySchwarzLevel = machineChecked

physicalSU2DirectInverseSquaredLevel : ProofLevel
physicalSU2DirectInverseSquaredLevel = machineChecked

physicalSU2P33InverseFactor32SquaredLevel : ProofLevel
physicalSU2P33InverseFactor32SquaredLevel = machineChecked
