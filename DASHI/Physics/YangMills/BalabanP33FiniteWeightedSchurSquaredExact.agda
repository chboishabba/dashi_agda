module DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Issai Schur,
-- classical matrix norm test (1911).  No DOI applies to the original result.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Lin Lin and Jianfeng Lu,
-- "Decay Estimates of Discretized Green's Functions for Schrödinger Type
-- Operators", Science China Mathematics 59 (2016), 1561--1578.
-- DOI: 10.1007/s11425-016-0311-4.
--
-- DASHI CONTRIBUTION
--
-- Prove the finite Schur test in the square-root-free form needed by the
-- constructive rational Combes--Thomas lane:
--
--   ||A v||_2^2 <= R C ||v||_2^2,
--
-- where every absolute row sum is at most R and every absolute column sum is
-- at most C.  The load-bearing weighted Cauchy step follows from the exact
-- identity
--
--   (sum w)(sum w x^2)
--     = (sum w x)^2 + sum_{i<j} w_i w_j (x_i-x_j)^2.
--
-- No square-root operation is used.  For a symmetric matrix, one row bound B
-- controls both orientations and gives ||A v||^2 <= B^2 ||v||^2.
--
-- The later tilted defect D H D^-1-H is not itself symmetric.  Its row and
-- column estimates must be derived separately from symmetry of H and the two
-- orientation bounds on the weight ratio; this module does not silently
-- identify those two matrices.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Literals
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini

------------------------------------------------------------------------
-- Generic finite ordered sums.
------------------------------------------------------------------------

sumPointwiseBelow :
  ∀ {Index : Set} (indices : List Index)
    (left right : Index → ℚ) →
  (∀ index → left index ≤ right index) →
  Sums.sumRational indices left ≤ Sums.sumRational indices right
sumPointwiseBelow [] left right pointwise = ℚP.≤-refl
sumPointwiseBelow (index ∷ indices) left right pointwise =
  ℚP.+-mono-≤
    (pointwise index)
    (sumPointwiseBelow indices left right pointwise)

sumNonnegative :
  ∀ {Index : Set} (indices : List Index) (term : Index → ℚ) →
  (∀ index → 0ℚ ≤ term index) →
  0ℚ ≤ Sums.sumRational indices term
sumNonnegative [] term termNonnegative = ℚP.≤-refl
sumNonnegative (index ∷ indices) term termNonnegative =
  let
    tailNonnegative : 0ℚ ≤ Sums.sumRational indices term
    tailNonnegative = sumNonnegative indices term termNonnegative
  in
  subst
    (λ lower → lower ≤ term index + Sums.sumRational indices term)
    (sym (ℚP.+-identityˡ 0ℚ))
    (ℚP.+-mono-≤ (termNonnegative index) tailNonnegative)

productNonnegative :
  ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right →
  0ℚ ≤ left * right
productNonnegative left right leftNonnegative rightNonnegative =
  let
    instance
      leftNN : NonNegative left
      leftNN = ℚ.nonNegative leftNonnegative
      rightNN : NonNegative right
      rightNN = ℚ.nonNegative rightNonnegative

      productNN : NonNegative (left * right)
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚP.nonNegative⁻¹ (left * right)

squareMonotoneNonnegative :
  ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → left ≤ right →
  FiniteL2.square left ≤ FiniteL2.square right
squareMonotoneNonnegative left right
    leftNonnegative rightNonnegative leftBelowRight =
  FiniteL2.nonnegativeProductMonotone
    leftNonnegative leftNonnegative
    rightNonnegative rightNonnegative
    leftBelowRight leftBelowRight

absoluteSquareExact : ∀ value →
  FiniteL2.square ∣ value ∣ ≡ FiniteL2.square value
absoluteSquareExact value =
  trans
    (sym (ℚP.∣p*q∣≡∣p∣*∣q∣ value value))
    (ℚP.0≤p⇒∣p∣≡p (FiniteL2.squareNonnegative value))

------------------------------------------------------------------------
-- Weighted finite Cauchy identity, without rational square roots.
------------------------------------------------------------------------

weightSum :
  ∀ {Index : Set} → List Index → (Index → ℚ) → ℚ
weightSum indices weight = Sums.sumRational indices weight

weightedValueSum :
  ∀ {Index : Set} →
  List Index → (Index → ℚ) → (Index → ℚ) → ℚ
weightedValueSum indices weight value =
  Sums.sumRational indices (λ index → weight index * value index)

weightedSquareSum :
  ∀ {Index : Set} →
  List Index → (Index → ℚ) → (Index → ℚ) → ℚ
weightedSquareSum indices weight value =
  Sums.sumRational indices
    (λ index → weight index * FiniteL2.square (value index))

weightedCross :
  ∀ {Index : Set} →
  ℚ → ℚ → List Index → (Index → ℚ) → (Index → ℚ) → ℚ
weightedCross headWeight headValue [] weight value = 0ℚ
weightedCross headWeight headValue (index ∷ indices) weight value =
  headWeight * weight index
    * FiniteL2.square (headValue - value index)
  + weightedCross headWeight headValue indices weight value

weightedGramDefect :
  ∀ {Index : Set} →
  List Index → (Index → ℚ) → (Index → ℚ) → ℚ
weightedGramDefect [] weight value = 0ℚ
weightedGramDefect (index ∷ indices) weight value =
  weightedCross (weight index) (value index) indices weight value
  + weightedGramDefect indices weight value

emptyWeightSum : ∀ {Index : Set} (weight : Index → ℚ) →
  weightSum [] weight ≡ 0ℚ
emptyWeightSum weight = refl

emptyWeightedValueSum : ∀ {Index : Set} (weight value : Index → ℚ) →
  weightedValueSum [] weight value ≡ 0ℚ
emptyWeightedValueSum weight value = refl

emptyWeightedSquareSum : ∀ {Index : Set} (weight value : Index → ℚ) →
  weightedSquareSum [] weight value ≡ 0ℚ
emptyWeightedSquareSum weight value = refl

zeroMinusZero : 0ℚ - 0ℚ ≡ 0ℚ
zeroMinusZero = ℚRing.solve-∀

squareUnfold : ∀ value → FiniteL2.square value ≡ value * value
squareUnfold value = refl

weightedCrossHeadExpansion : ∀ headWeight headValue weightValue value →
  headWeight * weightValue
    * ((headValue - value) * (headValue - value))
  ≡ headWeight
      * (headValue * headValue * weightValue
        + weightValue * (value * value)
        - ((+ 2 / 1) * headValue * (weightValue * value)))
weightedCrossHeadExpansion = ℚRing.solve-∀

weightedCrossStepAlgebra : ∀ headWeight headValue weightValue value
    tailWeight tailSquare tailValue →
  headWeight * weightValue
    * ((headValue - value) * (headValue - value))
    + headWeight
      * (headValue * headValue * tailWeight + tailSquare
        - ((+ 2 / 1) * headValue * tailValue))
  ≡ headWeight
      * (headValue * headValue * (weightValue + tailWeight)
        + (weightValue * (value * value) + tailSquare)
        - ((+ 2 / 1) * headValue * (weightValue * value + tailValue)))
weightedCrossStepAlgebra = ℚRing.solve-∀

consWeightSum : ∀ {Index : Set} (index : Index) (indices : List Index)
    (weight : Index → ℚ) →
  weightSum (index ∷ indices) weight ≡ weight index + weightSum indices weight
consWeightSum index indices weight = refl

consWeightedValueSum : ∀ {Index : Set} (index : Index) (indices : List Index)
    (weight value : Index → ℚ) →
  weightedValueSum (index ∷ indices) weight value
    ≡ weight index * value index + weightedValueSum indices weight value
consWeightedValueSum index indices weight value = refl

consWeightedSquareSum : ∀ {Index : Set} (index : Index) (indices : List Index)
    (weight value : Index → ℚ) →
  weightedSquareSum (index ∷ indices) weight value
    ≡ weight index * FiniteL2.square (value index)
      + weightedSquareSum indices weight value
consWeightedSquareSum index indices weight value = refl

weightedCrossExpansion :
  ∀ {Index : Set}
    (headWeight headValue : ℚ)
    (indices : List Index)
    (weight value : Index → ℚ) →
  weightedCross headWeight headValue indices weight value
  ≡ headWeight
      * (FiniteL2.square headValue * weightSum indices weight
        + weightedSquareSum indices weight value
        - ((+ 2 / 1) * headValue
          * weightedValueSum indices weight value))
weightedCrossExpansion headWeight headValue [] weight value
  rewrite emptyWeightSum weight
        | emptyWeightedSquareSum weight value
        | emptyWeightedValueSum weight value
        | ℚP.*-zeroʳ (FiniteL2.square headValue)
        | ℚP.*-zeroʳ ((+ 2 / 1) * headValue)
        | zeroMinusZero
        | ℚP.+-identityʳ 0ℚ
        | ℚP.*-zeroʳ headWeight = refl
weightedCrossExpansion
    headWeight headValue (index ∷ indices) weight value
  rewrite weightedCrossExpansion
    headWeight headValue indices weight value
        | consWeightSum index indices weight
        | consWeightedSquareSum index indices weight value
        | consWeightedValueSum index indices weight value
        | squareUnfold (headValue - value index)
        | squareUnfold headValue
        | squareUnfold (value index) =
  weightedCrossStepAlgebra
    headWeight headValue (weight index) (value index)
    (weightSum indices weight)
    (weightedSquareSum indices weight value)
    (weightedValueSum indices weight value)
weightedGramStepAlgebraic :
  ∀ headWeight headValue tailWeight tailValue tailSquare →
  (headWeight + tailWeight)
    * (headWeight * (headValue * headValue) + tailSquare)
  ≡ (headWeight * headValue + tailValue)
      * (headWeight * headValue + tailValue)
    + headWeight
      * ((headValue * headValue) * tailWeight
        + tailSquare
        - ((+ 2 / 1) * headValue * tailValue))
    + (tailWeight * tailSquare
      - tailValue * tailValue)
weightedGramStepAlgebraic = ℚRing.solve-∀

tailDefectAlgebra : ∀ square defect →
  (square + defect) - square ≡ defect
tailDefectAlgebra = ℚRing.solve-∀

weightedGramFinalAlgebra : ∀ square cross defect →
  square + cross + defect ≡ square + (cross + defect)
weightedGramFinalAlgebra = ℚRing.solve-∀

scaleAssoc : ∀ left right value →
  left * (right * value) ≡ left * right * value
scaleAssoc = ℚRing.solve-∀

weightedTailDefectExact :
  ∀ tailWeight tailValue tailSquare tailDefect →
  tailWeight * tailSquare
    ≡ FiniteL2.square tailValue + tailDefect →
  tailWeight * tailSquare - FiniteL2.square tailValue
    ≡ tailDefect
weightedTailDefectExact
    tailWeight tailValue tailSquare tailDefect identity
  rewrite squareUnfold tailValue =
  trans
    (cong (λ selected → selected - tailValue * tailValue) identity)
    (tailDefectAlgebra (tailValue * tailValue) tailDefect)

weightedGramIdentity :
  ∀ {Index : Set}
    (indices : List Index)
    (weight value : Index → ℚ) →
  weightSum indices weight * weightedSquareSum indices weight value
  ≡ FiniteL2.square (weightedValueSum indices weight value)
    + weightedGramDefect indices weight value
weightedGramIdentity [] weight value
  rewrite emptyWeightSum weight
        | emptyWeightedSquareSum weight value
        | emptyWeightedValueSum weight value
        | squareUnfold 0ℚ
        | ℚP.*-zeroʳ 0ℚ
        | ℚP.+-identityʳ 0ℚ = refl
weightedGramIdentity (index ∷ indices) weight value =
  let
    headWeight = weight index
    headValue = value index
    tailWeight = weightSum indices weight
    tailValue = weightedValueSum indices weight value
    tailSquare = weightedSquareSum indices weight value
    tailDefect = weightedGramDefect indices weight value

    expandedCross =
      headWeight
        * (FiniteL2.square headValue * tailWeight
          + tailSquare
          - ((+ 2 / 1) * headValue * tailValue))

    step :
      (headWeight + tailWeight)
        * (headWeight * FiniteL2.square headValue + tailSquare)
      ≡ FiniteL2.square (headWeight * headValue + tailValue)
        + expandedCross
        + (tailWeight * tailSquare - FiniteL2.square tailValue)
    step =
      weightedGramStepAlgebraic
        headWeight headValue tailWeight tailValue tailSquare

    tailExact :
      tailWeight * tailSquare - FiniteL2.square tailValue
      ≡ tailDefect
    tailExact =
      weightedTailDefectExact
        tailWeight tailValue tailSquare tailDefect
        (weightedGramIdentity indices weight value)

    afterTail :
      FiniteL2.square (headWeight * headValue + tailValue)
        + expandedCross
        + (tailWeight * tailSquare - FiniteL2.square tailValue)
      ≡ FiniteL2.square (headWeight * headValue + tailValue)
        + expandedCross + tailDefect
    afterTail =
      cong
        (λ selected →
          FiniteL2.square (headWeight * headValue + tailValue)
            + expandedCross + selected)
        tailExact

    crossExact :
      weightedCross headWeight headValue indices weight value
      ≡ expandedCross
    crossExact =
      weightedCrossExpansion
        headWeight headValue indices weight value

    afterCross :
      FiniteL2.square (headWeight * headValue + tailValue)
        + expandedCross + tailDefect
      ≡ FiniteL2.square (headWeight * headValue + tailValue)
        + weightedCross headWeight headValue indices weight value
        + tailDefect
    afterCross =
      cong
        (λ selected →
          FiniteL2.square (headWeight * headValue + tailValue)
            + selected + tailDefect)
        (sym crossExact)
  in
  trans step
    (trans afterTail
      (trans afterCross
        (trans
          (cong
            (λ selected →
              selected + weightedCross headWeight headValue indices weight value
                + tailDefect)
            (squareUnfold (headWeight * headValue + tailValue)))
          (weightedGramFinalAlgebra
            ((headWeight * headValue + tailValue)
              * (headWeight * headValue + tailValue))
            (weightedCross headWeight headValue indices weight value)
            tailDefect))))

weightedCrossNonnegative :
  ∀ {Index : Set}
    (headWeight headValue : ℚ)
    (indices : List Index)
    (weight value : Index → ℚ) →
  0ℚ ≤ headWeight →
  (∀ index → 0ℚ ≤ weight index) →
  0ℚ ≤ weightedCross headWeight headValue indices weight value
weightedCrossNonnegative
    headWeight headValue [] weight value
    headNonnegative weightsNonnegative = ℚP.≤-refl
weightedCrossNonnegative
    headWeight headValue (index ∷ indices) weight value
    headNonnegative weightsNonnegative =
  let
    headTimesWeightNonnegative :
      0ℚ ≤ headWeight * weight index
    headTimesWeightNonnegative =
      productNonnegative
        headWeight (weight index)
        headNonnegative (weightsNonnegative index)

    crossTermNonnegative :
      0ℚ ≤ headWeight * weight index
        * FiniteL2.square (headValue - value index)
    crossTermNonnegative =
      productNonnegative
        (headWeight * weight index)
        (FiniteL2.square (headValue - value index))
        headTimesWeightNonnegative
        (FiniteL2.squareNonnegative (headValue - value index))
  in
  subst
    (λ lower →
      lower ≤
        headWeight * weight index
          * FiniteL2.square (headValue - value index)
        + weightedCross headWeight headValue indices weight value)
    (sym (ℚP.+-identityˡ 0ℚ))
    (ℚP.+-mono-≤
      crossTermNonnegative
      (weightedCrossNonnegative
        headWeight headValue indices weight value
        headNonnegative weightsNonnegative))

weightedGramDefectNonnegative :
  ∀ {Index : Set}
    (indices : List Index)
    (weight value : Index → ℚ) →
  (∀ index → 0ℚ ≤ weight index) →
  0ℚ ≤ weightedGramDefect indices weight value
weightedGramDefectNonnegative [] weight value weightsNonnegative =
  ℚP.≤-refl
weightedGramDefectNonnegative
    (index ∷ indices) weight value weightsNonnegative =
  subst
    (λ lower → lower ≤ weightedGramDefect (index ∷ indices) weight value)
    (sym (ℚP.+-identityˡ 0ℚ))
    (ℚP.+-mono-≤
      (weightedCrossNonnegative
        (weight index) (value index)
        indices weight value
        (weightsNonnegative index)
        weightsNonnegative)
      (weightedGramDefectNonnegative
        indices weight value weightsNonnegative))

finiteWeightedCauchySquared :
  ∀ {Index : Set}
    (indices : List Index)
    (weight value : Index → ℚ) →
  (∀ index → 0ℚ ≤ weight index) →
  FiniteL2.square (weightedValueSum indices weight value)
  ≤ weightSum indices weight * weightedSquareSum indices weight value
finiteWeightedCauchySquared indices weight value weightsNonnegative =
  let
    addDefect :
      FiniteL2.square (weightedValueSum indices weight value)
      ≤ FiniteL2.square (weightedValueSum indices weight value)
        + weightedGramDefect indices weight value
    addDefect =
      subst
        (λ lower →
          lower ≤ FiniteL2.square (weightedValueSum indices weight value)
            + weightedGramDefect indices weight value)
        (ℚP.+-identityʳ
          (FiniteL2.square (weightedValueSum indices weight value)))
        (ℚP.+-monoʳ-≤
          (FiniteL2.square (weightedValueSum indices weight value))
          (weightedGramDefectNonnegative
            indices weight value weightsNonnegative))
  in
  subst
    (λ upper →
      FiniteL2.square (weightedValueSum indices weight value) ≤ upper)
    (sym (weightedGramIdentity indices weight value))
    addDefect

------------------------------------------------------------------------
-- Absolute finite matrix calculus.
------------------------------------------------------------------------

Matrix : Set → Set
Matrix Index = Index → Index → ℚ

Vector : Set → Set
Vector Index = Index → ℚ

matrixApply :
  ∀ {Index : Set} →
  List Index → Matrix Index → Vector Index → Vector Index
matrixApply indices matrix vector row =
  Sums.sumRational indices
    (λ column → matrix row column * vector column)

vectorNormSq :
  ∀ {Index : Set} →
  List Index → Vector Index → ℚ
vectorNormSq indices vector =
  Sums.sumRational indices
    (λ index → FiniteL2.square (vector index))

absoluteRowMass :
  ∀ {Index : Set} →
  List Index → Matrix Index → Index → ℚ
absoluteRowMass indices matrix row =
  Sums.sumRational indices (λ column → ∣ matrix row column ∣)

absoluteColumnMass :
  ∀ {Index : Set} →
  List Index → Matrix Index → Index → ℚ
absoluteColumnMass indices matrix column =
  Sums.sumRational indices (λ row → ∣ matrix row column ∣)

rowWeightedEnergy :
  ∀ {Index : Set} →
  List Index → Matrix Index → Vector Index → Index → ℚ
rowWeightedEnergy indices matrix vector row =
  Sums.sumRational indices
    (λ column →
      ∣ matrix row column ∣ * FiniteL2.square (vector column))

absoluteMajorantApply :
  ∀ {Index : Set} →
  List Index → Matrix Index → Vector Index → Index → ℚ
absoluteMajorantApply indices matrix vector row =
  Sums.sumRational indices
    (λ column → ∣ matrix row column ∣ * ∣ vector column ∣)

sumAbsoluteTriangle :
  ∀ {Index : Set}
    (indices : List Index) (term : Index → ℚ) →
  ∣ Sums.sumRational indices term ∣
  ≤ Sums.sumRational indices (λ index → ∣ term index ∣)
sumAbsoluteTriangle [] term = ℚP.≤-refl
sumAbsoluteTriangle (index ∷ indices) term =
  let
    headAbsoluteExact : ∣ term index ∣ ≤ ∣ term index ∣
    headAbsoluteExact = ℚP.≤-refl
  in
  ℚP.≤-trans
    (ℚP.∣p+q∣≤∣p∣+∣q∣
      (term index)
      (Sums.sumRational indices term))
    (ℚP.+-mono-≤
      headAbsoluteExact
      (sumAbsoluteTriangle indices term))

sumAbsoluteProductsExact :
  ∀ {Index : Set}
    (indices : List Index)
    (left right : Index → ℚ) →
  Sums.sumRational indices
    (λ index → ∣ left index * right index ∣)
  ≡ Sums.sumRational indices
    (λ index → ∣ left index ∣ * ∣ right index ∣)
sumAbsoluteProductsExact indices left right =
  Sums.sumRationalCong
    indices
    (λ index → ∣ left index * right index ∣)
    (λ index → ∣ left index ∣ * ∣ right index ∣)
    (λ index → ℚP.∣p*q∣≡∣p∣*∣q∣
      (left index) (right index))

matrixApplyAbsoluteBound :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Matrix Index)
    (vector : Vector Index)
    (row : Index) →
  ∣ matrixApply indices matrix vector row ∣
  ≤ absoluteMajorantApply indices matrix vector row
matrixApplyAbsoluteBound indices matrix vector row =
  subst
    (λ upper →
      ∣ matrixApply indices matrix vector row ∣ ≤ upper)
    (sumAbsoluteProductsExact indices (matrix row) vector)
    (sumAbsoluteTriangle
      indices
      (λ column → matrix row column * vector column))

absoluteMajorantNonnegative :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Matrix Index)
    (vector : Vector Index)
    (row : Index) →
  0ℚ ≤ absoluteMajorantApply indices matrix vector row
absoluteMajorantNonnegative indices matrix vector row =
  sumNonnegative
    indices
    (λ column → ∣ matrix row column ∣ * ∣ vector column ∣)
    (λ column →
      productNonnegative
        ∣ matrix row column ∣ ∣ vector column ∣
        (ℚP.0≤∣p∣ (matrix row column))
        (ℚP.0≤∣p∣ (vector column)))

weightedAbsoluteSquareSumExact :
  ∀ {Index : Set}
    (indices : List Index)
    (weight vector : Index → ℚ) →
  weightedSquareSum indices weight (λ index → ∣ vector index ∣)
  ≡ Sums.sumRational indices
      (λ index → weight index * FiniteL2.square (vector index))
weightedAbsoluteSquareSumExact indices weight vector =
  Sums.sumRationalCong
    indices
    (λ index → weight index * FiniteL2.square ∣ vector index ∣)
    (λ index → weight index * FiniteL2.square (vector index))
    (λ index → cong (weight index *_) (absoluteSquareExact (vector index)))

rowApplySquaredBound :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Matrix Index)
    (vector : Vector Index)
    (row : Index) →
  FiniteL2.square (matrixApply indices matrix vector row)
  ≤ absoluteRowMass indices matrix row
      * rowWeightedEnergy indices matrix vector row
rowApplySquaredBound indices matrix vector row =
  let
    absoluteSquared :
      FiniteL2.square ∣ matrixApply indices matrix vector row ∣
      ≤ FiniteL2.square
          (absoluteMajorantApply indices matrix vector row)
    absoluteSquared =
      squareMonotoneNonnegative
        ∣ matrixApply indices matrix vector row ∣
        (absoluteMajorantApply indices matrix vector row)
        (ℚP.0≤∣p∣ (matrixApply indices matrix vector row))
        (absoluteMajorantNonnegative indices matrix vector row)
        (matrixApplyAbsoluteBound indices matrix vector row)

    weightedCauchy :
      FiniteL2.square
        (absoluteMajorantApply indices matrix vector row)
      ≤ absoluteRowMass indices matrix row
          * weightedSquareSum
              indices
              (λ column → ∣ matrix row column ∣)
              (λ column → ∣ vector column ∣)
    weightedCauchy =
      finiteWeightedCauchySquared
        indices
        (λ column → ∣ matrix row column ∣)
        (λ column → ∣ vector column ∣)
        (λ column → ℚP.0≤∣p∣ (matrix row column))

    combined :
      FiniteL2.square ∣ matrixApply indices matrix vector row ∣
      ≤ absoluteRowMass indices matrix row
          * weightedSquareSum
              indices
              (λ column → ∣ matrix row column ∣)
              (λ column → ∣ vector column ∣)
    combined = ℚP.≤-trans absoluteSquared weightedCauchy
  in
  subst
    (λ lower →
      lower
      ≤ absoluteRowMass indices matrix row
          * rowWeightedEnergy indices matrix vector row)
    (absoluteSquareExact (matrixApply indices matrix vector row))
    (subst
      (λ upper →
        FiniteL2.square ∣ matrixApply indices matrix vector row ∣
        ≤ absoluteRowMass indices matrix row * upper)
      (weightedAbsoluteSquareSumExact
        indices
        (λ column → ∣ matrix row column ∣)
        vector)
      combined)

rowWeightedEnergyNonnegative :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Matrix Index)
    (vector : Vector Index)
    (row : Index) →
  0ℚ ≤ rowWeightedEnergy indices matrix vector row
rowWeightedEnergyNonnegative indices matrix vector row =
  sumNonnegative
    indices
    (λ column →
      ∣ matrix row column ∣ * FiniteL2.square (vector column))
    (λ column →
      productNonnegative
        ∣ matrix row column ∣
        (FiniteL2.square (vector column))
        (ℚP.0≤∣p∣ (matrix row column))
        (FiniteL2.squareNonnegative (vector column)))

sumRowsWeightedEnergyExact :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Matrix Index)
    (vector : Vector Index) →
  Sums.sumRational indices
    (rowWeightedEnergy indices matrix vector)
  ≡ Sums.sumRational indices
      (λ column →
        FiniteL2.square (vector column)
          * absoluteColumnMass indices matrix column)
sumRowsWeightedEnergyExact indices matrix vector =
  trans
    (Fubini.sumSwap
      indices indices
      (λ row column →
        ∣ matrix row column ∣ * FiniteL2.square (vector column)))
    (Sums.sumRationalCong
      indices
      (λ column →
        Sums.sumRational indices
          (λ row →
            ∣ matrix row column ∣
              * FiniteL2.square (vector column)))
      (λ column →
        FiniteL2.square (vector column)
          * absoluteColumnMass indices matrix column)
      (λ column →
        trans
          (Sums.sumRationalCong
            indices
            (λ row →
              ∣ matrix row column ∣
                * FiniteL2.square (vector column))
            (λ row →
              FiniteL2.square (vector column)
                * ∣ matrix row column ∣)
            (λ row → ℚP.*-comm
              ∣ matrix row column ∣
              (FiniteL2.square (vector column))))
          (Sums.sumRationalScale
            (FiniteL2.square (vector column))
            indices
            (λ row → ∣ matrix row column ∣))))

finiteSchurSquared :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Matrix Index)
    (vector : Vector Index)
    (rowBound columnBound : ℚ) →
  0ℚ ≤ rowBound →
  0ℚ ≤ columnBound →
  (∀ row → absoluteRowMass indices matrix row ≤ rowBound) →
  (∀ column → absoluteColumnMass indices matrix column ≤ columnBound) →
  vectorNormSq indices (matrixApply indices matrix vector)
  ≤ (rowBound * columnBound) * vectorNormSq indices vector
finiteSchurSquared
    indices matrix vector rowBound columnBound
    rowBoundNonnegative columnBoundNonnegative
    rowsBounded columnsBounded =
  let
    rowPointwise : ∀ row →
      FiniteL2.square (matrixApply indices matrix vector row)
      ≤ rowBound * rowWeightedEnergy indices matrix vector row
    rowPointwise row =
      ℚP.≤-trans
        (rowApplySquaredBound indices matrix vector row)
        (let
          instance
            energyNN : NonNegative
              (rowWeightedEnergy indices matrix vector row)
            energyNN = ℚ.nonNegative
              (rowWeightedEnergyNonnegative indices matrix vector row)
         in
         ℚP.*-monoʳ-≤-nonNeg
           (rowWeightedEnergy indices matrix vector row)
           (rowsBounded row))

    rowsSummed :
      vectorNormSq indices (matrixApply indices matrix vector)
      ≤ rowBound
          * Sums.sumRational indices
              (rowWeightedEnergy indices matrix vector)
    rowsSummed =
      subst
        (λ upper →
          vectorNormSq indices (matrixApply indices matrix vector)
          ≤ upper)
        (Sums.sumRationalScale
          rowBound indices
          (rowWeightedEnergy indices matrix vector))
        (sumPointwiseBelow
          indices
          (λ row →
            FiniteL2.square (matrixApply indices matrix vector row))
          (λ row →
            rowBound * rowWeightedEnergy indices matrix vector row)
          rowPointwise)

    columnPointwise : ∀ column →
      FiniteL2.square (vector column)
        * absoluteColumnMass indices matrix column
      ≤ FiniteL2.square (vector column) * columnBound
    columnPointwise column =
      let
        instance
          squareNN : NonNegative (FiniteL2.square (vector column))
          squareNN = ℚ.nonNegative
            (FiniteL2.squareNonnegative (vector column))
      in
      ℚP.*-monoˡ-≤-nonNeg
        (FiniteL2.square (vector column))
        (columnsBounded column)

    columnsSummed :
      Sums.sumRational indices
        (λ column →
          FiniteL2.square (vector column)
            * absoluteColumnMass indices matrix column)
      ≤ columnBound * vectorNormSq indices vector
    columnsSummed =
      subst
        (λ upper →
          Sums.sumRational indices
            (λ column →
              FiniteL2.square (vector column)
                * absoluteColumnMass indices matrix column)
          ≤ upper)
        (trans
          (Sums.sumRationalCong
            indices
            (λ column →
              FiniteL2.square (vector column) * columnBound)
            (λ column →
              columnBound * FiniteL2.square (vector column))
            (λ column → ℚP.*-comm
              (FiniteL2.square (vector column)) columnBound))
          (Sums.sumRationalScale
            columnBound indices
            (λ column → FiniteL2.square (vector column))))
        (sumPointwiseBelow
          indices
          (λ column →
            FiniteL2.square (vector column)
              * absoluteColumnMass indices matrix column)
          (λ column →
            FiniteL2.square (vector column) * columnBound)
          columnPointwise)

    energyBound :
      Sums.sumRational indices
        (rowWeightedEnergy indices matrix vector)
      ≤ columnBound * vectorNormSq indices vector
    energyBound =
      subst
        (λ lower → lower ≤ columnBound * vectorNormSq indices vector)
        (sym (sumRowsWeightedEnergyExact indices matrix vector))
        columnsSummed

    scaledEnergyBound :
      rowBound
        * Sums.sumRational indices
            (rowWeightedEnergy indices matrix vector)
      ≤ rowBound * (columnBound * vectorNormSq indices vector)
    scaledEnergyBound =
      let
        instance
          rowNN : NonNegative rowBound
          rowNN = ℚ.nonNegative rowBoundNonnegative
      in
      ℚP.*-monoˡ-≤-nonNeg rowBound energyBound

    combined :
      vectorNormSq indices (matrixApply indices matrix vector)
      ≤ rowBound * (columnBound * vectorNormSq indices vector)
    combined = ℚP.≤-trans rowsSummed scaledEnergyBound
  in
  subst
    (λ upper →
      vectorNormSq indices (matrixApply indices matrix vector)
      ≤ upper)
    (scaleAssoc
      rowBound columnBound (vectorNormSq indices vector))
    combined

------------------------------------------------------------------------
-- Symmetric specialization: one row bound controls both sides.
------------------------------------------------------------------------

Symmetric : ∀ {Index : Set} → Matrix Index → Set
Symmetric matrix = ∀ left right → matrix left right ≡ matrix right left

symmetricColumnMassEqualsRowMass :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Matrix Index) →
  Symmetric matrix →
  ∀ index →
  absoluteColumnMass indices matrix index
  ≡ absoluteRowMass indices matrix index
symmetricColumnMassEqualsRowMass indices matrix symmetry index =
  Sums.sumRationalCong
    indices
    (λ other → ∣ matrix other index ∣)
    (λ other → ∣ matrix index other ∣)
    (λ other → cong ∣_∣ (symmetry other index))

finiteSymmetricSchurSquared :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Matrix Index)
    (vector : Vector Index)
    (bound : ℚ) →
  0ℚ ≤ bound →
  Symmetric matrix →
  (∀ row → absoluteRowMass indices matrix row ≤ bound) →
  vectorNormSq indices (matrixApply indices matrix vector)
  ≤ (bound * bound) * vectorNormSq indices vector
finiteSymmetricSchurSquared
    indices matrix vector bound boundNonnegative symmetry rowsBounded =
  finiteSchurSquared
    indices matrix vector bound bound
    boundNonnegative boundNonnegative
    rowsBounded
    (λ column →
      subst
        (λ selected → selected ≤ bound)
        (sym (symmetricColumnMassEqualsRowMass
          indices matrix symmetry column))
        (rowsBounded column))

finiteWeightedCauchyLevel : ProofLevel
finiteWeightedCauchyLevel = machineChecked

finiteSchurSquaredLevel : ProofLevel
finiteSchurSquaredLevel = machineChecked

finiteSymmetricSchurSquaredLevel : ProofLevel
finiteSymmetricSchurSquaredLevel = machineChecked
