module DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact finite perturbative lower-bound algebra needed to transport
-- the flat multiplier floor to a nearby physical background.  For vectors
-- r,d on any literal finite rational carrier,
--
--   1/2 ||r||^2 - ||d||^2 <= ||r+d||^2.
--
-- Hence, if c ||lambda||^2 <= ||r||^2 and
-- ||d||^2 <= epsilon ||lambda||^2, then
--
--   (c/2-epsilon) ||lambda||^2 <= ||r+d||^2.
--
-- No spectral continuity, rank constancy, square roots, or operator-norm
-- black box is used.  The proof is a pointwise rational square identity plus
-- a literal finite sum.  A physical caller must still identify r with the
-- flat adjoint, d with the covariant-adjoint defect, and prove its epsilon.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

oneHalf : ℚ
oneHalf = + 1 / 2

pointwiseHalfMinusDefectLower : ∀ reference defect →
  oneHalf * (reference * reference) - defect * defect
  ≤ (reference + defect) * (reference + defect)
pointwiseHalfMinusDefectLower reference defect =
  let
    square : ℚ
    square = reference + (+ 2 / 1) * defect

    nonnegative : 0ℚ ≤ square * square
    nonnegative = FiniteL2.squareNonnegative square

    scaled :
      0ℚ ≤ oneHalf * (square * square)
    scaled =
      Norm.scaleNonnegative oneHalf
        (ℚP.nonNegative⁻¹ oneHalf) nonnegative

    differenceExact :
      (reference + defect) * (reference + defect)
        - (oneHalf * (reference * reference) - defect * defect)
      ≡ oneHalf * (square * square)
    differenceExact = ℚRing.solve-∀ reference defect

    differenceNonnegative :
      0ℚ ≤
        (reference + defect) * (reference + defect)
          - (oneHalf * (reference * reference) - defect * defect)
    differenceNonnegative =
      subst (λ difference → 0ℚ ≤ difference)
        (sym differenceExact) scaled
  in
  Norm.nonnegativeDifferenceImpliesBelow differenceNonnegative

sumMonotone : ∀ {Index : Set} (values : List Index) left right →
  (∀ index → left index ≤ right index) →
  Sums.sumRational values left ≤ Sums.sumRational values right
sumMonotone [] left right pointwise = ℚP.≤-refl
sumMonotone (index ∷ values) left right pointwise =
  ℚP.+-mono-≤
    (pointwise index)
    (sumMonotone values left right pointwise)

sumSubtract : ∀ {Index : Set} (values : List Index) left right →
  Sums.sumRational values (λ index → left index - right index)
  ≡ Sums.sumRational values left - Sums.sumRational values right
sumSubtract [] left right = ℚRing.solve []
sumSubtract (index ∷ values) left right
  rewrite sumSubtract values left right =
  ℚRing.solve-∀
    (left index) (right index)
    (Sums.sumRational values left)
    (Sums.sumRational values right)

finiteVectorHalfMinusDefectLower :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    reference defect →
  oneHalf * Rect.finiteNormSq carrier reference
    - Rect.finiteNormSq carrier defect
  ≤ Rect.finiteNormSq carrier (Rect.vectorAdd reference defect)
finiteVectorHalfMinusDefectLower carrier reference defect =
  let
    values = Matrix.coordinates carrier

    pointwiseLower :
      Sums.sumRational values
        (λ index →
          oneHalf * (reference index * reference index)
            - defect index * defect index)
      ≤ Sums.sumRational values
        (λ index →
          (reference index + defect index)
            * (reference index + defect index))
    pointwiseLower =
      sumMonotone values _ _
        (λ index →
          pointwiseHalfMinusDefectLower
            (reference index) (defect index))

    leftExact :
      Sums.sumRational values
        (λ index →
          oneHalf * (reference index * reference index)
            - defect index * defect index)
      ≡ oneHalf * Rect.finiteNormSq carrier reference
          - Rect.finiteNormSq carrier defect
    leftExact =
      trans
        (sumSubtract values
          (λ index → oneHalf * (reference index * reference index))
          (λ index → defect index * defect index))
        (cong
          (λ selected → selected - Rect.finiteNormSq carrier defect)
          (Sums.sumRationalScale oneHalf values
            (λ index → reference index * reference index)))
  in
  subst
    (λ lower →
      lower ≤ Rect.finiteNormSq carrier (Rect.vectorAdd reference defect))
    leftExact
    pointwiseLower

record ReducedFloorPerturbationData {Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index) : Set₁ where
  field
    Multiplier : Set
    multiplierNormSq : Multiplier → ℚ

    reference : Multiplier → Rect.RationalVector Index
    defect : Multiplier → Rect.RationalVector Index
    full : Multiplier → Rect.RationalVector Index

    referenceFloor defectCoefficient : ℚ

    fullSplits : ∀ multiplier index →
      full multiplier index
      ≡ reference multiplier index + defect multiplier index

    referenceCoercive : ∀ multiplier →
      referenceFloor * multiplierNormSq multiplier
      ≤ Rect.finiteNormSq carrier (reference multiplier)

    defectUpper : ∀ multiplier →
      Rect.finiteNormSq carrier (defect multiplier)
      ≤ defectCoefficient * multiplierNormSq multiplier
open ReducedFloorPerturbationData public

perturbedReducedFloor :
  ∀ {Index} {carrier : Matrix.FiniteRationalCoordinates Index}
    (dataSet : ReducedFloorPerturbationData carrier) multiplier →
  (oneHalf * referenceFloor dataSet - defectCoefficient dataSet)
    * multiplierNormSq dataSet multiplier
  ≤ Rect.finiteNormSq carrier (full dataSet multiplier)
perturbedReducedFloor {carrier = carrier} dataSet multiplier =
  let
    ref = reference dataSet multiplier
    def = defect dataSet multiplier
    norm = multiplierNormSq dataSet multiplier

    base = finiteVectorHalfMinusDefectLower carrier ref def

    refLower :
      oneHalf * (referenceFloor dataSet * norm)
      ≤ oneHalf * Rect.finiteNormSq carrier ref
    refLower =
      Norm.scaleNonnegative oneHalf
        (ℚP.nonNegative⁻¹ oneHalf)
        (referenceCoercive dataSet multiplier)

    defectUpperBound = defectUpper dataSet multiplier

    combined :
      oneHalf * (referenceFloor dataSet * norm)
        - defectCoefficient dataSet * norm
      ≤ oneHalf * Rect.finiteNormSq carrier ref
        - Rect.finiteNormSq carrier def
    combined = ℚP.+-mono-≤
      refLower
      (ℚP.neg-antimono-≤ defectUpperBound)

    coefficientExact :
      (oneHalf * referenceFloor dataSet - defectCoefficient dataSet) * norm
      ≡ oneHalf * (referenceFloor dataSet * norm)
        - defectCoefficient dataSet * norm
    coefficientExact =
      ℚRing.solve-∀
        (referenceFloor dataSet) (defectCoefficient dataSet) norm

    fullExact :
      Rect.finiteNormSq carrier (full dataSet multiplier)
      ≡ Rect.finiteNormSq carrier (Rect.vectorAdd ref def)
    fullExact =
      Sums.sumRationalCong
        (Matrix.coordinates carrier)
        (λ index → full dataSet multiplier index * full dataSet multiplier index)
        (λ index →
          (ref index + def index) * (ref index + def index))
        (λ index →
          cong₂ _*_
            (fullSplits dataSet multiplier index)
            (fullSplits dataSet multiplier index))
  in
  subst
    (λ lower → lower ≤ Rect.finiteNormSq carrier (full dataSet multiplier))
    coefficientExact
    (ℚP.≤-trans combined
      (ℚP.≤-trans base
        (subst
          (λ upper →
            Rect.finiteNormSq carrier (Rect.vectorAdd ref def) ≤ upper)
          (sym fullExact)
          ℚP.≤-refl)))

finiteReducedFloorPerturbationLevel : ProofLevel
finiteReducedFloorPerturbationLevel = machineChecked

physicalReducedFloorPerturbationProducerLevel : ProofLevel
physicalReducedFloorPerturbationProducerLevel = conditional
