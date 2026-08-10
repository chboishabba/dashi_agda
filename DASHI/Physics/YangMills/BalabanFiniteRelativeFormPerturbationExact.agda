module DASHI.Physics.YangMills.BalabanFiniteRelativeFormPerturbationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Exact square-root-free relative-form algebra on an arbitrary finite
-- rational carrier.  For finite vectors r,d,
--
--   Delta(r,d) = ||r+d||^2 - ||r||^2,
--
-- the pointwise square identities at epsilon = 1/4 give
--
--  -(1/4 ||r||^2 + 5 ||d||^2)
--      <= Delta(r,d)
--      <= 1/4 ||r||^2 + 5 ||d||^2.
--
-- The lower inequality actually has four defect squares available; five is
-- used symmetrically so callers get one common envelope.  Everything below is
-- a literal rational square identity plus a finite sum: no spectral theorem,
-- square root, operator norm, or function extensionality is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
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
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Previous

oneQuarter five two four : ℚ
oneQuarter = + 1 / 4
five = + 5 / 1
two = + 2 / 1
four = + 4 / 1

pointwiseQuarterFiveUpper : ∀ reference defect →
  (reference + defect) * (reference + defect) - reference * reference
  ≤ oneQuarter * (reference * reference) + five * (defect * defect)
pointwiseQuarterFiveUpper reference defect =
  let
    square = reference - four * defect

    scaledSquare : 0ℚ ≤ oneQuarter * (square * square)
    scaledSquare =
      Norm.scaleNonnegative oneQuarter
        (ℚP.nonNegative⁻¹ oneQuarter)
        (FiniteL2.squareNonnegative square)

    differenceExact :
      (oneQuarter * (reference * reference) + five * (defect * defect))
        - ((reference + defect) * (reference + defect) - reference * reference)
      ≡ oneQuarter * (square * square)
    differenceExact = ℚRing.solve-∀ reference defect
  in
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ difference → 0ℚ ≤ difference)
      (sym differenceExact)
      scaledSquare)

pointwiseQuarterFiveLower : ∀ reference defect →
  - (oneQuarter * (reference * reference) + five * (defect * defect))
  ≤ (reference + defect) * (reference + defect) - reference * reference
pointwiseQuarterFiveLower reference defect =
  let
    square = reference + four * defect

    first : 0ℚ ≤ oneQuarter * (square * square)
    first =
      Norm.scaleNonnegative oneQuarter
        (ℚP.nonNegative⁻¹ oneQuarter)
        (FiniteL2.squareNonnegative square)

    second : 0ℚ ≤ two * (defect * defect)
    second =
      Norm.scaleNonnegative two
        (ℚP.nonNegative⁻¹ two)
        (FiniteL2.squareNonnegative defect)

    combined :
      0ℚ ≤ oneQuarter * (square * square) + two * (defect * defect)
    combined = FiniteL2.addNonnegative first second

    differenceExact :
      ((reference + defect) * (reference + defect) - reference * reference)
        - (- (oneQuarter * (reference * reference) + five * (defect * defect)))
      ≡ oneQuarter * (square * square) + two * (defect * defect)
    differenceExact = ℚRing.solve-∀ reference defect
  in
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ difference → 0ℚ ≤ difference)
      (sym differenceExact)
      combined)

sumAddExact : ∀ {Index : Set} (values : List Index) left right →
  Sums.sumRational values (λ value → left value + right value)
  ≡ Sums.sumRational values left + Sums.sumRational values right
sumAddExact [] left right = ℚRing.solve []
sumAddExact (value ∷ values) left right
  rewrite sumAddExact values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (Sums.sumRational values left)
    (Sums.sumRational values right)

finiteVectorQuarterFiveDifferenceUpper :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    reference defect →
  Rect.finiteNormSq carrier (Rect.vectorAdd reference defect)
    - Rect.finiteNormSq carrier reference
  ≤ oneQuarter * Rect.finiteNormSq carrier reference
    + five * Rect.finiteNormSq carrier defect
finiteVectorQuarterFiveDifferenceUpper carrier reference defect =
  let
    values = Matrix.coordinates carrier

    pointwise :
      Sums.sumRational values
        (λ index →
          (reference index + defect index) * (reference index + defect index)
            - reference index * reference index)
      ≤ Sums.sumRational values
        (λ index →
          oneQuarter * (reference index * reference index)
            + five * (defect index * defect index))
    pointwise =
      Previous.sumMonotone values _ _
        (λ index →
          pointwiseQuarterFiveUpper (reference index) (defect index))

    leftExact :
      Sums.sumRational values
        (λ index →
          (reference index + defect index) * (reference index + defect index)
            - reference index * reference index)
      ≡ Rect.finiteNormSq carrier (Rect.vectorAdd reference defect)
          - Rect.finiteNormSq carrier reference
    leftExact =
      Previous.sumSubtract values
        (λ index →
          (reference index + defect index) * (reference index + defect index))
        (λ index → reference index * reference index)

    rightExact :
      Sums.sumRational values
        (λ index →
          oneQuarter * (reference index * reference index)
            + five * (defect index * defect index))
      ≡ oneQuarter * Rect.finiteNormSq carrier reference
          + five * Rect.finiteNormSq carrier defect
    rightExact =
      trans
        (sumAddExact values
          (λ index → oneQuarter * (reference index * reference index))
          (λ index → five * (defect index * defect index)))
        (cong₂ _+_
          (Sums.sumRationalScale oneQuarter values
            (λ index → reference index * reference index))
          (Sums.sumRationalScale five values
            (λ index → defect index * defect index)))
  in
  subst
    (λ lower →
      lower
      ≤ oneQuarter * Rect.finiteNormSq carrier reference
        + five * Rect.finiteNormSq carrier defect)
    leftExact
    (subst
      (λ upper →
        Sums.sumRational values
          (λ index →
            (reference index + defect index) * (reference index + defect index)
              - reference index * reference index)
        ≤ upper)
      rightExact pointwise)

finiteVectorQuarterFiveDifferenceLower :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    reference defect →
  - (oneQuarter * Rect.finiteNormSq carrier reference
      + five * Rect.finiteNormSq carrier defect)
  ≤ Rect.finiteNormSq carrier (Rect.vectorAdd reference defect)
      - Rect.finiteNormSq carrier reference
finiteVectorQuarterFiveDifferenceLower carrier reference defect =
  let
    values = Matrix.coordinates carrier

    pointwise :
      Sums.sumRational values
        (λ index →
          - (oneQuarter * (reference index * reference index)
            + five * (defect index * defect index)))
      ≤ Sums.sumRational values
        (λ index →
          (reference index + defect index) * (reference index + defect index)
            - reference index * reference index)
    pointwise =
      Previous.sumMonotone values _ _
        (λ index →
          pointwiseQuarterFiveLower (reference index) (defect index))

    leftInsideExact :
      Sums.sumRational values
        (λ index →
          oneQuarter * (reference index * reference index)
            + five * (defect index * defect index))
      ≡ oneQuarter * Rect.finiteNormSq carrier reference
          + five * Rect.finiteNormSq carrier defect
    leftInsideExact =
      trans
        (sumAddExact values
          (λ index → oneQuarter * (reference index * reference index))
          (λ index → five * (defect index * defect index)))
        (cong₂ _+_
          (Sums.sumRationalScale oneQuarter values
            (λ index → reference index * reference index))
          (Sums.sumRationalScale five values
            (λ index → defect index * defect index)))

    leftExact :
      Sums.sumRational values
        (λ index →
          - (oneQuarter * (reference index * reference index)
            + five * (defect index * defect index)))
      ≡ - (oneQuarter * Rect.finiteNormSq carrier reference
          + five * Rect.finiteNormSq carrier defect)
    leftExact =
      trans
        (Sums.sumRationalNegate values
          (λ index →
            oneQuarter * (reference index * reference index)
              + five * (defect index * defect index)))
        (cong -_ leftInsideExact)

    rightExact :
      Sums.sumRational values
        (λ index →
          (reference index + defect index) * (reference index + defect index)
            - reference index * reference index)
      ≡ Rect.finiteNormSq carrier (Rect.vectorAdd reference defect)
          - Rect.finiteNormSq carrier reference
    rightExact =
      Previous.sumSubtract values
        (λ index →
          (reference index + defect index) * (reference index + defect index))
        (λ index → reference index * reference index)
  in
  subst
    (λ lower →
      lower
      ≤ Rect.finiteNormSq carrier (Rect.vectorAdd reference defect)
          - Rect.finiteNormSq carrier reference)
    leftExact
    (subst
      (λ upper →
        Sums.sumRational values
          (λ index →
            - (oneQuarter * (reference index * reference index)
              + five * (defect index * defect index)))
        ≤ upper)
      rightExact pointwise)

finiteRelativeFormQuarterFiveLevel : ProofLevel
finiteRelativeFormQuarterFiveLevel = machineChecked
