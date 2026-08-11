module DASHI.Physics.YangMills.BalabanFiniteScaledYoungDotExact where

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
-- Prove the square-root-free scaled Young inequality needed to turn a strict
-- finite normal floor into an explicit bound for the normal correction.  For
-- every finite rational carrier and scalar c,
--
--   2 c <y,x> <= c^2 ||x||^2 + ||y||^2,
--
-- because the difference is the finite sum of squares
--
--   sum_i (c x_i - y_i)^2.
--
-- No Cauchy--Schwarz theorem, square root, norm completion, or spectral
-- theorem is imported.  This is exact rational finite algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Perturb
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

pointwiseTwiceScaledDotUpper : ∀ scale left right →
  (+ 2 / 1) * scale * (left * right)
  ≤ (scale * scale) * (right * right) + left * left
pointwiseTwiceScaledDotUpper scale left right =
  let
    square = scale * right - left

    squareNonnegative : 0ℚ ≤ square * square
    squareNonnegative = FiniteL2.squareNonnegative square

    differenceExact :
      ((scale * scale) * (right * right) + left * left)
        - ((+ 2 / 1) * scale * (left * right))
      ≡ square * square
    differenceExact = ℚRing.solve-∀ scale left right

    differenceNonnegative :
      0ℚ ≤
        ((scale * scale) * (right * right) + left * left)
          - ((+ 2 / 1) * scale * (left * right))
    differenceNonnegative =
      subst (λ difference → 0ℚ ≤ difference)
        (sym differenceExact) squareNonnegative
  in
  Norm.nonnegativeDifferenceImpliesBelow differenceNonnegative

finiteTwiceScaledDotUpper :
  ∀ {Index}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    scale left right →
  (+ 2 / 1) * scale * Rect.finiteDot carrier left right
  ≤ (scale * scale) * Rect.finiteNormSq carrier right
      + Rect.finiteNormSq carrier left
finiteTwiceScaledDotUpper carrier scale left right =
  let
    values = Matrix.coordinates carrier

    pointwise = Perturb.sumMonotone values _ _
      (λ index → pointwiseTwiceScaledDotUpper
        scale (left index) (right index))

    leftScale :
      Sums.sumRational values
        (λ index → (+ 2 / 1) * scale * (left index * right index))
      ≡ (+ 2 / 1) * scale * Rect.finiteDot carrier left right
    leftScale =
      trans
        (Sums.sumRationalScale ((+ 2 / 1) * scale) values
          (λ index → left index * right index))
        (ℚRing.solve-∀ scale (Rect.finiteDot carrier left right))

    rightSplit :
      Sums.sumRational values
        (λ index →
          (scale * scale) * (right index * right index)
            + left index * left index)
      ≡ Sums.sumRational values
          (λ index → (scale * scale) * (right index * right index))
        + Rect.finiteNormSq carrier left
    rightSplit = Fubini.sumRationalAdd values
      (λ index → (scale * scale) * (right index * right index))
      (λ index → left index * left index)

    rightScale :
      Sums.sumRational values
        (λ index → (scale * scale) * (right index * right index))
      ≡ (scale * scale) * Rect.finiteNormSq carrier right
    rightScale = Sums.sumRationalScale (scale * scale) values
      (λ index → right index * right index)

    rightExact :
      Sums.sumRational values
        (λ index →
          (scale * scale) * (right index * right index)
            + left index * left index)
      ≡ (scale * scale) * Rect.finiteNormSq carrier right
          + Rect.finiteNormSq carrier left
    rightExact = trans rightSplit
      (cong (_+ Rect.finiteNormSq carrier left) rightScale)
  in
  subst
    (λ lower → lower ≤
      (scale * scale) * Rect.finiteNormSq carrier right
        + Rect.finiteNormSq carrier left)
    leftScale
    (subst
      (λ upper →
        Sums.sumRational values
          (λ index → (+ 2 / 1) * scale * (left index * right index))
        ≤ upper)
      rightExact pointwise)

coercivePairingImpliesScaledNorm :
  ∀ scale xNorm yNorm pairing →
  0ℚ ≤ scale →
  scale * xNorm ≤ pairing →
  (+ 2 / 1) * scale * pairing
    ≤ (scale * scale) * xNorm + yNorm →
  (scale * scale) * xNorm ≤ yNorm
coercivePairingImpliesScaledNorm scale xNorm yNorm pairing
    scaleNonnegative coercive young =
  let
    twoScaleNonnegative : 0ℚ ≤ (+ 2 / 1) * scale
    twoScaleNonnegative =
      Norm.scaleNonnegative (+ 2 / 1)
        (ℚP.nonNegative⁻¹ (+ 2 / 1)) scaleNonnegative

    doubledCoercive :
      ((+ 2 / 1) * scale) * (scale * xNorm)
      ≤ ((+ 2 / 1) * scale) * pairing
    doubledCoercive =
      Norm.scaleNonnegative ((+ 2 / 1) * scale)
        twoScaleNonnegative coercive

    doubledCoerciveExact :
      (+ 2 / 1) * ((scale * scale) * xNorm)
      ≤ (+ 2 / 1) * scale * pairing
    doubledCoerciveExact =
      subst
        (λ lower → lower ≤ (+ 2 / 1) * scale * pairing)
        (ℚRing.solve-∀ scale xNorm)
        (subst
          (λ upper →
            ((+ 2 / 1) * scale) * (scale * xNorm) ≤ upper)
          (ℚRing.solve-∀ scale pairing)
          doubledCoercive)

    combined :
      (+ 2 / 1) * ((scale * scale) * xNorm)
      ≤ (scale * scale) * xNorm + yNorm
    combined = ℚP.≤-trans doubledCoerciveExact young

    normalizedLeft :
      (+ 2 / 1) * ((scale * scale) * xNorm)
      ≡ (scale * scale) * xNorm + (scale * scale) * xNorm
    normalizedLeft = ℚRing.solve-∀ scale xNorm

    cancellable :
      (scale * scale) * xNorm + (scale * scale) * xNorm
      ≤ (scale * scale) * xNorm + yNorm
    cancellable = subst
      (λ lower → lower ≤ (scale * scale) * xNorm + yNorm)
      normalizedLeft combined
  in
  ℚP.+-cancelˡ-≤ ((scale * scale) * xNorm) cancellable

finiteScaledYoungDotLevel : ProofLevel
finiteScaledYoungDotLevel = machineChecked
