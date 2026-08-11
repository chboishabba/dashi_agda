module DASHI.Physics.YangMills.BalabanP33QuaternionScaledYoungLowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Give the square-root-free scalar estimate needed by the grouped deep Wilson
-- remainder.  If
--
--   N(q) <= (s l)(s r),     s,l,r >= 0,
--
-- then exact rational AM--GM and order reflection prove both
--
--   -s(l+r)/2 <= -q0(q) <= s(l+r)/2.
--
-- No square root, absolute-value elimination axiom, or analytic norm receipt
-- is introduced.  The lower bound is obtained by applying the same checked
-- upper theorem to -q and transporting the sign exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionAtomNormExact as Atom
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionScalarBudgetExact as Strong
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope

scaledYoungBudget : ℚ → ℚ → ℚ → ℚ
scaledYoungBudget scale left right =
  scale * ((+ 1 / 2) * (left + right))

scaledAverageExact : ∀ scale left right →
  Strong.average (scale * left) (scale * right)
  ≡ scaledYoungBudget scale left right
scaledAverageExact scale left right =
  ℚRing.solve-∀ scale left right

scaledYoungBudgetNonnegative :
  ∀ scale left right →
  0ℚ ≤ scale → 0ℚ ≤ left → 0ℚ ≤ right →
  0ℚ ≤ scaledYoungBudget scale left right
scaledYoungBudgetNonnegative scale left right scaleNN leftNN rightNN =
  subst
    (λ selected → 0ℚ ≤ selected)
    (scaledAverageExact scale left right)
    (Strong.averageNonnegative
      (scale * left) (scale * right)
      (Strong.multiplyNonnegative scale left scaleNN leftNN)
      (Strong.multiplyNonnegative scale right scaleNN rightNN))

scaledYoungUpperFromNorm :
  ∀ value scale left right →
  0ℚ ≤ scale → 0ℚ ≤ left → 0ℚ ≤ right →
  Norm.normSq value ≤ (scale * left) * (scale * right) →
  Telescope.wilsonScalar value
  ≤ scaledYoungBudget scale left right
scaledYoungUpperFromNorm
    value scale left right scaleNN leftNN rightNN normUpper =
  let
    scalarSquareToNorm :
      Strong.negativeScalar value * Strong.negativeScalar value
      ≤ Norm.normSq value
    scalarSquareToNorm = Strong.negativeScalarSquareBelowNormSq value

    scalarSquareToProduct :
      Strong.negativeScalar value * Strong.negativeScalar value
      ≤ (scale * left) * (scale * right)
    scalarSquareToProduct = ℚP.≤-trans scalarSquareToNorm normUpper

    productToAverageSquare :
      (scale * left) * (scale * right)
      ≤ Strong.average (scale * left) (scale * right)
          * Strong.average (scale * left) (scale * right)
    productToAverageSquare =
      Strong.productBelowAverageSquare (scale * left) (scale * right)

    scalarSquareToAverageSquare :
      Strong.negativeScalar value * Strong.negativeScalar value
      ≤ Strong.average (scale * left) (scale * right)
          * Strong.average (scale * left) (scale * right)
    scalarSquareToAverageSquare =
      ℚP.≤-trans scalarSquareToProduct productToAverageSquare

    scalarToAverage :
      Strong.negativeScalar value
      ≤ Strong.average (scale * left) (scale * right)
    scalarToAverage =
      Strong.squareBoundWithNonnegativeUpperImpliesUpper
        (Strong.negativeScalar value)
        (Strong.average (scale * left) (scale * right))
        (Strong.averageNonnegative
          (scale * left) (scale * right)
          (Strong.multiplyNonnegative scale left scaleNN leftNN)
          (Strong.multiplyNonnegative scale right scaleNN rightNN))
        scalarSquareToAverageSquare
  in
  subst
    (λ upper → Telescope.wilsonScalar value ≤ upper)
    (scaledAverageExact scale left right)
    scalarToAverage

wilsonScalarNegExact : ∀ value →
  Telescope.wilsonScalar (Q.negQ value)
  ≡ - Telescope.wilsonScalar value
wilsonScalarNegExact (Q.quat q0 q1 q2 q3) =
  ℚRing.solve-∀ q0

scaledYoungLowerFromNorm :
  ∀ value scale left right →
  0ℚ ≤ scale → 0ℚ ≤ left → 0ℚ ≤ right →
  Norm.normSq value ≤ (scale * left) * (scale * right) →
  - scaledYoungBudget scale left right
  ≤ Telescope.wilsonScalar value
scaledYoungLowerFromNorm
    value scale left right scaleNN leftNN rightNN normUpper =
  let
    negNormUpper :
      Norm.normSq (Q.negQ value)
      ≤ (scale * left) * (scale * right)
    negNormUpper =
      subst
        (λ lower → lower ≤ (scale * left) * (scale * right))
        (sym (Atom.normSqNegExact value))
        normUpper

    negUpper :
      Telescope.wilsonScalar (Q.negQ value)
      ≤ scaledYoungBudget scale left right
    negUpper =
      scaledYoungUpperFromNorm
        (Q.negQ value) scale left right
        scaleNN leftNN rightNN negNormUpper

    reflected :
      - scaledYoungBudget scale left right
      ≤ - Telescope.wilsonScalar (Q.negQ value)
    reflected = ℚP.neg-mono-≤ negUpper
  in
  subst
    (λ upper → - scaledYoungBudget scale left right ≤ upper)
    (trans
      (cong -_ (wilsonScalarNegExact value))
      (ℚRing.solve-∀ (Telescope.wilsonScalar value)))
    reflected

quaternionScaledYoungUpperLevel : ProofLevel
quaternionScaledYoungUpperLevel = machineChecked

quaternionScaledYoungLowerLevel : ProofLevel
quaternionScaledYoungLowerLevel = machineChecked
