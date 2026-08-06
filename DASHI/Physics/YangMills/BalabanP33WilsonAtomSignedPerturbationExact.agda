module DASHI.Physics.YangMills.BalabanP33WilsonAtomSignedPerturbationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- The local Wilson problem needs signed estimates, not only bounds on the
-- square of a sixteen-atom defect.  This module proves the square-root-free
-- weighted Young inequality directly over the repository's exact rational
-- order and applies it to the exact bilinear perturbation identity
--
--   (a+r)(b+s)-ab = as+br+rs.
--
-- Each of the three perturbation products receives its own positive reciprocal
-- pair.  The result is the reusable signed scalar reducer consumed by the
-- diagonal/cross Wilson placement analysis; no absolute value or square root is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record ReciprocalYoungPair : Set where
  field
    weight inverseWeight : ℚ
    weightNonnegative : 0ℚ ≤ weight
    inverseWeightNonnegative : 0ℚ ≤ inverseWeight
    reciprocal : inverseWeight * weight ≡ + 1 / 1

open ReciprocalYoungPair public

weightedYoungSquare : ReciprocalYoungPair → ℚ → ℚ → ℚ
weightedYoungSquare parameters left right =
  inverseWeight parameters
    * ((weight parameters * left + right)
      * (weight parameters * left + right))

weightedYoungSquareNonnegative :
  ∀ parameters left right →
  0ℚ ≤ weightedYoungSquare parameters left right
weightedYoungSquareNonnegative parameters left right =
  Norm.scaleNonnegative
    (inverseWeight parameters)
    (inverseWeightNonnegative parameters)
    (FiniteL2.squareNonnegative
      (weight parameters * left + right))

weightedYoungSquareExpanded :
  ∀ parameters left right →
  weightedYoungSquare parameters left right
  ≡ weight parameters * (left * left)
    + (+ 2 / 1) * left * right
    + inverseWeight parameters * (right * right)
weightedYoungSquareExpanded parameters left right =
  let
    raw :
      weightedYoungSquare parameters left right
      ≡ weight parameters * (left * left)
        + (+ 2 / 1) * left * right
        + inverseWeight parameters * (right * right)
        + (inverseWeight parameters * weight parameters - (+ 1 / 1))
          * (weight parameters * left * left
            + (+ 2 / 1) * left * right)
    raw = ℚRing.solve-∀
      (weight parameters) (inverseWeight parameters) left right
  in
  trans raw
    (subst
      (λ product →
        weight parameters * (left * left)
          + (+ 2 / 1) * left * right
          + inverseWeight parameters * (right * right)
          + (product - (+ 1 / 1))
            * (weight parameters * left * left
              + (+ 2 / 1) * left * right)
        ≡ weight parameters * (left * left)
          + (+ 2 / 1) * left * right
          + inverseWeight parameters * (right * right))
      (sym (reciprocal parameters))
      (ℚRing.solve []))

weightedYoungLower :
  ∀ parameters left right →
  - (weight parameters * (left * left))
    - inverseWeight parameters * (right * right)
  ≤ (+ 2 / 1) * left * right
weightedYoungLower parameters left right =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (weightedYoungSquareExpanded parameters left right)
      (weightedYoungSquareNonnegative parameters left right))

bilinearPerturbationExact : ∀ baseLeft baseRight defectLeft defectRight →
  (baseLeft + defectLeft) * (baseRight + defectRight)
    - baseLeft * baseRight
  ≡ baseLeft * defectRight
    + baseRight * defectLeft
    + defectLeft * defectRight
bilinearPerturbationExact = ℚRing.solve-∀

record BilinearYoungParameters : Set where
  field
    baseLeftDefectRight : ReciprocalYoungPair
    baseRightDefectLeft : ReciprocalYoungPair
    defectDefect : ReciprocalYoungPair

open BilinearYoungParameters public

bilinearYoungCost :
  BilinearYoungParameters → ℚ → ℚ → ℚ → ℚ → ℚ
bilinearYoungCost parameters baseLeft baseRight defectLeft defectRight =
  (+ 1 / 2)
    * (weight (baseLeftDefectRight parameters) * (baseLeft * baseLeft)
      + inverseWeight (baseLeftDefectRight parameters)
        * (defectRight * defectRight))
  + (+ 1 / 2)
    * (weight (baseRightDefectLeft parameters) * (baseRight * baseRight)
      + inverseWeight (baseRightDefectLeft parameters)
        * (defectLeft * defectLeft))
  + (+ 1 / 2)
    * (weight (defectDefect parameters) * (defectLeft * defectLeft)
      + inverseWeight (defectDefect parameters)
        * (defectRight * defectRight))

bilinearPerturbationSignedLower :
  ∀ parameters baseLeft baseRight defectLeft defectRight →
  - bilinearYoungCost parameters
      baseLeft baseRight defectLeft defectRight
  ≤ (baseLeft + defectLeft) * (baseRight + defectRight)
      - baseLeft * baseRight
bilinearPerturbationSignedLower
    parameters baseLeft baseRight defectLeft defectRight =
  let
    first = weightedYoungLower
      (baseLeftDefectRight parameters) baseLeft defectRight
    second = weightedYoungLower
      (baseRightDefectLeft parameters) baseRight defectLeft
    third = weightedYoungLower
      (defectDefect parameters) defectLeft defectRight

    combined = ℚP.+-mono-≤
      (ℚP.+-mono-≤ first second) third

    scaledCombined :
      (+ 1 / 2)
        * ((- (weight (baseLeftDefectRight parameters)
              * (baseLeft * baseLeft))
            - inverseWeight (baseLeftDefectRight parameters)
              * (defectRight * defectRight))
          + (- (weight (baseRightDefectLeft parameters)
              * (baseRight * baseRight))
            - inverseWeight (baseRightDefectLeft parameters)
              * (defectLeft * defectLeft))
          + (- (weight (defectDefect parameters)
              * (defectLeft * defectLeft))
            - inverseWeight (defectDefect parameters)
              * (defectRight * defectRight)))
      ≤ (+ 1 / 2)
        * (((+ 2 / 1) * baseLeft * defectRight
          + (+ 2 / 1) * baseRight * defectLeft)
          + (+ 2 / 1) * defectLeft * defectRight)
    scaledCombined =
      Norm.scaleNonnegative
        (+ 1 / 2)
        (ℚP.nonNegative⁻¹ (+ 1 / 2))
        combined
  in
  subst
    (λ lower →
      lower
      ≤ (baseLeft + defectLeft) * (baseRight + defectRight)
        - baseLeft * baseRight)
    (ℚRing.solve-∀
      (weight (baseLeftDefectRight parameters))
      (inverseWeight (baseLeftDefectRight parameters))
      (weight (baseRightDefectLeft parameters))
      (inverseWeight (baseRightDefectLeft parameters))
      (weight (defectDefect parameters))
      (inverseWeight (defectDefect parameters))
      baseLeft baseRight defectLeft defectRight)
    (subst
      (λ upper →
        (+ 1 / 2)
          * ((- (weight (baseLeftDefectRight parameters)
                * (baseLeft * baseLeft))
              - inverseWeight (baseLeftDefectRight parameters)
                * (defectRight * defectRight))
            + (- (weight (baseRightDefectLeft parameters)
                * (baseRight * baseRight))
              - inverseWeight (baseRightDefectLeft parameters)
                * (defectLeft * defectLeft))
            + (- (weight (defectDefect parameters)
                * (defectLeft * defectLeft))
              - inverseWeight (defectDefect parameters)
                * (defectRight * defectRight)))
        ≤ upper)
      (trans
        (ℚRing.solve-∀ baseLeft baseRight defectLeft defectRight)
        (sym
          (bilinearPerturbationExact
            baseLeft baseRight defectLeft defectRight)))
      scaledCombined)

wilsonWeightedYoungLevel : ProofLevel
wilsonWeightedYoungLevel = machineChecked

wilsonBilinearPerturbationIdentityLevel : ProofLevel
wilsonBilinearPerturbationIdentityLevel = machineChecked

wilsonBilinearSignedReducerLevel : ProofLevel
wilsonBilinearSignedReducerLevel = machineChecked
