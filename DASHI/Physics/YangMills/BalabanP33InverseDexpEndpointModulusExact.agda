module DASHI.Physics.YangMills.BalabanP33InverseDexpEndpointModulusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Check the removable inverse-dexp endpoint at polynomial level.  For the
-- seventh-order sine/cosine truncations used by the constructive proof,
--
--   n7(t) = t^3/6 - t^5/40 + t^7/1008,
--   d7(t) = 2t^3 - t^5/3 + t^7/60,
--
-- the exact defect from the endpoint coefficient is
--
--   n7(t) - d7(t)/12
--     = t^5 (1/360 - t^2/2520).
--
-- On t^2 <= 1/4 this defect is nonnegative and is bounded by
--
--   (t^2/100) d7(t).
--
-- Thus the truncated quotient has the explicit quadratic endpoint modulus
-- 1/100.  This is intentionally stronger than merely declaring beta(0)=1/12:
-- it supplies the exact cross-multiplied continuity estimate needed to pass
-- the positive branch to the removable endpoint constructively.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

square cube fifth seventh : ℚ → ℚ
square t = t * t
cube t = square t * t
fifth t = square t * cube t
seventh t = square t * fifth t

numeratorSepticTruncation : ℚ → ℚ
numeratorSepticTruncation t =
  (+ 1 / 6) * cube t
  - (+ 1 / 40) * fifth t
  + (+ 1 / 1008) * seventh t

denominatorSepticTruncation : ℚ → ℚ
denominatorSepticTruncation t =
  (+ 2 / 1) * cube t
  - (+ 1 / 3) * fifth t
  + (+ 1 / 60) * seventh t

endpointDefect : ℚ → ℚ
endpointDefect t =
  numeratorSepticTruncation t
  - (+ 1 / 12) * denominatorSepticTruncation t

endpointDefectFactor : ℚ → ℚ
endpointDefectFactor t =
  (+ 1 / 360) - (+ 1 / 2520) * square t

endpointDefectExact : ∀ t →
  endpointDefect t ≡ fifth t * endpointDefectFactor t
endpointDefectExact = ℚRing.solve-∀

denominatorFactor : ℚ → ℚ
denominatorFactor t =
  (+ 2 / 1)
  - (+ 1 / 3) * square t
  + (+ 1 / 60) * square t * square t

denominatorFactorizationExact : ∀ t →
  denominatorSepticTruncation t ≡ cube t * denominatorFactor t
denominatorFactorizationExact = ℚRing.solve-∀

endpointUpperSlackFactor : ℚ → ℚ
endpointUpperSlackFactor t =
  (+ 277 / 16800)
  + (+ 37 / 12600) * ((+ 1 / 4) - square t)
  + (+ 1 / 6000) * square t * square t

endpointFactorPlusSlackExact : ∀ t →
  endpointDefectFactor t + endpointUpperSlackFactor t
  ≡ (+ 1 / 100) * denominatorFactor t
endpointFactorPlusSlackExact = ℚRing.solve-∀

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

squareNonnegative : ∀ t → 0ℚ ≤ square t
squareNonnegative t = ℚP.nonNegative⁻¹ (square t)

cubeNonnegative : ∀ t → 0ℚ ≤ t → 0ℚ ≤ cube t
cubeNonnegative t tNonnegative =
  productNonnegative (square t) t (squareNonnegative t) tNonnegative

fifthNonnegative : ∀ t → 0ℚ ≤ t → 0ℚ ≤ fifth t
fifthNonnegative t tNonnegative =
  productNonnegative
    (square t) (cube t)
    (squareNonnegative t)
    (cubeNonnegative t tNonnegative)

squareGapNonnegative : ∀ t →
  square t ≤ (+ 1 / 4) →
  0ℚ ≤ (+ 1 / 4) - square t
squareGapNonnegative t squareBelowQuarter =
  ℚP.p≤q⇒0≤q-p squareBelowQuarter

endpointDefectFactorPositiveDecomposition : ∀ t →
  endpointDefectFactor t
  ≡ (+ 3 / 1120)
    + (+ 1 / 2520) * ((+ 1 / 4) - square t)
endpointDefectFactorPositiveDecomposition = ℚRing.solve-∀

endpointDefectFactorNonnegative : ∀ t →
  square t ≤ (+ 1 / 4) →
  0ℚ ≤ endpointDefectFactor t
endpointDefectFactorNonnegative t squareBelowQuarter =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (endpointDefectFactorPositiveDecomposition t))
    (ℚP.+-mono-≤
      (ℚP.nonNegative⁻¹ (+ 3 / 1120))
      (productNonnegative
        (+ 1 / 2520)
        ((+ 1 / 4) - square t)
        (ℚP.nonNegative⁻¹ (+ 1 / 2520))
        (squareGapNonnegative t squareBelowQuarter)))

endpointUpperSlackFactorNonnegative : ∀ t →
  square t ≤ (+ 1 / 4) →
  0ℚ ≤ endpointUpperSlackFactor t
endpointUpperSlackFactorNonnegative t squareBelowQuarter =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (ℚP.nonNegative⁻¹ (+ 277 / 16800))
      (productNonnegative
        (+ 37 / 12600)
        ((+ 1 / 4) - square t)
        (ℚP.nonNegative⁻¹ (+ 37 / 12600))
        (squareGapNonnegative t squareBelowQuarter)))
    (productNonnegative
      ((+ 1 / 6000) * square t)
      (square t)
      (productNonnegative
        (+ 1 / 6000) (square t)
        (ℚP.nonNegative⁻¹ (+ 1 / 6000))
        (squareNonnegative t))
      (squareNonnegative t))

endpointDefectNonnegative : ∀ t →
  0ℚ ≤ t →
  square t ≤ (+ 1 / 4) →
  0ℚ ≤ endpointDefect t
endpointDefectNonnegative t tNonnegative squareBelowQuarter =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (endpointDefectExact t))
    (productNonnegative
      (fifth t) (endpointDefectFactor t)
      (fifthNonnegative t tNonnegative)
      (endpointDefectFactorNonnegative t squareBelowQuarter))

endpointFactorBelowOnePercentDenominatorFactor : ∀ t →
  square t ≤ (+ 1 / 4) →
  endpointDefectFactor t ≤ (+ 1 / 100) * denominatorFactor t
endpointFactorBelowOnePercentDenominatorFactor t squareBelowQuarter =
  subst
    (λ upper → endpointDefectFactor t ≤ upper)
    (endpointFactorPlusSlackExact t)
    (let
      instance
        slackNN : NonNegative (endpointUpperSlackFactor t)
        slackNN = ℚ.nonNegative
          (endpointUpperSlackFactorNonnegative t squareBelowQuarter)
     in ℚP.p≤p+q
          (endpointDefectFactor t)
          (endpointUpperSlackFactor t))

endpointDefectQuadraticModulus : ∀ t →
  0ℚ ≤ t →
  square t ≤ (+ 1 / 4) →
  endpointDefect t
  ≤ (+ 1 / 100) * square t * denominatorSepticTruncation t
endpointDefectQuadraticModulus t tNonnegative squareBelowQuarter =
  let
    factorBound =
      endpointFactorBelowOnePercentDenominatorFactor
        t squareBelowQuarter
    scaled =
      let
        instance
          fifthNN : NonNegative (fifth t)
          fifthNN = ℚ.nonNegative (fifthNonnegative t tNonnegative)
      in ℚP.*-monoˡ-≤-nonNeg (fifth t) factorBound
  in
  subst
    (λ lower → lower
      ≤ (+ 1 / 100) * square t * denominatorSepticTruncation t)
    (sym (endpointDefectExact t))
    (subst
      (λ upper →
        fifth t * ((+ 1 / 100) * denominatorFactor t) ≤ upper)
      (ℚRing.solve-∀ t)
      scaled)

endpointCoefficientSeriesSecondOrder :
  (+ 1 / 12) + (+ 1 / 720) * (+ 1 / 4)
  ≡ (+ 241 / 2880)
endpointCoefficientSeriesSecondOrder = ℚRing.solve []

p33InverseDexpEndpointExpansionLevel : ProofLevel
p33InverseDexpEndpointExpansionLevel = machineChecked

p33InverseDexpEndpointQuadraticModulusLevel : ProofLevel
p33InverseDexpEndpointQuadraticModulusLevel = machineChecked
