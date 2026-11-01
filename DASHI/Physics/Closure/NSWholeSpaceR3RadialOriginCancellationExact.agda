module DASHI.Physics.Closure.NSWholeSpaceR3RadialOriginCancellationExact where

------------------------------------------------------------------------
-- A / THREE-DIMENSIONAL RADIAL ORIGIN CANCELLATION
--
-- Let
--
--   q  = |xi|^2 > 0,
--   a  = nu q,        nu > 0.
--
-- The centered-resolvent curvature contributes a^{-3}.  In three dimensions
-- the radial Lebesgue density contributes r^2 = q.  Therefore a state factor
-- with FOUR output-frequency powers,
--
--   q^2 M = |xi|^4 M,
--
-- is already enough:
--
--   q * a^{-3} * (q^2 M)
--      ~= nu^{-3} M.
--
-- Thus the pointwise |xi|^6 target is sufficient but unnecessarily strong.
-- The sharp measure-aware target is |xi|^4 (modulo an integrable angular/radial
-- majorant), provided signed cancellation is preserved until this radial
-- density is applied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Physics.Closure.NSWholeSpaceLowFrequencyCompensationExact as Low

inverse :
  (x : BishopReal.ℝ) →
  BishopReal._≄0 x →
  BishopReal.ℝ
inverse = BishopInverse._⁻¹

inverseCube :
  (x : BishopReal.ℝ) →
  BishopReal._≄0 x →
  BishopReal.ℝ
inverseCube = Low.inverseCube

square : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x

cube : BishopReal.ℝ → BishopReal.ℝ
cube x = BishopReal._*_ (BishopReal._*_ x x) x

productPositive :
  ∀ {x y} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.0ℝ y →
  BishopReal._<_ BishopReal.0ℝ (BishopReal._*_ x y)
productPositive xPositive yPositive =
  BishopP.posx⇒0<x
    (BishopP.posx,y⇒posx*y
      (BishopP.0<x⇒posx xPositive)
      (BishopP.0<x⇒posx yPositive))

record PositiveViscosityRadiusSquare : Set where
  constructor positive-viscosity-radius-square
  field
    viscosity radiusSquared : BishopReal.ℝ
    viscosityPositive :
      BishopReal._<_ BishopReal.0ℝ viscosity
    radiusSquaredPositive :
      BishopReal._<_ BishopReal.0ℝ radiusSquared

open PositiveViscosityRadiusSquare public

heatRate :
  PositiveViscosityRadiusSquare →
  BishopReal.ℝ
heatRate dataSet =
  BishopReal._*_
    (viscosity dataSet)
    (radiusSquared dataSet)

heatRatePositive :
  (dataSet : PositiveViscosityRadiusSquare) →
  BishopReal._<_ BishopReal.0ℝ (heatRate dataSet)
heatRatePositive dataSet =
  productPositive
    (viscosityPositive dataSet)
    (radiusSquaredPositive dataSet)

viscosityNonzero :
  (dataSet : PositiveViscosityRadiusSquare) →
  BishopReal._≄0 (viscosity dataSet)
viscosityNonzero dataSet =
  Reciprocal.xNonzero (viscosityPositive dataSet)

radiusSquaredNonzero :
  (dataSet : PositiveViscosityRadiusSquare) →
  BishopReal._≄0 (radiusSquared dataSet)
radiusSquaredNonzero dataSet =
  Reciprocal.xNonzero (radiusSquaredPositive dataSet)

heatRateNonzero :
  (dataSet : PositiveViscosityRadiusSquare) →
  BishopReal._≄0 (heatRate dataSet)
heatRateNonzero dataSet =
  Reciprocal.xNonzero (heatRatePositive dataSet)

inverseProductExact :
  (dataSet : PositiveViscosityRadiusSquare) →
  BishopReal._≃_
    (inverse (heatRate dataSet) (heatRateNonzero dataSet))
    (BishopReal._*_
      (inverse (viscosity dataSet) (viscosityNonzero dataSet))
      (inverse (radiusSquared dataSet) (radiusSquaredNonzero dataSet)))
inverseProductExact dataSet =
  let
    nu = viscosity dataSet
    q = radiusSquared dataSet
    invNu = inverse nu (viscosityNonzero dataSet)
    invQ = inverse q (radiusSquaredNonzero dataSet)
    invA = inverse (heatRate dataSet) (heatRateNonzero dataSet)

    candidateRightInverse :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_ nu q)
          (BishopReal._*_ invNu invQ))
        BishopReal.1ℝ
    candidateRightInverse =
      let
        nuLaw = BishopInverse.*-inverseˡ nu (viscosityNonzero dataSet)
        qLaw = BishopInverse.*-inverseˡ q (radiusSquaredNonzero dataSet)
        open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 4
          (λ n q' ni qi →
            (n ⊗ q') ⊗ (ni ⊗ qi)
            ⊜
            (n ⊗ ni) ⊗ (q' ⊗ qi))
          BishopP.≃-refl
          nu q invNu invQ)
        (BishopP.≃-trans
          (BishopP.*-cong nuLaw qLaw)
          (BishopP.*-identityˡ BishopReal.1ℝ))

    actualRightInverse =
      BishopInverse.*-inverseˡ
        (heatRate dataSet)
        (heatRateNonzero dataSet)

    -- In a field, two right inverses of the same nonzero element coincide.
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.≃-symm
      (BishopP.*-identityˡ invA))
    (BishopP.≃-trans
      (BishopP.*-congˡ
        (BishopP.≃-symm candidateRightInverse))
      (BishopP.≃-trans
        (solve 4
          (λ a i n q' →
            i ⊗ (a ⊗ (n ⊗ q'))
            ⊜
            (i ⊗ a) ⊗ (n ⊗ q'))
          BishopP.≃-refl
          (heatRate dataSet) invA invNu invQ)
        (BishopP.≃-trans
          (BishopP.*-congˡ actualRightInverse)
          (BishopP.*-identityˡ
            (BishopReal._*_ invNu invQ)))))

inverseCubeProductExact :
  (dataSet : PositiveViscosityRadiusSquare) →
  BishopReal._≃_
    (inverseCube
      (heatRate dataSet)
      (heatRateNonzero dataSet))
    (BishopReal._*_
      (inverseCube
        (viscosity dataSet)
        (viscosityNonzero dataSet))
      (inverseCube
        (radiusSquared dataSet)
        (radiusSquaredNonzero dataSet)))
inverseCubeProductExact dataSet =
  let
    productInverse = inverseProductExact dataSet
    invNu = inverse (viscosity dataSet) (viscosityNonzero dataSet)
    invQ = inverse (radiusSquared dataSet) (radiusSquaredNonzero dataSet)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-cong
      (BishopP.*-cong productInverse productInverse)
      productInverse)
    (solve 2
      (λ n q →
        ((n ⊗ q) ⊗ (n ⊗ q)) ⊗ (n ⊗ q)
        ⊜
        (((n ⊗ n) ⊗ n) ⊗ ((q ⊗ q) ⊗ q)))
      BishopP.≃-refl
      invNu invQ)

radiusDensityCancelsInverseCubeAgainstFourthOrder :
  (dataSet : PositiveViscosityRadiusSquare) →
  (majorant : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopReal._*_
      (radiusSquared dataSet)
      (BishopReal._*_
        (inverseCube
          (heatRate dataSet)
          (heatRateNonzero dataSet))
        (BishopReal._*_
          (square (radiusSquared dataSet))
          majorant)))
    (BishopReal._*_
      (inverseCube
        (viscosity dataSet)
        (viscosityNonzero dataSet))
      majorant)
radiusDensityCancelsInverseCubeAgainstFourthOrder dataSet majorant =
  let
    q = radiusSquared dataSet
    iq = inverse q (radiusSquaredNonzero dataSet)
    invNu3 =
      inverseCube
        (viscosity dataSet)
        (viscosityNonzero dataSet)
    invQ3 =
      inverseCube q (radiusSquaredNonzero dataSet)

    splitInverseCube = inverseCubeProductExact dataSet
    qInverseLaw =
      BishopInverse.*-inverseˡ q (radiusSquaredNonzero dataSet)

    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-congʳ
      (BishopP.*-congˡ splitInverseCube))
    (BishopP.≃-trans
      (solve 4
        (λ q' n qi m →
          q' ⊗
          ((n ⊗ ((qi ⊗ qi) ⊗ qi))
           ⊗ ((q' ⊗ q') ⊗ m))
          ⊜
          n ⊗
          (((q' ⊗ qi) ⊗ (q' ⊗ qi) ⊗ (q' ⊗ qi)) ⊗ m))
        BishopP.≃-refl
        q invNu3 iq majorant)
      (BishopP.≃-trans
        (BishopP.*-congʳ
          (BishopP.*-congˡ
            (BishopP.*-cong
              (BishopP.*-cong qInverseLaw qInverseLaw)
              qInverseLaw)))
        (let open BishopP.ℝ-Solver
         in solve 2
           (λ n m →
             n ⊗
             (((BishopReal.1ℝ ⊗ BishopReal.1ℝ)
               ⊗ BishopReal.1ℝ) ⊗ m)
             ⊜ n ⊗ m)
           BishopP.≃-refl invNu3 majorant)))

------------------------------------------------------------------------
-- Consequence for A:
--
-- after radialization, a fourth-order physical state factor is enough to
-- remove the entire origin singularity.  What remains is an ordinary
-- integrability problem for the majorant and the angular/sphere measure.
------------------------------------------------------------------------

r3RadialDensityCancelsResidualInverseSquare : Bool
r3RadialDensityCancelsResidualInverseSquare = true

pointwiseXiSixRequired : Bool
pointwiseXiSixRequired = false

measureAwareXiFourSufficesAlgebraically : Bool
measureAwareXiFourSufficesAlgebraically = true

radialLebesgueSameObjectWeldClosedHere : Bool
radialLebesgueSameObjectWeldClosedHere = false

physicalXiFourProducerClosedHere : Bool
physicalXiFourProducerClosedHere = false

clayPromotion : Bool
clayPromotion = false

r3RadialDensityCancelsResidualInverseSquareIsTrue :
  r3RadialDensityCancelsResidualInverseSquare ≡ true
r3RadialDensityCancelsResidualInverseSquareIsTrue = refl

pointwiseXiSixRequiredIsFalse :
  pointwiseXiSixRequired ≡ false
pointwiseXiSixRequiredIsFalse = refl

measureAwareXiFourSufficesAlgebraicallyIsTrue :
  measureAwareXiFourSufficesAlgebraically ≡ true
measureAwareXiFourSufficesAlgebraicallyIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
