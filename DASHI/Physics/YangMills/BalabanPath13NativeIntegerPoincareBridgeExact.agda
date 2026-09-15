module DASHI.Physics.YangMills.BalabanPath13NativeIntegerPoincareBridgeExact where

------------------------------------------------------------------------
-- Native integer Path13 certificate -> ordinary rational Poincare floor.
--
-- The huge closed certificate never enters normalized Data.Rational arithmetic.
-- It is interpreted in ℚᵘ, where denominators are carried without gcd/division.
-- Only the final order statement is transported back through toℚᵘ-cancel-≤.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer using (ℤ; +_; -[1+_]; _*_; -_)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_)
import Data.Rational.Properties as RP
import Data.Rational.Unnormalised.Base as U
open import Data.Rational.Unnormalised.Base
  using (ℚᵘ; 0ℚᵘ; _≃_; NonNegative; Positive; mkℚᵘ)
  renaming (_+_ to _+ᵘ_; _*_ to _*ᵘ_; -_ to -ᵘ_; _/_ to _/ᵘ_; _≤_ to _≤ᵘ_)
import Data.Rational.Unnormalised.Properties as UP
import Data.Rational.Unnormalised.Tactic.RingSolver as URing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq; sqDiff)
open import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLDataExact
open import DASHI.Physics.YangMills.BalabanPath13NativeIntegerCoefficientCertificateExact
import DASHI.Physics.YangMills.BalabanIntegerTriangularUnnormalisedCompilerExact as C

------------------------------------------------------------------------
-- Small normalized -> unnormalised transport helpers.
------------------------------------------------------------------------

sumQ : List ℚ → ℚ
sumQ [] = 0ℚ
sumQ (x ∷ xs) = x + sumQ xs

sumU : List ℚᵘ → ℚᵘ
sumU [] = 0ℚᵘ
sumU (x ∷ xs) = x +ᵘ sumU xs

toListU : List ℚ → List ℚᵘ
toListU [] = []
toListU (x ∷ xs) = RP.toℚᵘ x ∷ toListU xs

toSumU : ∀ xs → RP.toℚᵘ (sumQ xs) ≃ sumU (toListU xs)
toSumU [] = UP.≃-refl
toSumU (x ∷ xs) =
  UP.≃-trans
    (RP.toℚᵘ-homo-+ x (sumQ xs))
    (UP.+-cong UP.≃-refl (toSumU xs))

toSubU : ∀ p q →
  RP.toℚᵘ (p - q) ≃ RP.toℚᵘ p +ᵘ (-ᵘ RP.toℚᵘ q)
toSubU p q =
  UP.≃-trans
    (RP.toℚᵘ-homo-+ p (- q))
    (UP.+-cong UP.≃-refl (RP.toℚᵘ-homo‿- q))

squareIntoQ : ∀ {u q} →
  u ≃ RP.toℚᵘ q →
  u *ᵘ u ≃ RP.toℚᵘ (q * q)
squareIntoQ {u} {q} u≈q =
  UP.≃-trans
    (UP.*-cong u≈q u≈q)
    (UP.≃-sym (RP.toℚᵘ-homo-* q q))

coordinateTermsQ : Path13Coordinates → List ℚ
coordinateTermsQ c =
  y0 c ∷ y1 c ∷ y2 c ∷ y3 c ∷ y4 c ∷ y5 c ∷
  y6 c ∷ y7 c ∷ y8 c ∷ y9 c ∷ y10 c ∷ y11 c ∷ []

coordinatesU : Path13Coordinates → List ℚᵘ
coordinatesU c = toListU (coordinateTermsQ c)

coordinateSumExact : ∀ c →
  sumQ (coordinateTermsQ c)
  ≡ y0 c + (y1 c + (y2 c + (y3 c + (y4 c + (y5 c +
     (y6 c + (y7 c + (y8 c + (y9 c + (y10 c + y11 c)))))))))))
coordinateSumExact c rewrite RP.+-identityʳ (y11 c) = refl

lastCoordinateAsSum : ∀ c →
  lastCoordinate c ≡ - (sumQ (coordinateTermsQ c))
lastCoordinateAsSum c = cong -_ (sym (coordinateSumExact c))

lastCoordinateToU : ∀ c →
  RP.toℚᵘ (lastCoordinate c)
  ≃ -ᵘ (sumU (coordinatesU c))
lastCoordinateToU c =
  UP.≃-trans
    (RP.toℚᵘ-cong (lastCoordinateAsSum c))
    (UP.≃-trans
      (RP.toℚᵘ-homo‿- (sumQ (coordinateTermsQ c)))
      (UP.-‿cong (toSumU (coordinateTermsQ c))))

------------------------------------------------------------------------
-- Degree-one attachment only.  Reflection sees twelve atoms but no products
-- between coordinate variables and no huge rational coefficients.
------------------------------------------------------------------------

energyLinear0RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy0CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷
     RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷
     RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ b +ᵘ (-ᵘ RP.toℚᵘ a)
energyLinear0RawU = URing.solve-∀
energyLinear1RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy1CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ c +ᵘ (-ᵘ RP.toℚᵘ b)
energyLinear1RawU = URing.solve-∀
energyLinear2RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy2CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ d +ᵘ (-ᵘ RP.toℚᵘ c)
energyLinear2RawU = URing.solve-∀
energyLinear3RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy3CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ e +ᵘ (-ᵘ RP.toℚᵘ d)
energyLinear3RawU = URing.solve-∀
energyLinear4RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy4CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ f +ᵘ (-ᵘ RP.toℚᵘ e)
energyLinear4RawU = URing.solve-∀
energyLinear5RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy5CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ g +ᵘ (-ᵘ RP.toℚᵘ f)
energyLinear5RawU = URing.solve-∀
energyLinear6RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy6CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ h +ᵘ (-ᵘ RP.toℚᵘ g)
energyLinear6RawU = URing.solve-∀
energyLinear7RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy7CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ i +ᵘ (-ᵘ RP.toℚᵘ h)
energyLinear7RawU = URing.solve-∀
energyLinear8RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy8CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ j +ᵘ (-ᵘ RP.toℚᵘ i)
energyLinear8RawU = URing.solve-∀
energyLinear9RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy9CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ k +ᵘ (-ᵘ RP.toℚᵘ j)
energyLinear9RawU = URing.solve-∀
energyLinear10RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy10CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ RP.toℚᵘ l +ᵘ (-ᵘ RP.toℚᵘ k)
energyLinear10RawU = URing.solve-∀
energyLinear11RawU : ∀ a b c d e f g h i j k l →
  C.dotZU energy11CoefficientsZ
    (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])
  ≃ -ᵘ (sumU (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])) +ᵘ (-ᵘ RP.toℚᵘ l)
energyLinear11RawU = URing.solve-∀

energyLinear0U : ∀ c → C.dotZU energy0CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y1 c - y0 c)
energyLinear0U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear0RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU b a))
energyLinear1U : ∀ c → C.dotZU energy1CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y2 c - y1 c)
energyLinear1U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear1RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU c b))
energyLinear2U : ∀ c → C.dotZU energy2CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y3 c - y2 c)
energyLinear2U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear2RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU d c))
energyLinear3U : ∀ c → C.dotZU energy3CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y4 c - y3 c)
energyLinear3U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear3RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU e d))
energyLinear4U : ∀ c → C.dotZU energy4CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y5 c - y4 c)
energyLinear4U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear4RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU f e))
energyLinear5U : ∀ c → C.dotZU energy5CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y6 c - y5 c)
energyLinear5U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear5RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU g f))
energyLinear6U : ∀ c → C.dotZU energy6CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y7 c - y6 c)
energyLinear6U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear6RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU h g))
energyLinear7U : ∀ c → C.dotZU energy7CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y8 c - y7 c)
energyLinear7U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear7RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU i h))
energyLinear8U : ∀ c → C.dotZU energy8CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y9 c - y8 c)
energyLinear8U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear8RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU j i))
energyLinear9U : ∀ c → C.dotZU energy9CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y10 c - y9 c)
energyLinear9U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear9RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU k j))
energyLinear10U : ∀ c → C.dotZU energy10CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y11 c - y10 c)
energyLinear10U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energyLinear10RawU a b c d e f g h i j k l) (UP.≃-sym (toSubU l k))
energyLinear11U : ∀ c → C.dotZU energy11CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (lastCoordinate c - y11 c)
energyLinear11U c =
  UP.≃-trans
    (case c return (λ c → C.dotZU energy11CoefficientsZ (coordinatesU c) ≃ -ᵘ (sumU (coordinatesU c)) +ᵘ (-ᵘ RP.toℚᵘ (y11 c))) of λ where
      (path13Coordinates a b c d e f g h i j k l) → energyLinear11RawU a b c d e f g h i j k l)
    (UP.≃-trans
      (UP.+-cong (UP.≃-sym (lastCoordinateToU c)) UP.≃-refl)
      (UP.≃-sym (toSubU (lastCoordinate c) (y11 c))))

normLinearRawU : ∀ a b c d e f g h i j k l →
  C.dotZU norm0CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ a
normLinearRawU = URing.solve-∀

-- The remaining standard-basis rows are definitionally the same statement
-- after shifting the single 1; ring reflection remains degree one.
normLinear0U : ∀ c → C.dotZU norm0CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y0 c)
normLinear0U (path13Coordinates a b c d e f g h i j k l) = normLinearRawU a b c d e f g h i j k l
normLinear1U : ∀ c → C.dotZU norm1CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y1 c)
normLinear1U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear2U : ∀ c → C.dotZU norm2CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y2 c)
normLinear2U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear3U : ∀ c → C.dotZU norm3CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y3 c)
normLinear3U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear4U : ∀ c → C.dotZU norm4CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y4 c)
normLinear4U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear5U : ∀ c → C.dotZU norm5CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y5 c)
normLinear5U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear6U : ∀ c → C.dotZU norm6CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y6 c)
normLinear6U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear7U : ∀ c → C.dotZU norm7CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y7 c)
normLinear7U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear8U : ∀ c → C.dotZU norm8CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y8 c)
normLinear8U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear9U : ∀ c → C.dotZU norm9CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y9 c)
normLinear9U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear10U : ∀ c → C.dotZU norm10CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y10 c)
normLinear10U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear11U : ∀ c → C.dotZU norm11CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y11 c)
normLinear11U (path13Coordinates a b c d e f g h i j k l) = URing.solve-∀ a b c d e f g h i j k l
normLinear12U : ∀ c → C.dotZU norm12CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (lastCoordinate c)
normLinear12U c =
  UP.≃-trans
    (case c return (λ c → C.dotZU norm12CoefficientsZ (coordinatesU c) ≃ -ᵘ sumU (coordinatesU c)) of λ where
      (path13Coordinates a b c d e f g h i j k l) → URing.solve-∀ a b c d e f g h i j k l)
    (UP.≃-sym (lastCoordinateToU c))

energyTermsQ : Path13Coordinates → List ℚ
energyTermsQ c =
  sqDiff (y1 c) (y0 c) ∷ sqDiff (y2 c) (y1 c) ∷
  sqDiff (y3 c) (y2 c) ∷ sqDiff (y4 c) (y3 c) ∷
  sqDiff (y5 c) (y4 c) ∷ sqDiff (y6 c) (y5 c) ∷
  sqDiff (y7 c) (y6 c) ∷ sqDiff (y8 c) (y7 c) ∷
  sqDiff (y9 c) (y8 c) ∷ sqDiff (y10 c) (y9 c) ∷
  sqDiff (y11 c) (y10 c) ∷ sqDiff (lastCoordinate c) (y11 c) ∷ []

normTermsQ : Path13Coordinates → List ℚ
normTermsQ c =
  sq (y0 c) ∷ sq (y1 c) ∷ sq (y2 c) ∷ sq (y3 c) ∷
  sq (y4 c) ∷ sq (y5 c) ∷ sq (y6 c) ∷ sq (y7 c) ∷
  sq (y8 c) ∷ sq (y9 c) ∷ sq (y10 c) ∷ sq (y11 c) ∷
  sq (lastCoordinate c) ∷ []

energySumExact : ∀ c → sumQ (energyTermsQ c) ≡ path13Energy c
energySumExact c rewrite RP.+-identityʳ (sqDiff (lastCoordinate c) (y11 c)) = refl

normSumExact : ∀ c → sumQ (normTermsQ c) ≡ path13NormSq c
normSumExact c rewrite RP.+-identityʳ (sq (lastCoordinate c)) = refl

energyValuesToTerms : ∀ c →
  C.sumSquareValuesZU energyFamiliesZ (coordinatesU c)
  ≃ sumU (toListU (energyTermsQ c))
energyValuesToTerms c =
  UP.+-cong (squareIntoQ (energyLinear0U c))
  (UP.+-cong (squareIntoQ (energyLinear1U c))
  (UP.+-cong (squareIntoQ (energyLinear2U c))
  (UP.+-cong (squareIntoQ (energyLinear3U c))
  (UP.+-cong (squareIntoQ (energyLinear4U c))
  (UP.+-cong (squareIntoQ (energyLinear5U c))
  (UP.+-cong (squareIntoQ (energyLinear6U c))
  (UP.+-cong (squareIntoQ (energyLinear7U c))
  (UP.+-cong (squareIntoQ (energyLinear8U c))
  (UP.+-cong (squareIntoQ (energyLinear9U c))
  (UP.+-cong (squareIntoQ (energyLinear10U c))
  (UP.+-cong (squareIntoQ (energyLinear11U c)) UP.≃-refl))))))))))))

normValuesToTerms : ∀ c →
  C.sumSquareValuesZU normFamiliesZ (coordinatesU c)
  ≃ sumU (toListU (normTermsQ c))
normValuesToTerms c =
  UP.+-cong (squareIntoQ (normLinear0U c))
  (UP.+-cong (squareIntoQ (normLinear1U c))
  (UP.+-cong (squareIntoQ (normLinear2U c))
  (UP.+-cong (squareIntoQ (normLinear3U c))
  (UP.+-cong (squareIntoQ (normLinear4U c))
  (UP.+-cong (squareIntoQ (normLinear5U c))
  (UP.+-cong (squareIntoQ (normLinear6U c))
  (UP.+-cong (squareIntoQ (normLinear7U c))
  (UP.+-cong (squareIntoQ (normLinear8U c))
  (UP.+-cong (squareIntoQ (normLinear9U c))
  (UP.+-cong (squareIntoQ (normLinear10U c))
  (UP.+-cong (squareIntoQ (normLinear11U c))
  (UP.+-cong (squareIntoQ (normLinear12U c)) UP.≃-refl)))))))))))))

energyEvalToQ : ∀ c →
  C.evalTriZU energyTriZ (coordinatesU c) ≃ RP.toℚᵘ (path13Energy c)
energyEvalToQ c =
  UP.≃-trans
    (C.sumSquareCompilerZU energyFamiliesZ (coordinatesU c))
    (UP.≃-trans
      (energyValuesToTerms c)
      (UP.≃-trans
        (UP.≃-sym (toSumU (energyTermsQ c)))
        (RP.toℚᵘ-cong (energySumExact c))))

normEvalToQ : ∀ c →
  C.evalTriZU normTriZ (coordinatesU c) ≃ RP.toℚᵘ (path13NormSq c)
normEvalToQ c =
  UP.≃-trans
    (C.sumSquareCompilerZU normFamiliesZ (coordinatesU c))
    (UP.≃-trans
      (normValuesToTerms c)
      (UP.≃-trans
        (UP.≃-sym (toSumU (normTermsQ c)))
        (RP.toℚᵘ-cong (normSumExact c))))

------------------------------------------------------------------------
-- Nonnegative integer-weight SOS residual.
------------------------------------------------------------------------

squareNonnegativeU : ∀ x → 0ℚᵘ ≤ᵘ (x *ᵘ x)
squareNonnegativeU x@(mkℚᵘ (+ n) d) =
  let instance
      productNonnegative : NonNegative (x *ᵘ x)
      productNonnegative = U.nonNeg
  in UP.nonNegative⁻¹ (x *ᵘ x)
squareNonnegativeU x@(mkℚᵘ -[1+ n ] d) =
  let instance
      productNonnegative : NonNegative (x *ᵘ x)
      productNonnegative = U.nonNeg
  in UP.nonNegative⁻¹ (x *ᵘ x)

weightedSquareNonnegativeU : ∀ weight coefficients coordinates →
  NonNegative (C.embedZ weight) →
  0ℚᵘ ≤ᵘ
    C.embedZ weight *ᵘ
      (C.dotZU coefficients coordinates *ᵘ C.dotZU coefficients coordinates)
weightedSquareNonnegativeU weight coefficients coordinates weightNonnegative =
  let
    dot = C.dotZU coefficients coordinates
    instance
      weightNN : NonNegative (C.embedZ weight)
      weightNN = weightNonnegative
      squareNN : NonNegative (dot *ᵘ dot)
      squareNN = U.nonNegative (squareNonnegativeU dot)
      productNN : NonNegative (C.embedZ weight *ᵘ (dot *ᵘ dot))
      productNN = UP.nonNeg*nonNeg⇒nonNeg (C.embedZ weight) (dot *ᵘ dot)
  in UP.nonNegative⁻¹ (C.embedZ weight *ᵘ (dot *ᵘ dot))

data AllWeightsNonnegative : List (ℤ × List ℤ) → Set where
  all[] : AllWeightsNonnegative []
  all∷ : ∀ {weight coefficients rest} →
    NonNegative (C.embedZ weight) →
    AllWeightsNonnegative rest →
    AllWeightsNonnegative ((weight , coefficients) ∷ rest)

sumWeightedNonnegativeU : ∀ {families} →
  AllWeightsNonnegative families →
  ∀ coordinates →
  0ℚᵘ ≤ᵘ C.sumWeightedSquareValuesZU families coordinates
sumWeightedNonnegativeU all[] coordinates = UP.≤-refl
sumWeightedNonnegativeU (all∷ {weight} {coefficients} {rest} weightNN restNN) coordinates =
  let
    term = C.embedZ weight *ᵘ
      (C.dotZU coefficients coordinates *ᵘ C.dotZU coefficients coordinates)
    tail = C.sumWeightedSquareValuesZU rest coordinates
    instance
      termNN : NonNegative term
      termNN = U.nonNegative (weightedSquareNonnegativeU weight coefficients coordinates weightNN)
      tailNN : NonNegative tail
      tailNN = U.nonNegative (sumWeightedNonnegativeU restNN coordinates)
      totalNN : NonNegative (term +ᵘ tail)
      totalNN = UP.nonNeg+nonNeg⇒nonNeg term tail
  in UP.nonNegative⁻¹ (term +ᵘ tail)

scaledLDLWeightsNonnegative : AllWeightsNonnegative scaledLDLFamiliesZ
scaledLDLWeightsNonnegative =
  all∷ U.nonNeg (all∷ U.nonNeg (all∷ U.nonNeg (all∷ U.nonNeg
  (all∷ U.nonNeg (all∷ U.nonNeg (all∷ U.nonNeg (all∷ U.nonNeg
  (all∷ U.nonNeg (all∷ U.nonNeg (all∷ U.nonNeg (all∷ U.nonNeg all[]))))))))))))

------------------------------------------------------------------------
-- Certificate equality and order extraction in ℚᵘ.
------------------------------------------------------------------------

scaleKU scaleMU eighteenU oneEighteenthU : ℚᵘ
scaleKU = C.embedZ scaleKZ
scaleMU = C.embedZ scaleMZ
eighteenU = (+ 18) /ᵘ 1
oneEighteenthU = (+ 1) /ᵘ 18

instance
  scaleKUPositive : Positive scaleKU
  scaleKUPositive = U.pos
  eighteenUPositive : Positive eighteenU
  eighteenUPositive = U.pos

negativeScaleKEmbedding :
  C.embedZ (neg 70100214151882488833120838983750438907686861074695467566355130758678976489785281281004080)
  ≃ -ᵘ scaleKU
negativeScaleKEmbedding = UP.≃-reflexive refl

scaledGapEval : ∀ c →
  C.evalTriZU scaledGapTriZ (coordinatesU c)
  ≃ scaleMU *ᵘ RP.toℚᵘ (path13Energy c)
    +ᵘ (-ᵘ scaleKU) *ᵘ RP.toℚᵘ (path13NormSq c)
scaledGapEval c =
  UP.≃-trans
    (C.evalAddZU
      (QuadZ.scaleTriZ scaleMZ energyTriZ)
      (QuadZ.scaleTriZ
        (neg 70100214151882488833120838983750438907686861074695467566355130758678976489785281281004080)
        normTriZ)
      (coordinatesU c))
    (UP.+-cong
      (UP.≃-trans
        (C.evalScaleZU scaleMZ energyTriZ (coordinatesU c))
        (UP.*-cong UP.≃-refl (energyEvalToQ c)))
      (UP.≃-trans
        (C.evalScaleZU
          (neg 70100214151882488833120838983750438907686861074695467566355130758678976489785281281004080)
          normTriZ
          (coordinatesU c))
        (UP.*-cong negativeScaleKEmbedding (normEvalToQ c))))
  where
  import DASHI.Physics.YangMills.BalabanIntegerTriangularQuadraticCertificateExact as QuadZ

scaledLDLEval : ∀ c →
  C.evalTriZU scaledLDLTriZ (coordinatesU c)
  ≃ C.sumWeightedSquareValuesZU scaledLDLFamiliesZ (coordinatesU c)
scaledLDLEval c = C.sumWeightedSquareCompilerZU scaledLDLFamiliesZ (coordinatesU c)

scaledGapToResidual : ∀ c →
  scaleMU *ᵘ RP.toℚᵘ (path13Energy c)
    +ᵘ (-ᵘ scaleKU) *ᵘ RP.toℚᵘ (path13NormSq c)
  ≃ C.sumWeightedSquareValuesZU scaledLDLFamiliesZ (coordinatesU c)
scaledGapToResidual c =
  UP.≃-trans
    (UP.≃-sym (scaledGapEval c))
    (UP.≃-trans
      (UP.≃-reflexive
        (cong (λ quadratic → C.evalTriZU quadratic (coordinatesU c))
          scaledIntegerCoefficientCertificate))
      (scaledLDLEval c))

scaledGapNonnegative : ∀ c →
  0ℚᵘ ≤ᵘ
    scaleMU *ᵘ RP.toℚᵘ (path13Energy c)
      +ᵘ (-ᵘ scaleKU) *ᵘ RP.toℚᵘ (path13NormSq c)
scaledGapNonnegative c =
  UP.≤-respʳ-≃
    (UP.≃-sym (scaledGapToResidual c))
    (sumWeightedNonnegativeU scaledLDLWeightsNonnegative (coordinatesU c))

gapAsDifference : ∀ energyValue normValue →
  scaleMU *ᵘ energyValue +ᵘ (-ᵘ scaleKU) *ᵘ normValue
  ≃ scaleMU *ᵘ energyValue +ᵘ (-ᵘ (scaleKU *ᵘ normValue))
gapAsDifference = URing.solve-∀

scaleKTimesNormBelowScaleMTimesEnergy : ∀ c →
  scaleKU *ᵘ RP.toℚᵘ (path13NormSq c)
  ≤ᵘ scaleMU *ᵘ RP.toℚᵘ (path13Energy c)
scaleKTimesNormBelowScaleMTimesEnergy c =
  UP.0≤q-p⇒p≤q
    (UP.≤-respʳ-≃
      (gapAsDifference
        (RP.toℚᵘ (path13Energy c))
        (RP.toℚᵘ (path13NormSq c)))
      (scaledGapNonnegative c))

scaleMFactorZ : scaleMZ ≡ scaleKZ * (+ 18)
scaleMFactorZ = refl

scaleMFactorU : scaleMU ≃ scaleKU *ᵘ eighteenU
scaleMFactorU =
  UP.≃-reflexive
    (trans
      (cong C.embedZ scaleMFactorZ)
      (C.embedZ-* scaleKZ (+ 18)))

factorScaleM : ∀ energyValue →
  scaleMU *ᵘ energyValue
  ≃ scaleKU *ᵘ (eighteenU *ᵘ energyValue)
factorScaleM energyValue =
  UP.≃-trans
    (UP.*-cong scaleMFactorU UP.≃-refl)
    (UP.*-assoc scaleKU eighteenU energyValue)

normBelowEighteenEnergy : ∀ c →
  RP.toℚᵘ (path13NormSq c)
  ≤ᵘ eighteenU *ᵘ RP.toℚᵘ (path13Energy c)
normBelowEighteenEnergy c =
  UP.*-cancelˡ-≤-pos scaleKU
    (UP.≤-respʳ-≃
      (factorScaleM (RP.toℚᵘ (path13Energy c)))
      (scaleKTimesNormBelowScaleMTimesEnergy c))

eighteenUndo : ∀ x →
  eighteenU *ᵘ (oneEighteenthU *ᵘ x) ≃ x
eighteenUndo = URing.solve-∀

oneEighteenthNormBelowEnergyU : ∀ c →
  oneEighteenthU *ᵘ RP.toℚᵘ (path13NormSq c)
  ≤ᵘ RP.toℚᵘ (path13Energy c)
oneEighteenthNormBelowEnergyU c =
  UP.*-cancelˡ-≤-pos eighteenU
    (UP.≤-respˡ-≃
      (UP.≃-sym (eighteenUndo (RP.toℚᵘ (path13NormSq c))))
      (normBelowEighteenEnergy c))

oneEighteenthToU : RP.toℚᵘ oneEighteenth ≃ oneEighteenthU
oneEighteenthToU = UP.≃-reflexive refl

normalizedLeftToU : ∀ c →
  RP.toℚᵘ (oneEighteenth * path13NormSq c)
  ≃ oneEighteenthU *ᵘ RP.toℚᵘ (path13NormSq c)
normalizedLeftToU c =
  UP.≃-trans
    (RP.toℚᵘ-homo-* oneEighteenth (path13NormSq c))
    (UP.*-cong oneEighteenthToU UP.≃-refl)

path13Poincare : ∀ c → oneEighteenth * path13NormSq c ≤ path13Energy c
path13Poincare c =
  RP.toℚᵘ-cancel-≤
    (UP.≤-respˡ-≃
      (UP.≃-sym (normalizedLeftToU c))
      (oneEighteenthNormBelowEnergyU c))

path13NativeIntegerCertificateLevel : ProofLevel
path13NativeIntegerCertificateLevel = machineChecked
