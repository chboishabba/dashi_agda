module DASHI.Physics.YangMills.BalabanPath13NativeIntegerAttachmentExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_)
import Data.Rational.Properties as RP
open import Data.Rational.Unnormalised.Base
  using (ℚᵘ; 0ℚᵘ; _≃_)
  renaming (_+_ to _+ᵘ_; _*_ to _*ᵘ_; -_ to -ᵘ_)
import Data.Rational.Unnormalised.Properties as UP
import Data.Rational.Unnormalised.Tactic.RingSolver as URing
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq; sqDiff)
open import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLDataExact
open import DASHI.Physics.YangMills.BalabanPath13NativeIntegerCoefficientDataExact
import DASHI.Physics.YangMills.BalabanIntegerTriangularUnnormalisedCompilerExact as C

------------------------------------------------------------------------
-- Small normalized-Q -> unnormalised-Q transport.
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
squareIntoQ {q = q} u≈q =
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
  RP.toℚᵘ (lastCoordinate c) ≃ -ᵘ (sumU (coordinatesU c))
lastCoordinateToU c =
  UP.≃-trans
    (RP.toℚᵘ-cong (lastCoordinateAsSum c))
    (UP.≃-trans
      (RP.toℚᵘ-homo‿- (sumQ (coordinateTermsQ c)))
      (UP.-‿cong (toSumU (coordinateTermsQ c))))

------------------------------------------------------------------------
-- Degree-one attachment.  These are the only 12-coordinate solver calls.
------------------------------------------------------------------------

energy0Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy0CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ b +ᵘ (-ᵘ RP.toℚᵘ a)
energy0Raw = URing.solve-∀
energy1Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy1CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ c +ᵘ (-ᵘ RP.toℚᵘ b)
energy1Raw = URing.solve-∀
energy2Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy2CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ d +ᵘ (-ᵘ RP.toℚᵘ c)
energy2Raw = URing.solve-∀
energy3Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy3CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ e +ᵘ (-ᵘ RP.toℚᵘ d)
energy3Raw = URing.solve-∀
energy4Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy4CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ f +ᵘ (-ᵘ RP.toℚᵘ e)
energy4Raw = URing.solve-∀
energy5Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy5CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ g +ᵘ (-ᵘ RP.toℚᵘ f)
energy5Raw = URing.solve-∀
energy6Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy6CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ h +ᵘ (-ᵘ RP.toℚᵘ g)
energy6Raw = URing.solve-∀
energy7Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy7CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ i +ᵘ (-ᵘ RP.toℚᵘ h)
energy7Raw = URing.solve-∀
energy8Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy8CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ j +ᵘ (-ᵘ RP.toℚᵘ i)
energy8Raw = URing.solve-∀
energy9Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy9CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ k +ᵘ (-ᵘ RP.toℚᵘ j)
energy9Raw = URing.solve-∀
energy10Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy10CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ l +ᵘ (-ᵘ RP.toℚᵘ k)
energy10Raw = URing.solve-∀
energy11Raw : ∀ a b c d e f g h i j k l →
  C.dotZU energy11CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ -ᵘ (sumU (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ [])) +ᵘ (-ᵘ RP.toℚᵘ l)
energy11Raw = URing.solve-∀

energyLinear0U : ∀ c → C.dotZU energy0CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y1 c - y0 c)
energyLinear0U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy0Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU b a))
energyLinear1U : ∀ c → C.dotZU energy1CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y2 c - y1 c)
energyLinear1U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy1Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU c b))
energyLinear2U : ∀ c → C.dotZU energy2CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y3 c - y2 c)
energyLinear2U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy2Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU d c))
energyLinear3U : ∀ c → C.dotZU energy3CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y4 c - y3 c)
energyLinear3U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy3Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU e d))
energyLinear4U : ∀ c → C.dotZU energy4CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y5 c - y4 c)
energyLinear4U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy4Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU f e))
energyLinear5U : ∀ c → C.dotZU energy5CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y6 c - y5 c)
energyLinear5U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy5Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU g f))
energyLinear6U : ∀ c → C.dotZU energy6CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y7 c - y6 c)
energyLinear6U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy6Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU h g))
energyLinear7U : ∀ c → C.dotZU energy7CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y8 c - y7 c)
energyLinear7U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy7Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU i h))
energyLinear8U : ∀ c → C.dotZU energy8CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y9 c - y8 c)
energyLinear8U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy8Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU j i))
energyLinear9U : ∀ c → C.dotZU energy9CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y10 c - y9 c)
energyLinear9U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy9Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU k j))
energyLinear10U : ∀ c → C.dotZU energy10CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y11 c - y10 c)
energyLinear10U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy10Raw a b c d e f g h i j k l) (UP.≃-sym (toSubU l k))
energyLinear11U : ∀ c → C.dotZU energy11CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (lastCoordinate c - y11 c)
energyLinear11U p@(path13Coordinates a b c d e f g h i j k l) =
  UP.≃-trans
    (energy11Raw a b c d e f g h i j k l)
    (UP.≃-trans
      (UP.+-cong (UP.≃-sym (lastCoordinateToU p)) UP.≃-refl)
      (UP.≃-sym (toSubU (lastCoordinate p) l)))

------------------------------------------------------------------------
-- Norm basis rows.  Kept as explicit Raw owners so solve-∀ is never used as
-- an ordinary function call.
------------------------------------------------------------------------

norm0Raw : ∀ a b c d e f g h i j k l → C.dotZU norm0CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ a
norm0Raw = URing.solve-∀
norm1Raw : ∀ a b c d e f g h i j k l → C.dotZU norm1CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ b
norm1Raw = URing.solve-∀
norm2Raw : ∀ a b c d e f g h i j k l → C.dotZU norm2CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ c
norm2Raw = URing.solve-∀
norm3Raw : ∀ a b c d e f g h i j k l → C.dotZU norm3CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ d
norm3Raw = URing.solve-∀
norm4Raw : ∀ a b c d e f g h i j k l → C.dotZU norm4CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ e
norm4Raw = URing.solve-∀
norm5Raw : ∀ a b c d e f g h i j k l → C.dotZU norm5CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ f
norm5Raw = URing.solve-∀
norm6Raw : ∀ a b c d e f g h i j k l → C.dotZU norm6CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ g
norm6Raw = URing.solve-∀
norm7Raw : ∀ a b c d e f g h i j k l → C.dotZU norm7CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ h
norm7Raw = URing.solve-∀
norm8Raw : ∀ a b c d e f g h i j k l → C.dotZU norm8CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ i
norm8Raw = URing.solve-∀
norm9Raw : ∀ a b c d e f g h i j k l → C.dotZU norm9CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ j
norm9Raw = URing.solve-∀
norm10Raw : ∀ a b c d e f g h i j k l → C.dotZU norm10CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ k
norm10Raw = URing.solve-∀
norm11Raw : ∀ a b c d e f g h i j k l → C.dotZU norm11CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ RP.toℚᵘ l
norm11Raw = URing.solve-∀
norm12Raw : ∀ a b c d e f g h i j k l → C.dotZU norm12CoefficientsZ (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []) ≃ -ᵘ (sumU (RP.toℚᵘ a ∷ RP.toℚᵘ b ∷ RP.toℚᵘ c ∷ RP.toℚᵘ d ∷ RP.toℚᵘ e ∷ RP.toℚᵘ f ∷ RP.toℚᵘ g ∷ RP.toℚᵘ h ∷ RP.toℚᵘ i ∷ RP.toℚᵘ j ∷ RP.toℚᵘ k ∷ RP.toℚᵘ l ∷ []))
norm12Raw = URing.solve-∀

normLinear0U : ∀ c → C.dotZU norm0CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y0 c)
normLinear0U (path13Coordinates a b c d e f g h i j k l) = norm0Raw a b c d e f g h i j k l
normLinear1U : ∀ c → C.dotZU norm1CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y1 c)
normLinear1U (path13Coordinates a b c d e f g h i j k l) = norm1Raw a b c d e f g h i j k l
normLinear2U : ∀ c → C.dotZU norm2CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y2 c)
normLinear2U (path13Coordinates a b c d e f g h i j k l) = norm2Raw a b c d e f g h i j k l
normLinear3U : ∀ c → C.dotZU norm3CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y3 c)
normLinear3U (path13Coordinates a b c d e f g h i j k l) = norm3Raw a b c d e f g h i j k l
normLinear4U : ∀ c → C.dotZU norm4CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y4 c)
normLinear4U (path13Coordinates a b c d e f g h i j k l) = norm4Raw a b c d e f g h i j k l
normLinear5U : ∀ c → C.dotZU norm5CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y5 c)
normLinear5U (path13Coordinates a b c d e f g h i j k l) = norm5Raw a b c d e f g h i j k l
normLinear6U : ∀ c → C.dotZU norm6CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y6 c)
normLinear6U (path13Coordinates a b c d e f g h i j k l) = norm6Raw a b c d e f g h i j k l
normLinear7U : ∀ c → C.dotZU norm7CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y7 c)
normLinear7U (path13Coordinates a b c d e f g h i j k l) = norm7Raw a b c d e f g h i j k l
normLinear8U : ∀ c → C.dotZU norm8CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y8 c)
normLinear8U (path13Coordinates a b c d e f g h i j k l) = norm8Raw a b c d e f g h i j k l
normLinear9U : ∀ c → C.dotZU norm9CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y9 c)
normLinear9U (path13Coordinates a b c d e f g h i j k l) = norm9Raw a b c d e f g h i j k l
normLinear10U : ∀ c → C.dotZU norm10CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y10 c)
normLinear10U (path13Coordinates a b c d e f g h i j k l) = norm10Raw a b c d e f g h i j k l
normLinear11U : ∀ c → C.dotZU norm11CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (y11 c)
normLinear11U (path13Coordinates a b c d e f g h i j k l) = norm11Raw a b c d e f g h i j k l
normLinear12U : ∀ c → C.dotZU norm12CoefficientsZ (coordinatesU c) ≃ RP.toℚᵘ (lastCoordinate c)
normLinear12U p@(path13Coordinates a b c d e f g h i j k l) =
  UP.≃-trans (norm12Raw a b c d e f g h i j k l) (UP.≃-sym (lastCoordinateToU p))

------------------------------------------------------------------------
-- Structural square/sum attachment to the literal Path13 energy and norm.
------------------------------------------------------------------------

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

energyValuesToTerms : ∀ c → C.sumSquareValuesZU energyFamiliesZ (coordinatesU c) ≃ sumU (toListU (energyTermsQ c))
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

normValuesToTerms : ∀ c → C.sumSquareValuesZU normFamiliesZ (coordinatesU c) ≃ sumU (toListU (normTermsQ c))
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

energyEvalToQ : ∀ c → C.evalTriZU energyTriZ (coordinatesU c) ≃ RP.toℚᵘ (path13Energy c)
energyEvalToQ c =
  UP.≃-trans
    (C.sumSquareCompilerZU energyFamiliesZ (coordinatesU c))
    (UP.≃-trans
      (energyValuesToTerms c)
      (UP.≃-trans
        (UP.≃-sym (toSumU (energyTermsQ c)))
        (RP.toℚᵘ-cong (energySumExact c))))

normEvalToQ : ∀ c → C.evalTriZU normTriZ (coordinatesU c) ≃ RP.toℚᵘ (path13NormSq c)
normEvalToQ c =
  UP.≃-trans
    (C.sumSquareCompilerZU normFamiliesZ (coordinatesU c))
    (UP.≃-trans
      (normValuesToTerms c)
      (UP.≃-trans
        (UP.≃-sym (toSumU (normTermsQ c)))
        (RP.toℚᵘ-cong (normSumExact c))))
