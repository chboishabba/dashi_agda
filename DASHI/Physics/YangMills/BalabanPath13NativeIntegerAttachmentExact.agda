module DASHI.Physics.YangMills.BalabanPath13NativeIntegerAttachmentExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer using (ℤ)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_; toℚᵘ)
import Data.Rational.Properties as RP
open import Data.Rational.Unnormalised.Base
  using (ℚᵘ; 0ℚᵘ; 1ℚᵘ; _≃_)
  renaming (_+_ to _+ᵘ_; _*_ to _*ᵘ_; -_ to -ᵘ_)
import Data.Rational.Unnormalised.Properties as UP
import Data.Rational.Unnormalised.Tactic.RingSolver as URing
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate using (sq)
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
toListU (x ∷ xs) = toℚᵘ x ∷ toListU xs

toSumU : ∀ xs → toℚᵘ (sumQ xs) ≃ sumU (toListU xs)
toSumU [] = UP.≃-refl {0ℚᵘ}
toSumU (x ∷ xs) =
  UP.≃-trans
    (RP.toℚᵘ-homo-+ x (sumQ xs))
    (UP.+-cong (UP.≃-refl {toℚᵘ x}) (toSumU xs))

toSubU : ∀ p q →
  toℚᵘ (p - q) ≃ toℚᵘ p +ᵘ (-ᵘ toℚᵘ q)
toSubU p q =
  UP.≃-trans
    (RP.toℚᵘ-homo-+ p (- q))
    (UP.+-cong (UP.≃-refl {toℚᵘ p}) (RP.toℚᵘ-homo‿- q))

squareIntoQ : ∀ {u q} →
  u ≃ toℚᵘ q →
  u *ᵘ u ≃ toℚᵘ (q * q)
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
     (y6 c + (y7 c + (y8 c + (y9 c + (y10 c + y11 c))))))))))
coordinateSumExact c rewrite RP.+-identityʳ (y11 c) = refl

lastCoordinateAsSum : ∀ c →
  lastCoordinate c ≡ - (sumQ (coordinateTermsQ c))
lastCoordinateAsSum c = cong -_ (sym (coordinateSumExact c))

lastCoordinateToU : ∀ c →
  toℚᵘ (lastCoordinate c) ≃ -ᵘ (sumU (coordinatesU c))
lastCoordinateToU c =
  UP.≃-trans
    (RP.toℚᵘ-cong (lastCoordinateAsSum c))
    (UP.≃-trans
      (RP.toℚᵘ-homo‿- (sumQ (coordinateTermsQ c)))
      (UP.-‿cong (toSumU (coordinateTermsQ c))))

------------------------------------------------------------------------
-- Exact degree-one reduction steps for C.dotZU.
------------------------------------------------------------------------

zeroDotStep : ∀ x d → 0ℚᵘ *ᵘ x +ᵘ d ≃ d
zeroDotStep = URing.solve-∀

oneDotStep : ∀ x d → 1ℚᵘ *ᵘ x +ᵘ d ≃ x +ᵘ d
oneDotStep = URing.solve-∀

negOneDotStep : ∀ x d → (-ᵘ 1ℚᵘ) *ᵘ x +ᵘ d ≃ (-ᵘ x) +ᵘ d
negOneDotStep = URing.solve-∀

negTwoDotStep : ∀ x d → ((-ᵘ 1ℚᵘ) +ᵘ (-ᵘ 1ℚᵘ)) *ᵘ x +ᵘ d ≃ (-ᵘ x) +ᵘ ((-ᵘ x) +ᵘ d)
negTwoDotStep = URing.solve-∀

plusZero : ∀ x → x +ᵘ 0ℚᵘ ≃ x
plusZero = URing.solve-∀

plusComm : ∀ x y → x +ᵘ y ≃ y +ᵘ x
plusComm = URing.solve-∀

negDistrib : ∀ x y → -ᵘ (x +ᵘ y) ≃ (-ᵘ x) +ᵘ (-ᵘ y)
negDistrib = URing.solve-∀

negZero : -ᵘ 0ℚᵘ ≃ 0ℚᵘ
negZero = URing.solve-∀

energy11BaseLemma : ∀ u → (-ᵘ u) +ᵘ ((-ᵘ u) +ᵘ 0ℚᵘ) ≃ (-ᵘ (u +ᵘ 0ℚᵘ)) +ᵘ (-ᵘ u)
energy11BaseLemma = URing.solve-∀

energy11StepLemma : ∀ x s t → (-ᵘ x) +ᵘ ((-ᵘ s) +ᵘ t) ≃ (-ᵘ (x +ᵘ s)) +ᵘ t
energy11StepLemma = URing.solve-∀

dotStep0 : ∀ x {as xs} → C.dotZU (zeroZ ∷ as) (x ∷ xs) ≃ C.dotZU as xs
dotStep0 x {as} {xs} = zeroDotStep x (C.dotZU as xs)

dotStep1 : ∀ x {as xs} → C.dotZU (pos 1 ∷ as) (x ∷ xs) ≃ x +ᵘ C.dotZU as xs
dotStep1 x {as} {xs} = oneDotStep x (C.dotZU as xs)

dotStep-1 : ∀ x {as xs} → C.dotZU (neg 1 ∷ as) (x ∷ xs) ≃ (-ᵘ x) +ᵘ C.dotZU as xs
dotStep-1 x {as} {xs} = negOneDotStep x (C.dotZU as xs)

dotStep-2 : ∀ x {as xs} → C.dotZU (neg 2 ∷ as) (x ∷ xs) ≃ (-ᵘ x) +ᵘ ((-ᵘ x) +ᵘ C.dotZU as xs)
dotStep-2 x {as} {xs} = negTwoDotStep x (C.dotZU as xs)

dotZeros : ∀ {as xs} → C.dotZU as xs ≃ 0ℚᵘ → ∀ x → C.dotZU (zeroZ ∷ as) (x ∷ xs) ≃ 0ℚᵘ
dotZeros {as} {xs} zRec x = UP.≃-trans (dotStep0 x {as} {xs}) zRec

z0 : C.dotZU [] [] ≃ 0ℚᵘ
z0 = UP.≃-refl {0ℚᵘ}

z1 : ∀ x0 → C.dotZU (zeroZ ∷ []) (x0 ∷ []) ≃ 0ℚᵘ
z1 x0 = dotZeros {[]} {[]} z0 x0

z2 : ∀ x0 x1 → C.dotZU (zeroZ ∷ zeroZ ∷ []) (x0 ∷ x1 ∷ []) ≃ 0ℚᵘ
z2 x0 x1 = dotZeros {zeroZ ∷ []} {x1 ∷ []} (z1 x1) x0

z3 : ∀ x0 x1 x2 → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ []) (x0 ∷ x1 ∷ x2 ∷ []) ≃ 0ℚᵘ
z3 x0 x1 x2 = dotZeros {zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ []} (z2 x1 x2) x0

z4 : ∀ x0 x1 x2 x3 → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ []) ≃ 0ℚᵘ
z4 x0 x1 x2 x3 = dotZeros {zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ []} (z3 x1 x2 x3) x0

z5 : ∀ x0 x1 x2 x3 x4 → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ []) ≃ 0ℚᵘ
z5 x0 x1 x2 x3 x4 = dotZeros {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ []} (z4 x1 x2 x3 x4) x0

z6 : ∀ x0 x1 x2 x3 x4 x5 → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ []) ≃ 0ℚᵘ
z6 x0 x1 x2 x3 x4 x5 = dotZeros {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ []} (z5 x1 x2 x3 x4 x5) x0

z7 : ∀ x0 x1 x2 x3 x4 x5 x6 → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ []) ≃ 0ℚᵘ
z7 x0 x1 x2 x3 x4 x5 x6 = dotZeros {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ []} (z6 x1 x2 x3 x4 x5 x6) x0

z8 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ []) ≃ 0ℚᵘ
z8 x0 x1 x2 x3 x4 x5 x6 x7 = dotZeros {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ []} (z7 x1 x2 x3 x4 x5 x6 x7) x0

z9 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ []) ≃ 0ℚᵘ
z9 x0 x1 x2 x3 x4 x5 x6 x7 x8 = dotZeros {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ []} (z8 x1 x2 x3 x4 x5 x6 x7 x8) x0

z10 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ []) ≃ 0ℚᵘ
z10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 = dotZeros {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ []} (z9 x1 x2 x3 x4 x5 x6 x7 x8 x9) x0

z11 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ []) ≃ 0ℚᵘ
z11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 = dotZeros {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ []} (z10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) x0

norm11Tail : List ℤ
norm11Tail = pos 1 ∷ []

norm10Tail : List ℤ
norm10Tail = pos 1 ∷ zeroZ ∷ []

norm9Tail : List ℤ
norm9Tail = pos 1 ∷ zeroZ ∷ zeroZ ∷ []

norm8Tail : List ℤ
norm8Tail = pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

norm7Tail : List ℤ
norm7Tail = pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

norm6Tail : List ℤ
norm6Tail = pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

norm5Tail : List ℤ
norm5Tail = pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

norm4Tail : List ℤ
norm4Tail = pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

norm3Tail : List ℤ
norm3Tail = pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

norm2Tail : List ℤ
norm2Tail = pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

norm1Tail : List ℤ
norm1Tail = pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

norm0Tail : List ℤ
norm0Tail = pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

energy10Tail : List ℤ
energy10Tail = neg 1 ∷ pos 1 ∷ []

energy9Tail : List ℤ
energy9Tail = neg 1 ∷ pos 1 ∷ zeroZ ∷ []

energy8Tail : List ℤ
energy8Tail = neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ []

energy7Tail : List ℤ
energy7Tail = neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

energy6Tail : List ℤ
energy6Tail = neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

energy5Tail : List ℤ
energy5Tail = neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

energy4Tail : List ℤ
energy4Tail = neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

energy3Tail : List ℤ
energy3Tail = neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

energy2Tail : List ℤ
energy2Tail = neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

energy1Tail : List ℤ
energy1Tail = neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

energy0Tail : List ℤ
energy0Tail = neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []

oz0 : ∀ x → C.dotZU norm11Tail (x ∷ []) ≃ x
oz0 x = UP.≃-trans (dotStep1 x {[]} {[]}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x}) z0) (plusZero x))

oz1 : ∀ x0 x1 → C.dotZU norm10Tail (x0 ∷ x1 ∷ []) ≃ x0
oz1 x0 x1 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ []} {x1 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z1 x1)) (plusZero x0))

oz2 : ∀ x0 x1 x2 → C.dotZU norm9Tail (x0 ∷ x1 ∷ x2 ∷ []) ≃ x0
oz2 x0 x1 x2 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z2 x1 x2)) (plusZero x0))

oz3 : ∀ x0 x1 x2 x3 → C.dotZU norm8Tail (x0 ∷ x1 ∷ x2 ∷ x3 ∷ []) ≃ x0
oz3 x0 x1 x2 x3 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z3 x1 x2 x3)) (plusZero x0))

oz4 : ∀ x0 x1 x2 x3 x4 → C.dotZU norm7Tail (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ []) ≃ x0
oz4 x0 x1 x2 x3 x4 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z4 x1 x2 x3 x4)) (plusZero x0))

oz5 : ∀ x0 x1 x2 x3 x4 x5 → C.dotZU norm6Tail (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ []) ≃ x0
oz5 x0 x1 x2 x3 x4 x5 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z5 x1 x2 x3 x4 x5)) (plusZero x0))

oz6 : ∀ x0 x1 x2 x3 x4 x5 x6 → C.dotZU norm5Tail (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ []) ≃ x0
oz6 x0 x1 x2 x3 x4 x5 x6 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z6 x1 x2 x3 x4 x5 x6)) (plusZero x0))

oz7 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 → C.dotZU norm4Tail (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ []) ≃ x0
oz7 x0 x1 x2 x3 x4 x5 x6 x7 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z7 x1 x2 x3 x4 x5 x6 x7)) (plusZero x0))

oz8 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 → C.dotZU norm3Tail (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ []) ≃ x0
oz8 x0 x1 x2 x3 x4 x5 x6 x7 x8 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z8 x1 x2 x3 x4 x5 x6 x7 x8)) (plusZero x0))

oz9 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 → C.dotZU norm2Tail (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ []) ≃ x0
oz9 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z9 x1 x2 x3 x4 x5 x6 x7 x8 x9)) (plusZero x0))

oz10 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 → C.dotZU norm1Tail (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ []) ≃ x0
oz10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) (plusZero x0))

oz11 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 → C.dotZU norm0Tail (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ []) ≃ x0
oz11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 = UP.≃-trans (dotStep1 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ []}) (UP.≃-trans (UP.+-cong (UP.≃-refl {x0}) (z11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)) (plusZero x0))

ep0 : ∀ x y → C.dotZU energy10Tail (x ∷ y ∷ []) ≃ y +ᵘ (-ᵘ x)
ep0 x y =
  UP.≃-trans (dotStep-1 x {norm11Tail} {y ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz0 y))
      (plusComm (-ᵘ x) y))

ep1 : ∀ x y z0 → C.dotZU energy9Tail (x ∷ y ∷ z0 ∷ []) ≃ y +ᵘ (-ᵘ x)
ep1 x y z0 =
  UP.≃-trans (dotStep-1 x {norm10Tail} {y ∷ z0 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz1 y z0))
      (plusComm (-ᵘ x) y))

ep2 : ∀ x y z0 z1 → C.dotZU energy8Tail (x ∷ y ∷ z0 ∷ z1 ∷ []) ≃ y +ᵘ (-ᵘ x)
ep2 x y z0 z1 =
  UP.≃-trans (dotStep-1 x {norm9Tail} {y ∷ z0 ∷ z1 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz2 y z0 z1))
      (plusComm (-ᵘ x) y))

ep3 : ∀ x y z0 z1 z2 → C.dotZU energy7Tail (x ∷ y ∷ z0 ∷ z1 ∷ z2 ∷ []) ≃ y +ᵘ (-ᵘ x)
ep3 x y z0 z1 z2 =
  UP.≃-trans (dotStep-1 x {norm8Tail} {y ∷ z0 ∷ z1 ∷ z2 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz3 y z0 z1 z2))
      (plusComm (-ᵘ x) y))

ep4 : ∀ x y z0 z1 z2 z3 → C.dotZU energy6Tail (x ∷ y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ []) ≃ y +ᵘ (-ᵘ x)
ep4 x y z0 z1 z2 z3 =
  UP.≃-trans (dotStep-1 x {norm7Tail} {y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz4 y z0 z1 z2 z3))
      (plusComm (-ᵘ x) y))

ep5 : ∀ x y z0 z1 z2 z3 z4 → C.dotZU energy5Tail (x ∷ y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ []) ≃ y +ᵘ (-ᵘ x)
ep5 x y z0 z1 z2 z3 z4 =
  UP.≃-trans (dotStep-1 x {norm6Tail} {y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz5 y z0 z1 z2 z3 z4))
      (plusComm (-ᵘ x) y))

ep6 : ∀ x y z0 z1 z2 z3 z4 z5 → C.dotZU energy4Tail (x ∷ y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ []) ≃ y +ᵘ (-ᵘ x)
ep6 x y z0 z1 z2 z3 z4 z5 =
  UP.≃-trans (dotStep-1 x {norm5Tail} {y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz6 y z0 z1 z2 z3 z4 z5))
      (plusComm (-ᵘ x) y))

ep7 : ∀ x y z0 z1 z2 z3 z4 z5 z6 → C.dotZU energy3Tail (x ∷ y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ []) ≃ y +ᵘ (-ᵘ x)
ep7 x y z0 z1 z2 z3 z4 z5 z6 =
  UP.≃-trans (dotStep-1 x {norm4Tail} {y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz7 y z0 z1 z2 z3 z4 z5 z6))
      (plusComm (-ᵘ x) y))

ep8 : ∀ x y z0 z1 z2 z3 z4 z5 z6 z7 → C.dotZU energy2Tail (x ∷ y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ []) ≃ y +ᵘ (-ᵘ x)
ep8 x y z0 z1 z2 z3 z4 z5 z6 z7 =
  UP.≃-trans (dotStep-1 x {norm3Tail} {y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz8 y z0 z1 z2 z3 z4 z5 z6 z7))
      (plusComm (-ᵘ x) y))

ep9 : ∀ x y z0 z1 z2 z3 z4 z5 z6 z7 z8 → C.dotZU energy1Tail (x ∷ y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ z8 ∷ []) ≃ y +ᵘ (-ᵘ x)
ep9 x y z0 z1 z2 z3 z4 z5 z6 z7 z8 =
  UP.≃-trans (dotStep-1 x {norm2Tail} {y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ z8 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz9 y z0 z1 z2 z3 z4 z5 z6 z7 z8))
      (plusComm (-ᵘ x) y))

ep10 : ∀ x y z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 → C.dotZU energy0Tail (x ∷ y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ z8 ∷ z9 ∷ []) ≃ y +ᵘ (-ᵘ x)
ep10 x y z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 =
  UP.≃-trans (dotStep-1 x {norm1Tail} {y ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z6 ∷ z7 ∷ z8 ∷ z9 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ x }) (oz10 y z0 z1 z2 z3 z4 z5 z6 z7 z8 z9))
      (plusComm (-ᵘ x) y))

strip1 : ∀ x as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ as) (x ∷ xs) ≃ v
strip1 x as xs rec = UP.≃-trans (dotStep0 x {as} {xs}) rec

strip2 : ∀ x0 x1 as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ zeroZ ∷ as) (x0 ∷ x1 ∷ xs) ≃ v
strip2 x0 x1 as xs rec = UP.≃-trans (dotStep0 x0 {zeroZ ∷ as} {x1 ∷ xs}) (strip1 x1 as xs rec)

strip3 : ∀ x0 x1 x2 as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ as) (x0 ∷ x1 ∷ x2 ∷ xs) ≃ v
strip3 x0 x1 x2 as xs rec = UP.≃-trans (dotStep0 x0 {zeroZ ∷ zeroZ ∷ as} {x1 ∷ x2 ∷ xs}) (strip2 x1 x2 as xs rec)

strip4 : ∀ x0 x1 x2 x3 as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ xs) ≃ v
strip4 x0 x1 x2 x3 as xs rec = UP.≃-trans (dotStep0 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ as} {x1 ∷ x2 ∷ x3 ∷ xs}) (strip3 x1 x2 x3 as xs rec)

strip5 : ∀ x0 x1 x2 x3 x4 as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ xs) ≃ v
strip5 x0 x1 x2 x3 x4 as xs rec = UP.≃-trans (dotStep0 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ xs}) (strip4 x1 x2 x3 x4 as xs rec)

strip6 : ∀ x0 x1 x2 x3 x4 x5 as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ xs) ≃ v
strip6 x0 x1 x2 x3 x4 x5 as xs rec = UP.≃-trans (dotStep0 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ xs}) (strip5 x1 x2 x3 x4 x5 as xs rec)

strip7 : ∀ x0 x1 x2 x3 x4 x5 x6 as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ xs) ≃ v
strip7 x0 x1 x2 x3 x4 x5 x6 as xs rec = UP.≃-trans (dotStep0 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ xs}) (strip6 x1 x2 x3 x4 x5 x6 as xs rec)

strip8 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ xs) ≃ v
strip8 x0 x1 x2 x3 x4 x5 x6 x7 as xs rec = UP.≃-trans (dotStep0 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ xs}) (strip7 x1 x2 x3 x4 x5 x6 x7 as xs rec)

strip9 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ xs) ≃ v
strip9 x0 x1 x2 x3 x4 x5 x6 x7 x8 as xs rec = UP.≃-trans (dotStep0 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ xs}) (strip8 x1 x2 x3 x4 x5 x6 x7 x8 as xs rec)

strip10 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ xs) ≃ v
strip10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 as xs rec = UP.≃-trans (dotStep0 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ xs}) (strip9 x1 x2 x3 x4 x5 x6 x7 x8 x9 as xs rec)

strip11 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 as xs {v} → C.dotZU as xs ≃ v → C.dotZU (zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as) (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ xs) ≃ v
strip11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 as xs rec = UP.≃-trans (dotStep0 x0 {zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ as} {x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ xs}) (strip10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 as xs rec)

energy0Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy0CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u1 +ᵘ (-ᵘ u0)
energy0Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = ep10 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

energy1Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy1CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u2 +ᵘ (-ᵘ u1)
energy1Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip1 u0 energy1Tail (u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (ep9 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11)

energy2Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy2CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u3 +ᵘ (-ᵘ u2)
energy2Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip2 u0 u1 energy2Tail (u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (ep8 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11)

energy3Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy3CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u4 +ᵘ (-ᵘ u3)
energy3Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip3 u0 u1 u2 energy3Tail (u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (ep7 u3 u4 u5 u6 u7 u8 u9 u10 u11)

energy4Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy4CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u5 +ᵘ (-ᵘ u4)
energy4Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip4 u0 u1 u2 u3 energy4Tail (u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (ep6 u4 u5 u6 u7 u8 u9 u10 u11)

energy5Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy5CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u6 +ᵘ (-ᵘ u5)
energy5Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip5 u0 u1 u2 u3 u4 energy5Tail (u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (ep5 u5 u6 u7 u8 u9 u10 u11)

energy6Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy6CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u7 +ᵘ (-ᵘ u6)
energy6Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip6 u0 u1 u2 u3 u4 u5 energy6Tail (u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (ep4 u6 u7 u8 u9 u10 u11)

energy7Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy7CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u8 +ᵘ (-ᵘ u7)
energy7Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip7 u0 u1 u2 u3 u4 u5 u6 energy7Tail (u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (ep3 u7 u8 u9 u10 u11)

energy8Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy8CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u9 +ᵘ (-ᵘ u8)
energy8Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip8 u0 u1 u2 u3 u4 u5 u6 u7 energy8Tail (u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (ep2 u8 u9 u10 u11)

energy9Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy9CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u10 +ᵘ (-ᵘ u9)
energy9Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip9 u0 u1 u2 u3 u4 u5 u6 u7 u8 energy9Tail (u9 ∷ u10 ∷ u11 ∷ []) (ep1 u9 u10 u11)

energy10Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy10CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u11 +ᵘ (-ᵘ u10)
energy10Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip10 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 energy10Tail (u10 ∷ u11 ∷ []) (ep0 u10 u11)

e11-11 : ∀ u11 →
  C.dotZU (neg 2 ∷ []) (u11 ∷ []) ≃
  (-ᵘ (sumU (u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-11 u11 =
  UP.≃-trans (dotStep-2 u11 {[]} {[]}) (energy11BaseLemma u11)

e11-10 : ∀ u10 u11 →
  C.dotZU (neg 1 ∷ neg 2 ∷ []) (u10 ∷ u11 ∷ []) ≃
  (-ᵘ (sumU (u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-10 u10 u11 =
  UP.≃-trans (dotStep-1 u10 {neg 2 ∷ []} {u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u10 }) (e11-11 u11))
      (energy11StepLemma u10 (sumU (u11 ∷ [])) (-ᵘ u11)))

e11-9 : ∀ u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 2 ∷ []) (u9 ∷ u10 ∷ u11 ∷ []) ≃
  (-ᵘ (sumU (u9 ∷ u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-9 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u9 {neg 1 ∷ neg 2 ∷ []} {u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u9 }) (e11-10 u10 u11))
      (energy11StepLemma u9 (sumU (u10 ∷ u11 ∷ [])) (-ᵘ u11)))

e11-8 : ∀ u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []) (u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  (-ᵘ (sumU (u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-8 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u8 {neg 1 ∷ neg 1 ∷ neg 2 ∷ []} {u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u8 }) (e11-9 u9 u10 u11))
      (energy11StepLemma u8 (sumU (u9 ∷ u10 ∷ u11 ∷ [])) (-ᵘ u11)))

e11-7 : ∀ u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []) (u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  (-ᵘ (sumU (u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-7 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u7 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []} {u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u7 }) (e11-8 u8 u9 u10 u11))
      (energy11StepLemma u7 (sumU (u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])) (-ᵘ u11)))

e11-6 : ∀ u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []) (u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  (-ᵘ (sumU (u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-6 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u6 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []} {u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u6 }) (e11-7 u7 u8 u9 u10 u11))
      (energy11StepLemma u6 (sumU (u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])) (-ᵘ u11)))

e11-5 : ∀ u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []) (u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  (-ᵘ (sumU (u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-5 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u5 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []} {u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u5 }) (e11-6 u6 u7 u8 u9 u10 u11))
      (energy11StepLemma u5 (sumU (u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])) (-ᵘ u11)))

e11-4 : ∀ u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []) (u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  (-ᵘ (sumU (u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-4 u4 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u4 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []} {u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u4 }) (e11-5 u5 u6 u7 u8 u9 u10 u11))
      (energy11StepLemma u4 (sumU (u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])) (-ᵘ u11)))

e11-3 : ∀ u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []) (u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  (-ᵘ (sumU (u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-3 u3 u4 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u3 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []} {u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u3 }) (e11-4 u4 u5 u6 u7 u8 u9 u10 u11))
      (energy11StepLemma u3 (sumU (u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])) (-ᵘ u11)))

e11-2 : ∀ u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []) (u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  (-ᵘ (sumU (u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-2 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u2 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []} {u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u2 }) (e11-3 u3 u4 u5 u6 u7 u8 u9 u10 u11))
      (energy11StepLemma u2 (sumU (u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])) (-ᵘ u11)))

e11-1 : ∀ u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []) (u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  (-ᵘ (sumU (u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
e11-1 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u1 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []} {u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u1 }) (e11-2 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11))
      (energy11StepLemma u1 (sumU (u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])) (-ᵘ u11)))

energy11Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU energy11CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])
  ≃ (-ᵘ (sumU (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))) +ᵘ (-ᵘ u11)
energy11Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u0 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []} {u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u0 }) (e11-1 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11))
      (UP.≃-trans
        (UP.≃-sym (UP.+-assoc (-ᵘ u0) (-ᵘ (sumU (u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))) (-ᵘ u11)))
        (UP.+-cong (UP.≃-sym (negDistrib u0 (sumU (u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])))) UP.≃-refl)))

energyLinear0U : ∀ c → C.dotZU energy0CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y1 c - y0 c)
energyLinear0U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy0Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU b a))

energyLinear1U : ∀ c → C.dotZU energy1CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y2 c - y1 c)
energyLinear1U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy1Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU c b))

energyLinear2U : ∀ c → C.dotZU energy2CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y3 c - y2 c)
energyLinear2U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy2Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU d c))

energyLinear3U : ∀ c → C.dotZU energy3CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y4 c - y3 c)
energyLinear3U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy3Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU e d))

energyLinear4U : ∀ c → C.dotZU energy4CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y5 c - y4 c)
energyLinear4U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy4Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU f e))

energyLinear5U : ∀ c → C.dotZU energy5CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y6 c - y5 c)
energyLinear5U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy5Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU g f))

energyLinear6U : ∀ c → C.dotZU energy6CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y7 c - y6 c)
energyLinear6U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy6Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU h g))

energyLinear7U : ∀ c → C.dotZU energy7CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y8 c - y7 c)
energyLinear7U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy7Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU i h))

energyLinear8U : ∀ c → C.dotZU energy8CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y9 c - y8 c)
energyLinear8U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy8Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU j i))

energyLinear9U : ∀ c → C.dotZU energy9CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y10 c - y9 c)
energyLinear9U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy9Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU k j))
energyLinear10U : ∀ c → C.dotZU energy10CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y11 c - y10 c)
energyLinear10U (path13Coordinates a b c d e f g h i j k l) = UP.≃-trans (energy10Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (toSubU l k))
energyLinear11U : ∀ c → C.dotZU energy11CoefficientsZ (coordinatesU c) ≃ toℚᵘ (lastCoordinate c - y11 c)
energyLinear11U p@(path13Coordinates a b c d e f g h i j k l) =
  UP.≃-trans
    (energy11Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l))
    (UP.≃-trans
      (UP.+-cong (UP.≃-sym (lastCoordinateToU p)) UP.≃-refl)
      (UP.≃-sym (toSubU (lastCoordinate p) l)))

------------------------------------------------------------------------
-- Norm basis rows.  Kept as explicit Raw owners so solve-∀ is never used as
-- an ordinary function call.
------------------------------------------------------------------------


dotNegSumNil : C.dotZU [] [] ≃ -ᵘ (sumU [])
dotNegSumNil = UP.≃-sym negZero

norm0Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm0CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u0
norm0Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = oz11 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

norm1Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm1CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u1
norm1Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip1 u0 norm1Tail (u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (oz10 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11)

norm2Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm2CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u2
norm2Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip2 u0 u1 norm2Tail (u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (oz9 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11)

norm3Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm3CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u3
norm3Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip3 u0 u1 u2 norm3Tail (u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (oz8 u3 u4 u5 u6 u7 u8 u9 u10 u11)

norm4Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm4CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u4
norm4Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip4 u0 u1 u2 u3 norm4Tail (u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (oz7 u4 u5 u6 u7 u8 u9 u10 u11)

norm5Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm5CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u5
norm5Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip5 u0 u1 u2 u3 u4 norm5Tail (u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (oz6 u5 u6 u7 u8 u9 u10 u11)

norm6Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm6CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u6
norm6Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip6 u0 u1 u2 u3 u4 u5 norm6Tail (u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (oz5 u6 u7 u8 u9 u10 u11)

norm7Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm7CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u7
norm7Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip7 u0 u1 u2 u3 u4 u5 u6 norm7Tail (u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (oz4 u7 u8 u9 u10 u11)

norm8Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm8CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u8
norm8Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip8 u0 u1 u2 u3 u4 u5 u6 u7 norm8Tail (u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) (oz3 u8 u9 u10 u11)

norm9Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm9CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u9
norm9Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip9 u0 u1 u2 u3 u4 u5 u6 u7 u8 norm9Tail (u9 ∷ u10 ∷ u11 ∷ []) (oz2 u9 u10 u11)

norm10Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm10CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u10
norm10Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip10 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 norm10Tail (u10 ∷ u11 ∷ []) (oz1 u10 u11)

norm11Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 → C.dotZU norm11CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃ u11
norm11Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 = strip11 u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 norm11Tail (u11 ∷ []) (oz0 u11)

n12-11 : ∀ u11 →
  C.dotZU (neg 1 ∷ []) (u11 ∷ []) ≃
  -ᵘ (sumU (u11 ∷ []))
n12-11 u11 =
  UP.≃-trans (dotStep-1 u11 {[]} {[]})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u11 }) dotNegSumNil)
      (UP.≃-sym (negDistrib u11 (sumU []))))

n12-10 : ∀ u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ []) (u10 ∷ u11 ∷ []) ≃
  -ᵘ (sumU (u10 ∷ u11 ∷ []))
n12-10 u10 u11 =
  UP.≃-trans (dotStep-1 u10 {neg 1 ∷ []} {u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u10 }) (n12-11 u11))
      (UP.≃-sym (negDistrib u10 (sumU (u11 ∷ [])))))

n12-9 : ∀ u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ []) (u9 ∷ u10 ∷ u11 ∷ []) ≃
  -ᵘ (sumU (u9 ∷ u10 ∷ u11 ∷ []))
n12-9 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u9 {neg 1 ∷ neg 1 ∷ []} {u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u9 }) (n12-10 u10 u11))
      (UP.≃-sym (negDistrib u9 (sumU (u10 ∷ u11 ∷ [])))))

n12-8 : ∀ u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []) (u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  -ᵘ (sumU (u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))
n12-8 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u8 {neg 1 ∷ neg 1 ∷ neg 1 ∷ []} {u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u8 }) (n12-9 u9 u10 u11))
      (UP.≃-sym (negDistrib u8 (sumU (u9 ∷ u10 ∷ u11 ∷ [])))))

n12-7 : ∀ u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []) (u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  -ᵘ (sumU (u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))
n12-7 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u7 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []} {u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u7 }) (n12-8 u8 u9 u10 u11))
      (UP.≃-sym (negDistrib u7 (sumU (u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])))))

n12-6 : ∀ u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []) (u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  -ᵘ (sumU (u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))
n12-6 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u6 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []} {u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u6 }) (n12-7 u7 u8 u9 u10 u11))
      (UP.≃-sym (negDistrib u6 (sumU (u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])))))

n12-5 : ∀ u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []) (u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  -ᵘ (sumU (u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))
n12-5 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u5 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []} {u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u5 }) (n12-6 u6 u7 u8 u9 u10 u11))
      (UP.≃-sym (negDistrib u5 (sumU (u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])))))

n12-4 : ∀ u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []) (u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  -ᵘ (sumU (u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))
n12-4 u4 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u4 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []} {u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u4 }) (n12-5 u5 u6 u7 u8 u9 u10 u11))
      (UP.≃-sym (negDistrib u4 (sumU (u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])))))

n12-3 : ∀ u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []) (u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  -ᵘ (sumU (u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))
n12-3 u3 u4 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u3 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []} {u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u3 }) (n12-4 u4 u5 u6 u7 u8 u9 u10 u11))
      (UP.≃-sym (negDistrib u3 (sumU (u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])))))

n12-2 : ∀ u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []) (u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  -ᵘ (sumU (u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))
n12-2 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u2 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []} {u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u2 }) (n12-3 u3 u4 u5 u6 u7 u8 u9 u10 u11))
      (UP.≃-sym (negDistrib u2 (sumU (u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])))))

n12-1 : ∀ u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU (neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []) (u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []) ≃
  -ᵘ (sumU (u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))
n12-1 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u1 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []} {u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u1 }) (n12-2 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11))
      (UP.≃-sym (negDistrib u1 (sumU (u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])))))

norm12Raw : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 →
  C.dotZU norm12CoefficientsZ (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])
  ≃ -ᵘ (sumU (u0 ∷ u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []))
norm12Raw u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 =
  UP.≃-trans (dotStep-1 u0 {neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []} {u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ []})
    (UP.≃-trans (UP.+-cong (UP.≃-refl { -ᵘ u0 }) (n12-1 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11))
      (UP.≃-sym (negDistrib u0 (sumU (u1 ∷ u2 ∷ u3 ∷ u4 ∷ u5 ∷ u6 ∷ u7 ∷ u8 ∷ u9 ∷ u10 ∷ u11 ∷ [])))))



normLinear0U : ∀ c → C.dotZU norm0CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y0 c)
normLinear0U (path13Coordinates a b c d e f g h i j k l) = norm0Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear1U : ∀ c → C.dotZU norm1CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y1 c)
normLinear1U (path13Coordinates a b c d e f g h i j k l) = norm1Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear2U : ∀ c → C.dotZU norm2CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y2 c)
normLinear2U (path13Coordinates a b c d e f g h i j k l) = norm2Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear3U : ∀ c → C.dotZU norm3CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y3 c)
normLinear3U (path13Coordinates a b c d e f g h i j k l) = norm3Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear4U : ∀ c → C.dotZU norm4CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y4 c)
normLinear4U (path13Coordinates a b c d e f g h i j k l) = norm4Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear5U : ∀ c → C.dotZU norm5CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y5 c)
normLinear5U (path13Coordinates a b c d e f g h i j k l) = norm5Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear6U : ∀ c → C.dotZU norm6CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y6 c)
normLinear6U (path13Coordinates a b c d e f g h i j k l) = norm6Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear7U : ∀ c → C.dotZU norm7CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y7 c)
normLinear7U (path13Coordinates a b c d e f g h i j k l) = norm7Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear8U : ∀ c → C.dotZU norm8CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y8 c)
normLinear8U (path13Coordinates a b c d e f g h i j k l) = norm8Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear9U : ∀ c → C.dotZU norm9CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y9 c)
normLinear9U (path13Coordinates a b c d e f g h i j k l) = norm9Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear10U : ∀ c → C.dotZU norm10CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y10 c)
normLinear10U (path13Coordinates a b c d e f g h i j k l) = norm10Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear11U : ∀ c → C.dotZU norm11CoefficientsZ (coordinatesU c) ≃ toℚᵘ (y11 c)
normLinear11U (path13Coordinates a b c d e f g h i j k l) = norm11Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)
normLinear12U : ∀ c → C.dotZU norm12CoefficientsZ (coordinatesU c) ≃ toℚᵘ (lastCoordinate c)
normLinear12U p@(path13Coordinates a b c d e f g h i j k l) =
  UP.≃-trans (norm12Raw (toℚᵘ a) (toℚᵘ b) (toℚᵘ c) (toℚᵘ d) (toℚᵘ e) (toℚᵘ f) (toℚᵘ g) (toℚᵘ h) (toℚᵘ i) (toℚᵘ j) (toℚᵘ k) (toℚᵘ l)) (UP.≃-sym (lastCoordinateToU p))

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
  (UP.+-cong (squareIntoQ (energyLinear11U c)) (UP.≃-refl {0ℚᵘ}))))))))))))

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
  (UP.+-cong (squareIntoQ (normLinear12U c)) (UP.≃-refl {0ℚᵘ})))))))))))))

energyEvalToQ : ∀ c → C.evalTriZU energyTriZ (coordinatesU c) ≃ toℚᵘ (path13Energy c)
energyEvalToQ c =
  UP.≃-trans
    (C.sumSquareCompilerZU energyFamiliesZ (coordinatesU c))
    (UP.≃-trans
      (energyValuesToTerms c)
      (UP.≃-trans
        (UP.≃-sym (toSumU (energyTermsQ c)))
        (UP.≃-reflexive (cong toℚᵘ (energySumExact c)))))

normEvalToQ : ∀ c → C.evalTriZU normTriZ (coordinatesU c) ≃ toℚᵘ (path13NormSq c)
normEvalToQ c =
  UP.≃-trans
    (C.sumSquareCompilerZU normFamiliesZ (coordinatesU c))
    (UP.≃-trans
      (normValuesToTerms c)
      (UP.≃-trans
        (UP.≃-sym (toSumU (normTermsQ c)))
        (UP.≃-reflexive (cong toℚᵘ (normSumExact c)))))
