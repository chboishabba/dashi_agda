module DASHI.Physics.YangMills.BalabanIntegerTriangularUnnormalisedCompilerExact where

------------------------------------------------------------------------
-- Interpret native-ℤ quadratic certificates in unnormalised rationals.
--
-- ℚᵘ is intentional: its +/* operations multiply integer numerators and
-- denominators directly and never call rational normalize/gcd/Nat division.
-- Algebra below is local (one list/triangular constructor at a time).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer using (ℤ; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Unnormalised.Base as U
  using (ℚᵘ; 0ℚᵘ; _≃_; NonNegative)
  renaming (_+_ to _+ᵘ_; _*_ to _*ᵘ_; -_ to -ᵘ_; _/_ to _/ᵘ_)
import Data.Rational.Unnormalised.Properties as UP
import Data.Rational.Unnormalised.Tactic.RingSolver as URing

import DASHI.Physics.YangMills.BalabanIntegerTriangularQuadraticCertificateExact as QuadZ

embedZ : ℤ → ℚᵘ
embedZ z = z /ᵘ 1

embedZ-+ : ∀ a b → embedZ (a + b) ≡ embedZ a +ᵘ embedZ b
embedZ-+ a b = refl

embedZ-* : ∀ a b → embedZ (a * b) ≡ embedZ a *ᵘ embedZ b
embedZ-* a b = refl

zeroMulZero : 0ℚᵘ *ᵘ 0ℚᵘ ≃ 0ℚᵘ
zeroMulZero = URing.solve-∀

zeroPlus : ∀ x → 0ℚᵘ +ᵘ x ≃ x
zeroPlus = URing.solve-∀

plusZero : ∀ x → x +ᵘ 0ℚᵘ ≃ x
plusZero = URing.solve-∀

dotZU : List ℤ → List ℚᵘ → ℚᵘ
dotZU [] ys = 0ℚᵘ
dotZU xs [] = 0ℚᵘ
dotZU (a ∷ as) (x ∷ xs) = embedZ a *ᵘ x +ᵘ dotZU as xs

scaleDotStep : ∀ s a x d →
  (embedZ s *ᵘ embedZ a) *ᵘ x +ᵘ embedZ s *ᵘ d
  ≃ embedZ s *ᵘ (embedZ a *ᵘ x +ᵘ d)
scaleDotStep = URing.solve-∀

dotScaleZU : ∀ scalar coefficients coordinates →
  dotZU (QuadZ.scaleListZ scalar coefficients) coordinates
  ≃ embedZ scalar *ᵘ dotZU coefficients coordinates
dotScaleZU scalar [] coordinates = UP.≃-sym (UP.*-zeroʳ (embedZ scalar))
dotScaleZU scalar (a ∷ as) [] = UP.≃-sym (UP.*-zeroʳ (embedZ scalar))
dotScaleZU scalar (a ∷ as) (x ∷ xs) =
  UP.≃-trans
    (UP.+-cong
      (UP.*-cong
        (UP.≃-reflexive (embedZ-* scalar a))
        UP.≃-refl)
      (dotScaleZU scalar as xs))
    (scaleDotStep scalar a x (dotZU as xs))

addDotStep : ∀ a b x da db →
  (embedZ a +ᵘ embedZ b) *ᵘ x +ᵘ (da +ᵘ db)
  ≃ (embedZ a *ᵘ x +ᵘ da) +ᵘ (embedZ b *ᵘ x +ᵘ db)
addDotStep = URing.solve-∀

dotAddZU : ∀ left right coordinates →
  dotZU (QuadZ.addListZ left right) coordinates
  ≃ dotZU left coordinates +ᵘ dotZU right coordinates
dotAddZU [] right coordinates = UP.≃-sym (zeroPlus (dotZU right coordinates))
dotAddZU (a ∷ as) [] coordinates = UP.≃-sym (plusZero (dotZU (a ∷ as) coordinates))
dotAddZU (a ∷ as) (b ∷ bs) [] = UP.≃-sym (zeroPlus 0ℚᵘ)
dotAddZU (a ∷ as) (b ∷ bs) (x ∷ xs) =
  UP.≃-trans
    (UP.+-cong
      (UP.*-cong
        (UP.≃-reflexive (embedZ-+ a b))
        UP.≃-refl)
      (dotAddZU as bs xs))
    (addDotStep a b x (dotZU as xs) (dotZU bs xs))

evalTriZU : QuadZ.TriQuadraticZ → List ℚᵘ → ℚᵘ
evalTriZU QuadZ.qnilZ xs = 0ℚᵘ
evalTriZU (QuadZ.qconsZ diagonal row tail) [] = 0ℚᵘ
evalTriZU (QuadZ.qconsZ diagonal row tail) (x ∷ xs) =
  embedZ diagonal *ᵘ x *ᵘ x
  +ᵘ x *ᵘ dotZU row xs
  +ᵘ evalTriZU tail xs

evalScaleStep : ∀ s d x r t →
  (embedZ s *ᵘ embedZ d) *ᵘ x *ᵘ x
  +ᵘ x *ᵘ (embedZ s *ᵘ r)
  +ᵘ embedZ s *ᵘ t
  ≃ embedZ s *ᵘ (embedZ d *ᵘ x *ᵘ x +ᵘ x *ᵘ r +ᵘ t)
evalScaleStep = URing.solve-∀

evalScaleZU : ∀ scalar quadratic coordinates →
  evalTriZU (QuadZ.scaleTriZ scalar quadratic) coordinates
  ≃ embedZ scalar *ᵘ evalTriZU quadratic coordinates
evalScaleZU scalar QuadZ.qnilZ coordinates = UP.≃-sym (UP.*-zeroʳ (embedZ scalar))
evalScaleZU scalar (QuadZ.qconsZ diagonal row tail) [] =
  UP.≃-sym (UP.*-zeroʳ (embedZ scalar))
evalScaleZU scalar (QuadZ.qconsZ diagonal row tail) (x ∷ xs) =
  UP.≃-trans
    (UP.+-cong
      (UP.+-cong
        (UP.*-cong
          (UP.*-cong
            (UP.≃-reflexive (embedZ-* scalar diagonal))
            UP.≃-refl)
          UP.≃-refl)
        (UP.*-cong UP.≃-refl (dotScaleZU scalar row xs)))
      (evalScaleZU scalar tail xs))
    (evalScaleStep scalar diagonal x (dotZU row xs) (evalTriZU tail xs))

evalAddStep : ∀ dl dr x rl rr tl tr →
  (embedZ dl +ᵘ embedZ dr) *ᵘ x *ᵘ x
  +ᵘ x *ᵘ (rl +ᵘ rr)
  +ᵘ (tl +ᵘ tr)
  ≃ (embedZ dl *ᵘ x *ᵘ x +ᵘ x *ᵘ rl +ᵘ tl)
    +ᵘ (embedZ dr *ᵘ x *ᵘ x +ᵘ x *ᵘ rr +ᵘ tr)
evalAddStep = URing.solve-∀

evalAddZU : ∀ left right coordinates →
  evalTriZU (QuadZ.addTriZ left right) coordinates
  ≃ evalTriZU left coordinates +ᵘ evalTriZU right coordinates
evalAddZU QuadZ.qnilZ right coordinates = UP.≃-sym (zeroPlus (evalTriZU right coordinates))
evalAddZU (QuadZ.qconsZ dl rl tl) QuadZ.qnilZ coordinates =
  UP.≃-sym (plusZero (evalTriZU (QuadZ.qconsZ dl rl tl) coordinates))
evalAddZU (QuadZ.qconsZ dl rl tl) (QuadZ.qconsZ dr rr tr) [] =
  UP.≃-sym (zeroPlus 0ℚᵘ)
evalAddZU (QuadZ.qconsZ dl rl tl) (QuadZ.qconsZ dr rr tr) (x ∷ xs) =
  UP.≃-trans
    (UP.+-cong
      (UP.+-cong
        (UP.*-cong
          (UP.*-cong
            (UP.≃-reflexive (embedZ-+ dl dr))
            UP.≃-refl)
          UP.≃-refl)
        (UP.*-cong UP.≃-refl (dotAddZU rl rr xs)))
      (evalAddZU tl tr xs))
    (evalAddStep dl dr x (dotZU rl xs) (dotZU rr xs)
      (evalTriZU tl xs) (evalTriZU tr xs))

squareStep : ∀ a x d →
  (embedZ a *ᵘ x +ᵘ d) *ᵘ (embedZ a *ᵘ x +ᵘ d)
  ≃ embedZ a *ᵘ embedZ a *ᵘ x *ᵘ x
    +ᵘ x *ᵘ ((embedZ a +ᵘ embedZ a) *ᵘ d)
    +ᵘ d *ᵘ d
squareStep = URing.solve-∀

squareDotZU : ∀ coefficients coordinates →
  dotZU coefficients coordinates *ᵘ dotZU coefficients coordinates
  ≃ evalTriZU (QuadZ.squareLinearZ coefficients) coordinates
squareDotZU [] coordinates = zeroMulZero
squareDotZU (a ∷ as) [] = zeroMulZero
squareDotZU (a ∷ as) (x ∷ xs) =
  UP.≃-trans
    (squareStep a x (dotZU as xs))
    (UP.≃-sym
      (UP.+-cong
        (UP.+-cong
          (UP.*-cong
            (UP.*-cong
              (UP.≃-reflexive (embedZ-* a a))
              UP.≃-refl)
            UP.≃-refl)
          (UP.*-cong UP.≃-refl
            (UP.≃-trans
              (UP.*-cong
                (UP.≃-reflexive (embedZ-+ a a))
                UP.≃-refl)
              (dotScaleZU (a + a) as xs))))
        (squareDotZU as xs)))

sumSquareValuesZU : List (List ℤ) → List ℚᵘ → ℚᵘ
sumSquareValuesZU [] coordinates = 0ℚᵘ
sumSquareValuesZU (coefficients ∷ rest) coordinates =
  dotZU coefficients coordinates *ᵘ dotZU coefficients coordinates
  +ᵘ sumSquareValuesZU rest coordinates

sumSquareCompilerZU : ∀ families coordinates →
  evalTriZU (QuadZ.sumSquareTriZ families) coordinates
  ≃ sumSquareValuesZU families coordinates
sumSquareCompilerZU [] coordinates = UP.≃-refl
sumSquareCompilerZU (coefficients ∷ rest) coordinates =
  UP.≃-trans
    (evalAddZU
      (QuadZ.squareLinearZ coefficients)
      (QuadZ.sumSquareTriZ rest)
      coordinates)
    (UP.+-cong
      (UP.≃-sym (squareDotZU coefficients coordinates))
      (sumSquareCompilerZU rest coordinates))

sumWeightedSquareValuesZU : List (ℤ × List ℤ) → List ℚᵘ → ℚᵘ
sumWeightedSquareValuesZU [] coordinates = 0ℚᵘ
sumWeightedSquareValuesZU ((weight , coefficients) ∷ rest) coordinates =
  embedZ weight *ᵘ (dotZU coefficients coordinates *ᵘ dotZU coefficients coordinates)
  +ᵘ sumWeightedSquareValuesZU rest coordinates

weightedSquareCompilerZU : ∀ weight coefficients coordinates →
  evalTriZU (QuadZ.weightedSquareTriZ weight coefficients) coordinates
  ≃ embedZ weight *ᵘ (dotZU coefficients coordinates *ᵘ dotZU coefficients coordinates)
weightedSquareCompilerZU weight coefficients coordinates =
  UP.≃-trans
    (evalScaleZU weight (QuadZ.squareLinearZ coefficients) coordinates)
    (UP.*-cong UP.≃-refl (UP.≃-sym (squareDotZU coefficients coordinates)))

sumWeightedSquareCompilerZU : ∀ families coordinates →
  evalTriZU (QuadZ.sumWeightedSquareTriZ families) coordinates
  ≃ sumWeightedSquareValuesZU families coordinates
sumWeightedSquareCompilerZU [] coordinates = UP.≃-refl
sumWeightedSquareCompilerZU ((weight , coefficients) ∷ rest) coordinates =
  UP.≃-trans
    (evalAddZU
      (QuadZ.weightedSquareTriZ weight coefficients)
      (QuadZ.sumWeightedSquareTriZ rest)
      coordinates)
    (UP.+-cong
      (weightedSquareCompilerZU weight coefficients coordinates)
      (sumWeightedSquareCompilerZU rest coordinates))
