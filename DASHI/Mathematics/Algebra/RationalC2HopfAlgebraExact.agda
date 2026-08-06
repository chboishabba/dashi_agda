module DASHI.Mathematics.Algebra.RationalC2HopfAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Christian Kassel,
-- "Quantum Groups", Graduate Texts in Mathematics 155.
-- DOI: 10.1007/978-1-4612-0783-2.
--
-- Stephen U. Chase and Moss E. Sweedler,
-- "Hopf Algebras and Galois Theory", Lecture Notes in Mathematics 97.
-- DOI: 10.1007/BFb0101433.
--
-- DASHI CONTRIBUTION
--
-- Keep "Hopf algebra" separate from Hopf fibrations and the Hopf invariant by
-- constructing a small exact example: the rational group algebra Q[C2].
-- With basis {1,g}, g^2=1, the coproduct, counit and antipode are
--
--   Delta(1)=1 tensor 1,   Delta(g)=g tensor g,
--   epsilon(1)=epsilon(g)=1,
--   S(1)=1,                S(g)=g.
--
-- The file proves multiplication associativity and units, coproduct
-- coassociativity, both counit laws, multiplicativity of Delta and epsilon,
-- and both antipode convolution identities by exact rational polynomial
-- calculation.
--
-- It does not identify this finite cocommutative example with a quantum gauge
-- field, a renormalisation Hopf algebra, a Hopf fibration, or a Hopf-invariant
-- theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- The rational group algebra of C2.
------------------------------------------------------------------------

record C2GroupAlgebra : Set where
  constructor c2
  field
    coefficientOne coefficientG : ℚ

open C2GroupAlgebra public

zeroH unitH generatorH : C2GroupAlgebra
zeroH      = c2 0ℚ 0ℚ
unitH      = c2 1ℚ 0ℚ
generatorH = c2 0ℚ 1ℚ

_+h_ : C2GroupAlgebra → C2GroupAlgebra → C2GroupAlgebra
c2 a b +h c2 c d = c2 (a + c) (b + d)

_*h_ : C2GroupAlgebra → C2GroupAlgebra → C2GroupAlgebra
c2 a b *h c2 c d =
  c2 (a * c + b * d) (a * d + b * c)

c2Ext : ∀ {left right} →
  coefficientOne left ≡ coefficientOne right →
  coefficientG left ≡ coefficientG right →
  left ≡ right
c2Ext {c2 _ _} {c2 _ _} refl refl = refl

multiplicationAssociative : ∀ first middle last →
  (first *h middle) *h last ≡ first *h (middle *h last)
multiplicationAssociative
    (c2 a b) (c2 c d) (c2 e f) =
  c2Ext
    (solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []))

unitLeft : ∀ value → unitH *h value ≡ value
unitLeft (c2 a b) =
  c2Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

unitRight : ∀ value → value *h unitH ≡ value
unitRight (c2 a b) =
  c2Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

generatorSquaresToUnit : generatorH *h generatorH ≡ unitH
generatorSquaresToUnit =
  c2Ext (solve []) (solve [])

------------------------------------------------------------------------
-- Tensor-square algebra Q[C2 x C2].
------------------------------------------------------------------------

record TensorSquare : Set where
  constructor tensorSquare
  field
    tensor00 tensor01 tensor10 tensor11 : ℚ

open TensorSquare public

tensorSquareExt : ∀ {left right} →
  tensor00 left ≡ tensor00 right →
  tensor01 left ≡ tensor01 right →
  tensor10 left ≡ tensor10 right →
  tensor11 left ≡ tensor11 right →
  left ≡ right
tensorSquareExt {tensorSquare _ _ _ _} {tensorSquare _ _ _ _}
  refl refl refl refl = refl

tensorUnit : TensorSquare
tensorUnit = tensorSquare 1ℚ 0ℚ 0ℚ 0ℚ

_*t_ : TensorSquare → TensorSquare → TensorSquare
tensorSquare a00 a01 a10 a11 *t tensorSquare b00 b01 b10 b11 =
  tensorSquare
    (a00 * b00 + a01 * b01 + a10 * b10 + a11 * b11)
    (a00 * b01 + a01 * b00 + a10 * b11 + a11 * b10)
    (a00 * b10 + a10 * b00 + a01 * b11 + a11 * b01)
    (a00 * b11 + a11 * b00 + a01 * b10 + a10 * b01)

delta : C2GroupAlgebra → TensorSquare
delta (c2 a b) = tensorSquare a 0ℚ 0ℚ b

counit : C2GroupAlgebra → ℚ
counit (c2 a b) = a + b

antipode : C2GroupAlgebra → C2GroupAlgebra
antipode value = value

deltaUnit : delta unitH ≡ tensorUnit
deltaUnit = refl

deltaMultiplicative : ∀ left right →
  delta (left *h right) ≡ delta left *t delta right
deltaMultiplicative (c2 a b) (c2 c d) =
  tensorSquareExt
    (solve (a ∷ b ∷ c ∷ d ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ []))

counitUnit : counit unitH ≡ 1ℚ
counitUnit = solve []

counitMultiplicative : ∀ left right →
  counit (left *h right) ≡ counit left * counit right
counitMultiplicative (c2 a b) (c2 c d) =
  solve (a ∷ b ∷ c ∷ d ∷ [])

------------------------------------------------------------------------
-- Coassociativity in an explicit tensor cube.
------------------------------------------------------------------------

record TensorCube : Set where
  constructor tensorCube
  field
    tensor000 tensor001 tensor010 tensor011 : ℚ
    tensor100 tensor101 tensor110 tensor111 : ℚ

open TensorCube public

tensorCubeExt : ∀ {left right} →
  tensor000 left ≡ tensor000 right →
  tensor001 left ≡ tensor001 right →
  tensor010 left ≡ tensor010 right →
  tensor011 left ≡ tensor011 right →
  tensor100 left ≡ tensor100 right →
  tensor101 left ≡ tensor101 right →
  tensor110 left ≡ tensor110 right →
  tensor111 left ≡ tensor111 right →
  left ≡ right
tensorCubeExt
  {tensorCube _ _ _ _ _ _ _ _}
  {tensorCube _ _ _ _ _ _ _ _}
  refl refl refl refl refl refl refl refl = refl

deltaFirstFactor : TensorSquare → TensorCube
deltaFirstFactor (tensorSquare x00 x01 x10 x11) =
  tensorCube x00 x01 0ℚ 0ℚ 0ℚ 0ℚ x10 x11

deltaSecondFactor : TensorSquare → TensorCube
deltaSecondFactor (tensorSquare x00 x01 x10 x11) =
  tensorCube x00 0ℚ 0ℚ x01 x10 0ℚ 0ℚ x11

deltaCoassociative : ∀ value →
  deltaFirstFactor (delta value) ≡ deltaSecondFactor (delta value)
deltaCoassociative (c2 a b) =
  tensorCubeExt
    (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))
    (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))
    (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))
    (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

------------------------------------------------------------------------
-- Counit and antipode identities.
------------------------------------------------------------------------

counitFirstFactor : TensorSquare → C2GroupAlgebra
counitFirstFactor (tensorSquare x00 x01 x10 x11) =
  c2 (x00 + x10) (x01 + x11)

counitSecondFactor : TensorSquare → C2GroupAlgebra
counitSecondFactor (tensorSquare x00 x01 x10 x11) =
  c2 (x00 + x01) (x10 + x11)

leftCounitIdentity : ∀ value →
  counitFirstFactor (delta value) ≡ value
leftCounitIdentity (c2 a b) =
  c2Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

rightCounitIdentity : ∀ value →
  counitSecondFactor (delta value) ≡ value
rightCounitIdentity (c2 a b) =
  c2Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

multiplyTensorFactors : TensorSquare → C2GroupAlgebra
multiplyTensorFactors (tensorSquare x00 x01 x10 x11) =
  c2 (x00 + x11) (x01 + x10)

antipodeFirstFactor : TensorSquare → TensorSquare
antipodeFirstFactor value = value

antipodeSecondFactor : TensorSquare → TensorSquare
antipodeSecondFactor value = value

unitAfterCounit : C2GroupAlgebra → C2GroupAlgebra
unitAfterCounit value = c2 (counit value) 0ℚ

leftAntipodeIdentity : ∀ value →
  multiplyTensorFactors (antipodeFirstFactor (delta value))
  ≡ unitAfterCounit value
leftAntipodeIdentity (c2 a b) =
  c2Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

rightAntipodeIdentity : ∀ value →
  multiplyTensorFactors (antipodeSecondFactor (delta value))
  ≡ unitAfterCounit value
rightAntipodeIdentity (c2 a b) =
  c2Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

------------------------------------------------------------------------
-- Meaning separation.
------------------------------------------------------------------------

data HopfMeaning : Set where
  hopfAlgebraMeaning : HopfMeaning
  hopfFibrationMeaning : HopfMeaning
  hopfInvariantMeaning : HopfMeaning

hopfAlgebraIsNotHopfFibration :
  hopfAlgebraMeaning ≡ hopfFibrationMeaning → ⊥
hopfAlgebraIsNotHopfFibration ()

hopfAlgebraIsNotHopfInvariant :
  hopfAlgebraMeaning ≡ hopfInvariantMeaning → ⊥
hopfAlgebraIsNotHopfInvariant ()

hopfFibrationIsNotHopfInvariant :
  hopfFibrationMeaning ≡ hopfInvariantMeaning → ⊥
hopfFibrationIsNotHopfInvariant ()
