module DASHI.Analysis.BishopSetoidComplexExact where

------------------------------------------------------------------------
-- BISHOP SETOID COMPLEX NUMBERS
--
-- Carrier:
--   BishopReal x BishopReal
--
-- Equality:
--   componentwise Bishop setoid equivalence.
--
-- Arithmetic is the literal Cartesian complex arithmetic over the vendored
-- Bishop real operations.  Complex exponential is built from the repository's
-- actual Bishop power-series exp/sin/cos:
--
--   exp(x+iy) = exp_B(x) cos_B(y) + i exp_B(x) sin_B(y).
--
-- No propositional quotient is introduced.  This is the setoid-native sibling
-- of DASHI.Analysis.ConcreteComplex needed by route B.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_×_; _,_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpPositive
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as TrigCong
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Concrete

open import DASHI.Physics.YangMills.CompactLieProofLevel

record BishopComplex : Set where
  constructor complex
  field
    re im : BishopReal.ℝ

open BishopComplex public

infix 4 _≈C_
record _≈C_ (left right : BishopComplex) : Set where
  constructor complex-equivalent
  field
    reEquivalent : BishopReal._≃_ (re left) (re right)
    imEquivalent : BishopReal._≃_ (im left) (im right)

open _≈C_ public

≈C-refl : ∀ z → z ≈C z
≈C-refl z =
  complex-equivalent BishopP.≃-refl BishopP.≃-refl

≈C-sym : ∀ {x y} → x ≈C y → y ≈C x
≈C-sym equivalent =
  complex-equivalent
    (BishopP.≃-symm (reEquivalent equivalent))
    (BishopP.≃-symm (imEquivalent equivalent))

≈C-trans : ∀ {x y z} → x ≈C y → y ≈C z → x ≈C z
≈C-trans left right =
  complex-equivalent
    (BishopP.≃-trans
      (reEquivalent left)
      (reEquivalent right))
    (BishopP.≃-trans
      (imEquivalent left)
      (imEquivalent right))

zeroC oneC imaginaryUnit : BishopComplex
zeroC = complex BishopReal.0ℝ BishopReal.0ℝ
oneC = complex BishopReal.1ℝ BishopReal.0ℝ
imaginaryUnit = complex BishopReal.0ℝ BishopReal.1ℝ

infixl 6 _+C_ _-C_
infixl 7 _*C_

_+C_ : BishopComplex → BishopComplex → BishopComplex
complex a b +C complex c d =
  complex
    (BishopReal._+_ a c)
    (BishopReal._+_ b d)

_-C_ : BishopComplex → BishopComplex → BishopComplex
complex a b -C complex c d =
  complex
    (BishopReal._-_ a c)
    (BishopReal._-_ b d)

_*C_ : BishopComplex → BishopComplex → BishopComplex
complex a b *C complex c d =
  complex
    (BishopReal._-_
      (BishopReal._*_ a c)
      (BishopReal._*_ b d))
    (BishopReal._+_
      (BishopReal._*_ a d)
      (BishopReal._*_ b c))

negC : BishopComplex → BishopComplex
negC (complex a b) =
  complex (BishopReal.- a) (BishopReal.- b)

addCongruent :
  ∀ {x x' y y'} →
  x ≈C x' →
  y ≈C y' →
  (x +C y) ≈C (x' +C y')
addCongruent left right =
  complex-equivalent
    (BishopP.+-cong
      (reEquivalent left)
      (reEquivalent right))
    (BishopP.+-cong
      (imEquivalent left)
      (imEquivalent right))

subCongruent :
  ∀ {x x' y y'} →
  x ≈C x' →
  y ≈C y' →
  (x -C y) ≈C (x' -C y')
subCongruent left right =
  complex-equivalent
    (BishopP.+-cong
      (reEquivalent left)
      (BishopP.-‿cong (reEquivalent right)))
    (BishopP.+-cong
      (imEquivalent left)
      (BishopP.-‿cong (imEquivalent right)))

mulCongruent :
  ∀ {x x' y y'} →
  x ≈C x' →
  y ≈C y' →
  (x *C y) ≈C (x' *C y')
mulCongruent left right =
  complex-equivalent
    (BishopP.+-cong
      (BishopP.*-cong
        (reEquivalent left)
        (reEquivalent right))
      (BishopP.-‿cong
        (BishopP.*-cong
          (imEquivalent left)
          (imEquivalent right))))
    (BishopP.+-cong
      (BishopP.*-cong
        (reEquivalent left)
        (imEquivalent right))
      (BishopP.*-cong
        (imEquivalent left)
        (reEquivalent right)))

negCongruent :
  ∀ {x y} →
  x ≈C y →
  negC x ≈C negC y
negCongruent equivalent =
  complex-equivalent
    (BishopP.-‿cong (reEquivalent equivalent))
    (BishopP.-‿cong (imEquivalent equivalent))

conjugate : BishopComplex → BishopComplex
conjugate (complex a b) =
  complex a (BishopReal.- b)

conjugateCongruent :
  ∀ {x y} →
  x ≈C y →
  conjugate x ≈C conjugate y
conjugateCongruent equivalent =
  complex-equivalent
    (reEquivalent equivalent)
    (BishopP.-‿cong (imEquivalent equivalent))

record BishopSetoidComplexTranscendentals : Set₁ where
  field
    dataSet : Elementary.BishopElementaryPowerSeriesData

    trigIdentification :
      Concrete.ConcreteSineCosineTermIdentification dataSet

    pi : BishopReal.ℝ

open BishopSetoidComplexTranscendentals public

expC :
  BishopSetoidComplexTranscendentals →
  BishopComplex →
  BishopComplex
expC T (complex x y) =
  complex
    (BishopReal._*_
      (Exp.bishopExp x)
      (Elementary.bishopCos (dataSet T) y))
    (BishopReal._*_
      (Exp.bishopExp x)
      (Elementary.bishopSin (dataSet T) y))

expCongruent :
  (T : BishopSetoidComplexTranscendentals) →
  ∀ {x y} →
  x ≈C y →
  expC T x ≈C expC T y
expCongruent T equivalent =
  complex-equivalent
    (BishopP.*-cong
      (ExpCong.bishopExpCongruent
        (reEquivalent equivalent))
      (TrigCong.bishopCosCongruent
        (trigIdentification T)
        (imEquivalent equivalent)))
    (BishopP.*-cong
      (ExpCong.bishopExpCongruent
        (reEquivalent equivalent))
      (TrigCong.bishopSinCongruent
        (trigIdentification T)
        (imEquivalent equivalent)))

piC :
  BishopSetoidComplexTranscendentals →
  BishopComplex
piC T = complex (pi T) BishopReal.0ℝ

------------------------------------------------------------------------
-- Natural scaling / powers used by the Eisenstein q-series.
------------------------------------------------------------------------

scaleNatC : Nat → BishopComplex → BishopComplex
scaleNatC zero z = zeroC
scaleNatC (suc n) z =
  z +C scaleNatC n z

powC : BishopComplex → Nat → BishopComplex
powC z zero = oneC
powC z (suc n) =
  z *C powC z n

scaleNatCongruent :
  ∀ n {x y} →
  x ≈C y →
  scaleNatC n x ≈C scaleNatC n y
scaleNatCongruent zero equivalent = ≈C-refl zeroC
scaleNatCongruent (suc n) equivalent =
  addCongruent equivalent
    (scaleNatCongruent n equivalent)

powCongruent :
  ∀ n {x y} →
  x ≈C y →
  powC x n ≈C powC y n
powCongruent zero equivalent = ≈C-refl oneC
powCongruent (suc n) equivalent =
  mulCongruent equivalent
    (powCongruent n equivalent)

------------------------------------------------------------------------
-- Basic structural receipt.
------------------------------------------------------------------------

record BishopSetoidComplexBoundary : Set where
  constructor bishop-setoid-complex-boundary
  field
    carrierIsVendoredBishopPair : Bool
    equalityIsComponentwiseBishopSetoid : Bool
    ringOperationsSetoidCongruent : Bool
    exponentialUsesActualBishopPowerSeries : Bool
    exponentialSetoidCongruent : Bool
    trigSetoidCongruenceReducerOwned : Bool

    trigConcreteTermIdentificationInhabitedHere : Bool
    selectedPiIdentifiedWithClassicalPi : Bool

canonicalBishopSetoidComplexBoundary : BishopSetoidComplexBoundary
canonicalBishopSetoidComplexBoundary =
  bishop-setoid-complex-boundary
    true true true true true true
    false false

bishopSetoidComplexAlgebraLevel : ProofLevel
bishopSetoidComplexAlgebraLevel = machineChecked

bishopSetoidComplexExponentialLevel : ProofLevel
bishopSetoidComplexExponentialLevel = machineChecked

bishopSetoidComplexConfiguredTrigIdentificationLevel : ProofLevel
bishopSetoidComplexConfiguredTrigIdentificationLevel = conditional


------------------------------------------------------------------------
-- K05: EXACT SAME-OBJECT REDUCTION OF BOTH ROUND11 TRIG ADDITION
-- LAWS TO ONE PURE-IMAGINARY COMPLEX EXPONENTIAL PRODUCT.
--
-- Unlike the generic constructed-real ExpAdd authority, ALL objects
-- here are the literal pinned Bishop setoid complex, original native
-- factorial exp, and the configured (signed-factorial) sine/cosine.
-- This pays the two-way Cartesian normalisation, NOT the still-open
-- all-x,y source Cauchy product of the imaginary exponential.
------------------------------------------------------------------------

imaginaryPhase :
  BishopSetoidComplexTranscendentals → BishopReal.ℝ → BishopComplex
imaginaryPhase T x =
  complex
    (Elementary.bishopCos (dataSet T) x)
    (Elementary.bishopSin (dataSet T) x)

pureImaginary : BishopReal.ℝ → BishopComplex
pureImaginary x = complex BishopReal.0ℝ x

imaginaryExponentialIsPhase :
  (T : BishopSetoidComplexTranscendentals) (x : BishopReal.ℝ) →
  expC T (pureImaginary x) ≈C imaginaryPhase T x
imaginaryExponentialIsPhase T x =
  complex-equivalent
    (BishopP.≃-trans
      (BishopP.*-cong ExpPositive.bishopExpZero BishopP.≃-refl)
      (BishopP.*-identityˡ
        (Elementary.bishopCos (dataSet T) x)))
    (BishopP.≃-trans
      (BishopP.*-cong ExpPositive.bishopExpZero BishopP.≃-refl)
      (BishopP.*-identityˡ
        (Elementary.bishopSin (dataSet T) x)))

-- The following predicates are *exact equalities* of the ORIGINAL
-- Bishop functions. They are not arbitrary Set-valued authority fields.
BishopSineAdditionAt :
  BishopSetoidComplexTranscendentals →
  BishopReal.ℝ → BishopReal.ℝ → Set
BishopSineAdditionAt T x y =
  BishopReal._≃_
    (Elementary.bishopSin (dataSet T)
      (BishopReal._+_ x y))
    (BishopReal._+_
      (BishopReal._*_
        (Elementary.bishopSin (dataSet T) x)
        (Elementary.bishopCos (dataSet T) y))
      (BishopReal._*_
        (Elementary.bishopCos (dataSet T) x)
        (Elementary.bishopSin (dataSet T) y)))

BishopCosineAdditionAt :
  BishopSetoidComplexTranscendentals →
  BishopReal.ℝ → BishopReal.ℝ → Set
BishopCosineAdditionAt T x y =
  BishopReal._≃_
    (Elementary.bishopCos (dataSet T)
      (BishopReal._+_ x y))
    (BishopReal._-_
      (BishopReal._*_
        (Elementary.bishopCos (dataSet T) x)
        (Elementary.bishopCos (dataSet T) y))
      (BishopReal._*_
        (Elementary.bishopSin (dataSet T) x)
        (Elementary.bishopSin (dataSet T) y)))

imaginaryPhaseProductFromAddition :
  (T : BishopSetoidComplexTranscendentals)
  (x y : BishopReal.ℝ) →
  BishopSineAdditionAt T x y →
  BishopCosineAdditionAt T x y →
  imaginaryPhase T (BishopReal._+_ x y)
    ≈C (imaginaryPhase T x *C imaginaryPhase T y)
imaginaryPhaseProductFromAddition T x y sineAddition cosineAddition =
  complex-equivalent
    cosineAddition
    (BishopP.≃-trans
      sineAddition
      (BishopP.+-comm
        (BishopReal._*_
          (Elementary.bishopSin (dataSet T) x)
          (Elementary.bishopCos (dataSet T) y))
        (BishopReal._*_
          (Elementary.bishopCos (dataSet T) x)
          (Elementary.bishopSin (dataSet T) y))))

imaginaryPhaseProductGivesSineAddition :
  (T : BishopSetoidComplexTranscendentals)
  (x y : BishopReal.ℝ) →
  imaginaryPhase T (BishopReal._+_ x y)
    ≈C (imaginaryPhase T x *C imaginaryPhase T y) →
  BishopSineAdditionAt T x y
imaginaryPhaseProductGivesSineAddition T x y product =
  BishopP.≃-trans
    (imEquivalent product)
    (BishopP.+-comm
      (BishopReal._*_
        (Elementary.bishopCos (dataSet T) x)
        (Elementary.bishopSin (dataSet T) y))
      (BishopReal._*_
        (Elementary.bishopSin (dataSet T) x)
        (Elementary.bishopCos (dataSet T) y)))

imaginaryPhaseProductGivesCosineAddition :
  (T : BishopSetoidComplexTranscendentals)
  (x y : BishopReal.ℝ) →
  imaginaryPhase T (BishopReal._+_ x y)
    ≈C (imaginaryPhase T x *C imaginaryPhase T y) →
  BishopCosineAdditionAt T x y
imaginaryPhaseProductGivesCosineAddition T x y product =
  reEquivalent product

-- Exact core interchange: ONE original complex exponential equation
-- is equivalent to BOTH original sine/cosine addition equations.
imaginaryExponentialProductFromAddition :
  (T : BishopSetoidComplexTranscendentals)
  (x y : BishopReal.ℝ) →
  BishopSineAdditionAt T x y →
  BishopCosineAdditionAt T x y →
  expC T (pureImaginary (BishopReal._+_ x y))
    ≈C (expC T (pureImaginary x) *C expC T (pureImaginary y))
imaginaryExponentialProductFromAddition T x y sineAddition cosineAddition =
  ≈C-trans
    (imaginaryExponentialIsPhase T (BishopReal._+_ x y))
    (≈C-trans
      (imaginaryPhaseProductFromAddition
        T x y sineAddition cosineAddition)
      (mulCongruent
        (≈C-sym (imaginaryExponentialIsPhase T x))
        (≈C-sym (imaginaryExponentialIsPhase T y))))

imaginaryExponentialProductGivesPhaseProduct :
  (T : BishopSetoidComplexTranscendentals)
  (x y : BishopReal.ℝ) →
  expC T (pureImaginary (BishopReal._+_ x y))
    ≈C (expC T (pureImaginary x) *C expC T (pureImaginary y)) →
  imaginaryPhase T (BishopReal._+_ x y)
    ≈C (imaginaryPhase T x *C imaginaryPhase T y)
imaginaryExponentialProductGivesPhaseProduct T x y product =
  ≈C-trans
    (≈C-sym (imaginaryExponentialIsPhase T (BishopReal._+_ x y)))
    (≈C-trans
      product
      (mulCongruent
        (imaginaryExponentialIsPhase T x)
        (imaginaryExponentialIsPhase T y)))

imaginaryExponentialProductGivesAddition :
  (T : BishopSetoidComplexTranscendentals)
  (x y : BishopReal.ℝ) →
  expC T (pureImaginary (BishopReal._+_ x y))
    ≈C (expC T (pureImaginary x) *C expC T (pureImaginary y)) →
  BishopSineAdditionAt T x y
    × BishopCosineAdditionAt T x y
imaginaryExponentialProductGivesAddition T x y product =
  imaginaryPhaseProductGivesSineAddition T x y
    (imaginaryExponentialProductGivesPhaseProduct T x y product)
  ,
  imaginaryPhaseProductGivesCosineAddition T x y
    (imaginaryExponentialProductGivesPhaseProduct T x y product)
