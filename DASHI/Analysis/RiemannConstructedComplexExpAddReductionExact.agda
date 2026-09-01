module DASHI.Analysis.RiemannConstructedComplexExpAddReductionExact where

open import Agda.Builtin.Equality using (_≡_; refl; trans; cong)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
import DASHI.Analysis.RiemannConstructedComplexCharacterCoreExact as CharacterCore

------------------------------------------------------------------------
-- BIDI DESCENT FOR H_X^exp
--
-- The ordinary power-series layer already carries the real exponential
-- addition law and the sine/cosine addition laws.  The remaining gap between
-- those scalar theorems and
--
--   expC (z + w) = expC z * expC w
--
-- is therefore a Cartesian ring-normalisation theorem for the concrete pair
-- representation.  We expose exactly the two scalar component equations and
-- derive the complex homomorphism from expCartesian.
------------------------------------------------------------------------

record CartesianComplexExpProductNormalisation
    (C : ConstructedComplexPackage) : Set₁ where
  private
    R = real (realPackage C)
    E = exponential (realPackage C)
    CE = complexExponential C
  field
    realComponentNormalisation :
      (x y a b : Real R) →
      _*_ R
        (exp E (_+_ R x a))
        (cos CE (_+_ R y b))
      ≡ _-_ R
          (_*_ R (_*_ R (exp E x) (cos CE y))
                 (_*_ R (exp E a) (cos CE b)))
          (_*_ R (_*_ R (exp E x) (sin CE y))
                 (_*_ R (exp E a) (sin CE b)))

    imaginaryComponentNormalisation :
      (x y a b : Real R) →
      _*_ R
        (exp E (_+_ R x a))
        (sin CE (_+_ R y b))
      ≡ _+_ R
          (_*_ R (_*_ R (exp E x) (cos CE y))
                 (_*_ R (exp E a) (sin CE b)))
          (_*_ R (_*_ R (exp E x) (sin CE y))
                 (_*_ R (exp E a) (cos CE b)))

open CartesianComplexExpProductNormalisation public

complexPairExt :
  ∀ {R : ConstructedOrderedCompleteReal}
    {x y a b : Real R} →
  x ≡ a → y ≡ b →
  complex x y ≡ complex a b
complexPairExt refl refl = refl

expAddCFromCartesianNormalisation :
  (C : ConstructedComplexPackage) →
  CartesianComplexExpProductNormalisation C →
  (z w : ComplexPair (real (realPackage C))) →
  expC (complexExponential C) (_+C_ z w)
  ≡ _*C_ (expC (complexExponential C) z)
           (expC (complexExponential C) w)
expAddCFromCartesianNormalisation C N (complex x y) (complex a b)
  rewrite expCartesian (complexExponential C) (_+_ (real (realPackage C)) x a)
            (_+_ (real (realPackage C)) y b)
        | expCartesian (complexExponential C) x y
        | expCartesian (complexExponential C) a b
  = complexPairExt
      (realComponentNormalisation N x y a b)
      (imaginaryComponentNormalisation N x y a b)

complexExponentialHomomorphismFromCartesianNormalisation :
  (C : ConstructedComplexPackage) →
  CartesianComplexExpProductNormalisation C →
  CharacterCore.ComplexExponentialHomomorphism C
complexExponentialHomomorphismFromCartesianNormalisation C N =
  record
    { expAddC = expAddCFromCartesianNormalisation C N
    }

record ComplexExpAddReductionBoundary : Set where
  constructor complex-exp-add-reduction-boundary
  field
    realExpAddAlreadyOwnedInConstructedExponential : Bool
    realExpAddAlreadyOwnedInConstructedExponentialIsTrue :
      realExpAddAlreadyOwnedInConstructedExponential ≡ true

    powerSeriesLayerAlreadyOwnsSinCosAddition : Bool
    powerSeriesLayerAlreadyOwnsSinCosAdditionIsTrue :
      powerSeriesLayerAlreadyOwnsSinCosAddition ≡ true

    complexExpAddStillNeedsIndependentTranscendentalAxiom : Bool
    complexExpAddStillNeedsIndependentTranscendentalAxiomIsFalse :
      complexExpAddStillNeedsIndependentTranscendentalAxiom ≡ false

    cartesianRingNormalisationStillRequired : Bool
    cartesianRingNormalisationStillRequiredIsTrue :
      cartesianRingNormalisationStillRequired ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    nextTheorem : String

complexExpAddReductionBoundary : ComplexExpAddReductionBoundary
complexExpAddReductionBoundary =
  complex-exp-add-reduction-boundary
    true refl
    true refl
    false refl
    true refl
    false refl
    "Derive the two Cartesian component normalisations from real expAdd, sinAdd, cosAdd and ordinary constructed-real ring laws; expC additivity then follows by pair extensionality."
