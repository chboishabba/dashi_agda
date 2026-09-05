module DASHI.Physics.QuantumVacuum.CasimirOneSixthFactorisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- TRANSVERSE 1/6 FACTORISATION
--
-- The standard radial organization separates the coefficient into:
--   angular normalization:  1/(2*pi)
--   radial primitive/finite part: 1/3
-- so the purely rational denominator is 2 * 3 = 6.
--
-- This module owns only that compiler arithmetic.  It does not prove the
-- polar-measure theorem or the regulated radial integral evaluation.
------------------------------------------------------------------------

twoTimesThreeIsSix : 2 * 3 ≡ 6
twoTimesThreeIsSix = refl

record AngularHalfReceipt : Set₁ where
  field
    Scalar : Set
    angularInput : Set
    angularNormalizedValue : Scalar
    inverseTwoProduced : Set
    samePolarMeasureObject : Set
    reading : String

open AngularHalfReceipt public

record RadialThirdReceipt : Set₁ where
  field
    Scalar : Set
    radialInput : Set
    radialFinitePart : Scalar
    inverseThreeProduced : Set
    sameRegulatedRadialObject : Set
    reading : String

open RadialThirdReceipt public

record OneSixthAssembly : Set₁ where
  field
    angular : AngularHalfReceipt
    radial : RadialThirdReceipt
    sameTransverseCasimirObject : Set
    denominatorTwo : Nat
    denominatorThree : Nat
    denominatorSix : Nat
    denominatorTwoIs2 : denominatorTwo ≡ 2
    denominatorThreeIs3 : denominatorThree ≡ 3
    denominatorSixIs6 : denominatorSix ≡ 6
    productCompiler : denominatorTwo * denominatorThree ≡ denominatorSix
    reading : String

open OneSixthAssembly public

canonicalOneSixthDenominators :
  Σ Nat (λ two → Σ Nat (λ three → two * three ≡ 6))
canonicalOneSixthDenominators = 2 , (3 , refl)

data ArithmeticSixAutomaticallyProvesPolarMeasure : Set where
data ArithmeticSixAutomaticallyProvesRadialFinitePart : Set where

sixDoesNotProvePolarMeasure :
  ArithmeticSixAutomaticallyProvesPolarMeasure → ⊥
sixDoesNotProvePolarMeasure ()

sixDoesNotProveRadialFinitePart :
  ArithmeticSixAutomaticallyProvesRadialFinitePart → ⊥
sixDoesNotProveRadialFinitePart ()
