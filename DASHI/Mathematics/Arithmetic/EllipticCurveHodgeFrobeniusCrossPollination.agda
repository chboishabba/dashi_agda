module DASHI.Mathematics.Arithmetic.EllipticCurveHodgeFrobeniusCrossPollination where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- Claire Voisin,
-- "Hodge Theory and Complex Algebraic Geometry I".
-- DOI: 10.1017/CBO9780511615344.
--
-- DASHI CONTRIBUTION
--
-- Cross-pollinate the BSD elliptic carrier with the Hodge carrier.  The finite
-- Hodge diamond of a complex elliptic curve is recorded exactly:
--
--       1
--     1   1
--       1
--
-- so b0=1, b1=2, b2=1.  A bridge record keeps the complex realization,
-- singular/de Rham comparison, Hodge decomposition, rational model and
-- finite-field Frobenius reduction as separate data.
--
-- Equality of the characteristic-zero and finite-field realizations, comparison
-- isomorphisms, good reduction and compatibility of Frobenius with cohomology
-- are not inferred from the matching finite dimensions.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as H
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as E

data EllipticBidegree : Set where
  elliptic00 elliptic10 elliptic01 elliptic11 : EllipticBidegree

ellipticConjugateDegree : EllipticBidegree → EllipticBidegree
ellipticConjugateDegree elliptic00 = elliptic00
ellipticConjugateDegree elliptic10 = elliptic01
ellipticConjugateDegree elliptic01 = elliptic10
ellipticConjugateDegree elliptic11 = elliptic11

ellipticHodgeNumber : EllipticBidegree → Nat
ellipticHodgeNumber elliptic00 = 1
ellipticHodgeNumber elliptic10 = 1
ellipticHodgeNumber elliptic01 = 1
ellipticHodgeNumber elliptic11 = 1

ellipticHodgeConjugationSymmetry : ∀ degree →
  ellipticHodgeNumber (ellipticConjugateDegree degree)
  ≡ ellipticHodgeNumber degree
ellipticHodgeConjugationSymmetry elliptic00 = refl
ellipticHodgeConjugationSymmetry elliptic10 = refl
ellipticHodgeConjugationSymmetry elliptic01 = refl
ellipticHodgeConjugationSymmetry elliptic11 = refl

ellipticBetti0 ellipticBetti1 ellipticBetti2 : Nat
ellipticBetti0 = ellipticHodgeNumber elliptic00
ellipticBetti1 =
  ellipticHodgeNumber elliptic10 + ellipticHodgeNumber elliptic01
ellipticBetti2 = ellipticHodgeNumber elliptic11

ellipticBettiNumbers :
  ellipticBetti0 ≡ 1
  × ellipticBetti1 ≡ 2
  × ellipticBetti2 ≡ 1
ellipticBettiNumbers = refl , refl , refl

record EllipticHodgeFrobeniusBridge : Setω where
  field
    rationalCurve : E.ShortWeierstrassCurve
    complexVariety : H.SmoothProjectiveComplexVariety
    complexDimensionIsOne : H.complexDimension complexVariety ≡ 1
    comparison : H.SingularDeRhamComparison complexVariety
    hodge : H.HodgeDecomposition complexVariety comparison
    hodgeDiamondIdentified : Set

    reductionPrime : Nat
    arithmeticFrobenius : E.ArithmeticFrobeniusDatum
    arithmeticFrobeniusAtReductionPrime :
      E.ArithmeticFrobeniusDatum.prime arithmeticFrobenius ≡ reductionPrime

    goodReduction : Set
    etaleCohomologyCarrier : Set
    frobeniusActsOnEtaleCohomology : Set
    characteristicPolynomialMatchesLocalEulerFactor : Set
    comparisonAcrossCharacteristics : Set

record ConcreteCurveP5HodgeBridge : Setω where
  field
    bridge : EllipticHodgeFrobeniusBridge
    rationalCurveIsY2X3MinusX :
      EllipticHodgeFrobeniusBridge.rationalCurve bridge
      ≡ E.curveY2EqualsX3MinusX
    reductionPrimeIsFive :
      EllipticHodgeFrobeniusBridge.reductionPrime bridge ≡ 5
    frobeniusDatumIsP5 :
      EllipticHodgeFrobeniusBridge.arithmeticFrobenius bridge
      ≡ E.p5FrobeniusDatum

data EllipticRealization : Set where
  rationalWeierstrassRealization
  complexHodgeRealization
  finiteFieldFrobeniusRealization
  etaleCohomologyRealization

complexAndFiniteFieldRealizationsAreDistinct :
  complexHodgeRealization ≡ finiteFieldFrobeniusRealization → ⊥
complexAndFiniteFieldRealizationsAreDistinct ()

matchingBettiDimensionsDoNotGiveComparison :
  complexHodgeRealization ≡ etaleCohomologyRealization → ⊥
matchingBettiDimensionsDoNotGiveComparison ()
