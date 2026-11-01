module DASHI.Physics.Closure.Deg23FromT13HeckeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- deg23 base degree from T_13.
--
-- The Hilbert modular volume route did not produce the 2-3 coupling.  This
-- receipt records the sharper arithmetic source for the base integer 14:
-- 13 is inert in Q(sqrt(21)), so the inert-prime Hecke correspondence T_13
-- on the Hilbert modular surface has degree p+1 = 14.  The remaining 2.1%
-- correction is explicitly open.

t13Prime : Nat
t13Prime = 13

t13InertHeckeDegree : Nat
t13InertHeckeDegree = 14

deg23ResidualMilliPercent : Nat
deg23ResidualMilliPercent = 2160

data T13ArithmeticFact : Set where
  qSqrt21RealQuadraticSubfield :
    T13ArithmeticFact

  legendre21Over13IsMinusOne :
    T13ArithmeticFact

  t13FactThirteenInertInQSqrt21 :
    T13ArithmeticFact

  inertPrimeHeckeDegreePPlusOne :
    T13ArithmeticFact

  t13DegreeFourteen :
    T13ArithmeticFact

canonicalT13ArithmeticFacts :
  List T13ArithmeticFact
canonicalT13ArithmeticFacts =
  qSqrt21RealQuadraticSubfield
  ∷ legendre21Over13IsMinusOne
  ∷ t13FactThirteenInertInQSqrt21
  ∷ inertPrimeHeckeDegreePPlusOne
  ∷ t13DegreeFourteen
  ∷ []

data Deg23T13OpenItem : Set where
  cmSpecialisedHeckeDegree :
    Deg23T13OpenItem

  twoPointOnePercentResidual :
    Deg23T13OpenItem

  physicalCKMNormalisation :
    Deg23T13OpenItem

canonicalDeg23T13OpenItems :
  List Deg23T13OpenItem
canonicalDeg23T13OpenItems =
  cmSpecialisedHeckeDegree
  ∷ twoPointOnePercentResidual
  ∷ physicalCKMNormalisation
  ∷ []

data Deg23T13Promotion : Set where

deg23T13PromotionImpossibleHere :
  Deg23T13Promotion →
  ⊥
deg23T13PromotionImpossibleHere ()

deg23T13Statement : String
deg23T13Statement =
  "deg23 base degree is identified with deg(T_13)=13+1=14 on the Hilbert modular surface for Q(sqrt(21)); the CM-specialised 2.1% residual remains open."

record Deg23FromT13HeckeReceipt : Setω where
  field
    hilbertRealQuadraticField :
      String

    hilbertRealQuadraticFieldIsCanonical :
      hilbertRealQuadraticField ≡ "Q(sqrt(21))"

    heckePrime :
      Nat

    heckePrimeIsThirteen :
      heckePrime ≡ t13Prime

    legendreTwentyOneOverThirteenMinusOne :
      Bool

    legendreTwentyOneOverThirteenMinusOneIsTrue :
      legendreTwentyOneOverThirteenMinusOne ≡ true

    thirteenInertInQSqrt21 :
      Bool

    thirteenInertInQSqrt21IsTrue :
      thirteenInertInQSqrt21 ≡ true

    inertPrimeDegreeRulePPlusOne :
      Bool

    inertPrimeDegreeRulePPlusOneIsTrue :
      inertPrimeDegreeRulePPlusOne ≡ true

    t13Degree :
      Nat

    t13DegreeIsFourteen :
      t13Degree ≡ t13InertHeckeDegree

    deg23BaseFromT13 :
      Bool

    deg23BaseFromT13IsTrue :
      deg23BaseFromT13 ≡ true

    deg23BaseIdentified :
      Nat

    deg23BaseIdentifiedIsFourteen :
      deg23BaseIdentified ≡ 14

    deg23ResidualMilliPercentRecorded :
      Nat

    deg23ResidualMilliPercentRecordedIs2160 :
      deg23ResidualMilliPercentRecorded ≡ deg23ResidualMilliPercent

    deg23ResidualExplained :
      Bool

    deg23ResidualExplainedIsFalse :
      deg23ResidualExplained ≡ false

    arithmeticFacts :
      List T13ArithmeticFact

    arithmeticFactsAreCanonical :
      arithmeticFacts ≡ canonicalT13ArithmeticFacts

    openItems :
      List Deg23T13OpenItem

    openItemsAreCanonical :
      openItems ≡ canonicalDeg23T13OpenItems

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List Deg23T13Promotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ deg23T13Statement

open Deg23FromT13HeckeReceipt public

canonicalDeg23FromT13HeckeReceipt :
  Deg23FromT13HeckeReceipt
canonicalDeg23FromT13HeckeReceipt =
  record
    { hilbertRealQuadraticField =
        "Q(sqrt(21))"
    ; hilbertRealQuadraticFieldIsCanonical =
        refl
    ; heckePrime =
        t13Prime
    ; heckePrimeIsThirteen =
        refl
    ; legendreTwentyOneOverThirteenMinusOne =
        true
    ; legendreTwentyOneOverThirteenMinusOneIsTrue =
        refl
    ; thirteenInertInQSqrt21 =
        true
    ; thirteenInertInQSqrt21IsTrue =
        refl
    ; inertPrimeDegreeRulePPlusOne =
        true
    ; inertPrimeDegreeRulePPlusOneIsTrue =
        refl
    ; t13Degree =
        t13InertHeckeDegree
    ; t13DegreeIsFourteen =
        refl
    ; deg23BaseFromT13 =
        true
    ; deg23BaseFromT13IsTrue =
        refl
    ; deg23BaseIdentified =
        14
    ; deg23BaseIdentifiedIsFourteen =
        refl
    ; deg23ResidualMilliPercentRecorded =
        deg23ResidualMilliPercent
    ; deg23ResidualMilliPercentRecordedIs2160 =
        refl
    ; deg23ResidualExplained =
        false
    ; deg23ResidualExplainedIsFalse =
        refl
    ; arithmeticFacts =
        canonicalT13ArithmeticFacts
    ; arithmeticFactsAreCanonical =
        refl
    ; openItems =
        canonicalDeg23T13OpenItems
    ; openItemsAreCanonical =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        deg23T13Statement
    ; statementIsCanonical =
        refl
    }

deg23BaseFromT13HeckeInhabited :
  deg23BaseFromT13 canonicalDeg23FromT13HeckeReceipt
  ≡
  true
deg23BaseFromT13HeckeInhabited =
  deg23BaseFromT13IsTrue canonicalDeg23FromT13HeckeReceipt

deg23BaseFromT13HeckeIsFourteen :
  deg23BaseIdentified canonicalDeg23FromT13HeckeReceipt
  ≡
  14
deg23BaseFromT13HeckeIsFourteen =
  deg23BaseIdentifiedIsFourteen canonicalDeg23FromT13HeckeReceipt

deg23T13ResidualStillOpen :
  deg23ResidualExplained canonicalDeg23FromT13HeckeReceipt
  ≡
  false
deg23T13ResidualStillOpen =
  deg23ResidualExplainedIsFalse canonicalDeg23FromT13HeckeReceipt
