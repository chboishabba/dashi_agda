module DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CASIMIR 720 COEFFICIENT FACTORISATION, BIDI
--
-- A standard analytic organization of the ideal-plate calculation separates
-- two nontrivial analytic payments:
--
--   (1) the transverse continuum evaluation contributes the 1/6-type factor;
--   (2) the remaining longitudinal finite part is governed by the same-object
--       special value zeta(-3) = 1/120.
--
-- Once those two receipts are independently established on the literal Casimir
-- defect, 720 = 6 * 120 is arithmetic compiler output.  This module does not
-- assert either analytic receipt.
------------------------------------------------------------------------

sixTimes120Is720 : 6 * 120 ≡ 720
sixTimes120Is720 = refl

record TransverseSixCoefficientReceipt : Set₁ where
  field
    Scalar : Set
    transverseInput : Set
    transverseFinitePart : Scalar

    inverseSixCoefficientProduced : Set
    piPowerTransport : Set
    sameCasimirTransverseIntegral : Set

    reading : String

open TransverseSixCoefficientReceipt public

record ZetaMinusThree120Receipt : Set₁ where
  field
    Scalar : Set
    longitudinalInput : Set
    zetaMinusThreeValue : Scalar

    analyticContinuationOrEquivalentFinitePart : Set
    zetaMinusThreeEqualsOneOver120 : Set
    sameCasimirLongitudinalDefect : Set

    reading : String

open ZetaMinusThree120Receipt public

record Casimir720Assembly : Set₁ where
  field
    transverse : TransverseSixCoefficientReceipt
    longitudinal : ZetaMinusThree120Receipt

    sameSpectralObject : Set
    sameSeparationParameter : Set
    sameRenormalisationPresentation : Set

    sixFactor : Nat
    oneTwentyFactor : Nat
    combinedFactor : Nat

    sixFactorIs6 : sixFactor ≡ 6
    oneTwentyFactorIs120 : oneTwentyFactor ≡ 120
    combinedFactorIs720 : combinedFactor ≡ 720

    assemblyReading : String

open Casimir720Assembly public

canonicalArithmeticFactors :
  Σ Nat (λ six → Σ Nat (λ oneTwenty → six * oneTwenty ≡ 720))
canonicalArithmeticFactors = 6 , (120 , refl)

------------------------------------------------------------------------
-- BIDI reverse obligations.
------------------------------------------------------------------------

record Casimir720Obligations : Set₁ where
  field
    transverseIntegralProducesSix : Set
    longitudinalFinitePartProducesZetaMinusThree : Set
    zetaMinusThreeSpecialValueProduces120 : Set
    sameObjectTransverseLongitudinalWeld : Set
    piAndSeparationPowerTransport : Set
    reading : String

open Casimir720Obligations public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data Arithmetic720AutomaticallyProvesTransverseIntegral : Set where

data Arithmetic720AutomaticallyProvesZetaSpecialValue : Set where

data ForeignZetaMinusThreeReceiptAutomaticallyClosesCasimir : Set where

arithmeticDoesNotProveTransverseSix :
  Arithmetic720AutomaticallyProvesTransverseIntegral → ⊥
arithmeticDoesNotProveTransverseSix ()

arithmeticDoesNotProveZeta120 :
  Arithmetic720AutomaticallyProvesZetaSpecialValue → ⊥
arithmeticDoesNotProveZeta120 ()

foreignZetaReceiptNeedsCasimirWeld :
  ForeignZetaMinusThreeReceiptAutomaticallyClosesCasimir → ⊥
foreignZetaReceiptNeedsCasimirWeld ()

record Casimir720Status : Set where
  field
    sixTimes120ArithmeticOwned : Bool
    transverseSixAnalyticReceiptClosed : Bool
    zetaMinusThree120AnalyticReceiptClosed : Bool
    sameObjectAssemblyClosed : Bool

    sixTimes120ArithmeticOwnedIsTrue : sixTimes120ArithmeticOwned ≡ true
    transverseSixAnalyticReceiptClosedIsFalse :
      transverseSixAnalyticReceiptClosed ≡ false
    zetaMinusThree120AnalyticReceiptClosedIsFalse :
      zetaMinusThree120AnalyticReceiptClosed ≡ false
    sameObjectAssemblyClosedIsFalse : sameObjectAssemblyClosed ≡ false

open Casimir720Status public

canonicalCasimir720Status : Casimir720Status
canonicalCasimir720Status = record
  { sixTimes120ArithmeticOwned = true
  ; transverseSixAnalyticReceiptClosed = false
  ; zetaMinusThree120AnalyticReceiptClosed = false
  ; sameObjectAssemblyClosed = false
  ; sixTimes120ArithmeticOwnedIsTrue = refl
  ; transverseSixAnalyticReceiptClosedIsFalse = refl
  ; zetaMinusThree120AnalyticReceiptClosedIsFalse = refl
  ; sameObjectAssemblyClosedIsFalse = refl
  }
