module DASHI.Analysis.ZetaMinusThreeSourceBackedConcreteCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Analysis.ZetaEulerMaclaurinContinuationSourceAuthorityExact as Euler
import DASHI.Analysis.ZetaMinusThreeSourceAuthorityExact as Special
import DASHI.Analysis.ZetaMinusThreeAnalyticCutsetExact as Analytic
import DASHI.Analysis.ZetaMinusThreeBernoulliArithmeticExact as Arithmetic

------------------------------------------------------------------------
-- SOURCE-BACKED ZETA(-3) -> CONCRETE LOCAL ANALYTIC RECORD
------------------------------------------------------------------------

eulerMaclaurinSourceClaim : Transport.SourceBackedClaim
eulerMaclaurinSourceClaim = record
  { Transport.SourceClaim =
      Euler.eulerMaclaurinRepresentationStated
        Euler.canonicalZetaEulerMaclaurinAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName = Euler.sourceName Euler.canonicalZetaEulerMaclaurinAuthority
  ; Transport.sourceLocator = Euler.sourceLocator Euler.canonicalZetaEulerMaclaurinAuthority
  ; Transport.reading = "DLMF Euler--Maclaurin continuation source authority."
  }

negativeIntegerSourceClaim : Transport.SourceBackedClaim
negativeIntegerSourceClaim = record
  { Transport.SourceClaim =
      Special.zetaMinusThreeEqualsMinusB4OverFour Special.nistDLMFZetaMinusThreeAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName = Special.sourceName Special.nistDLMFZetaMinusThreeAuthority
  ; Transport.sourceLocator = Special.sourceLocator Special.nistDLMFZetaMinusThreeAuthority
  ; Transport.reading = "DLMF negative-integer Bernoulli special-value source authority at n=3."
  }

record ConcreteEulerMaclaurinWeld
    (Z : Analytic.RiemannZetaContinuationCarrier) : Set₁ where
  field
    sameContinuedZetaBernoulliConventionAndRemainder : Set
    sourceToConcreteAnalyticReceipt :
      Transport.SourceClaim eulerMaclaurinSourceClaim →
      sameContinuedZetaBernoulliConventionAndRemainder →
      Analytic.BernoulliFourAnalyticReceipt Z
    reading : String

open ConcreteEulerMaclaurinWeld public

asConcreteEulerMaclaurinTarget :
  (Z : Analytic.RiemannZetaContinuationCarrier) →
  ConcreteEulerMaclaurinWeld Z →
  Transport.LocalTheoremTarget eulerMaclaurinSourceClaim
asConcreteEulerMaclaurinTarget Z W = record
  { Transport.LocalClaim = Analytic.BernoulliFourAnalyticReceipt Z
  ; Transport.sameMathematicalObject = sameContinuedZetaBernoulliConventionAndRemainder W
  ; Transport.sourceSemanticsToLocal = sourceToConcreteAnalyticReceipt W
  ; Transport.reading = reading W
  }

compileConcreteAnalyticReceipt :
  (Z : Analytic.RiemannZetaContinuationCarrier) →
  (W : ConcreteEulerMaclaurinWeld Z) →
  sameContinuedZetaBernoulliConventionAndRemainder W →
  Analytic.BernoulliFourAnalyticReceipt Z
compileConcreteAnalyticReceipt Z W weld =
  Transport.transportSourceBackedTheorem
    eulerMaclaurinSourceClaim
    (asConcreteEulerMaclaurinTarget Z W)
    (record { Transport.objectWeld = weld })

record ConcreteMinusThreeSpecialValueWeld
    (Z : Analytic.RiemannZetaContinuationCarrier) : Set₁ where
  field
    analyticReceipt : Analytic.BernoulliFourAnalyticReceipt Z
    sameZetaBernoulliAndRationalEmbedding : Set
    sourceToZetaMinusThreeOneOver120 :
      Transport.SourceClaim negativeIntegerSourceClaim →
      sameZetaBernoulliAndRationalEmbedding →
      Analytic.zeta Z (Analytic.minusThree Z)
      ≡ Analytic.embedRational Z Arithmetic.oneOver120
    reading : String

open ConcreteMinusThreeSpecialValueWeld public

asConcreteSpecialValueTarget :
  (Z : Analytic.RiemannZetaContinuationCarrier) →
  ConcreteMinusThreeSpecialValueWeld Z →
  Transport.LocalTheoremTarget negativeIntegerSourceClaim
asConcreteSpecialValueTarget Z W = record
  { Transport.LocalClaim =
      Analytic.zeta Z (Analytic.minusThree Z)
      ≡ Analytic.embedRational Z Arithmetic.oneOver120
  ; Transport.sameMathematicalObject = sameZetaBernoulliAndRationalEmbedding W
  ; Transport.sourceSemanticsToLocal = sourceToZetaMinusThreeOneOver120 W
  ; Transport.reading = reading W
  }

compileConcreteZetaMinusThreeOneOver120 :
  (Z : Analytic.RiemannZetaContinuationCarrier) →
  (W : ConcreteMinusThreeSpecialValueWeld Z) →
  sameZetaBernoulliAndRationalEmbedding W →
  Analytic.ZetaMinusThreeOneOver120Receipt Z
compileConcreteZetaMinusThreeOneOver120 Z W weld = record
  { Analytic.analytic = analyticReceipt W
  ; Analytic.rationalCompiler = Arithmetic.bernoulliB4CompilerProducesOneOver120
  ; Analytic.rationalCompilerUsesB4 =
      Arithmetic.minusB4OverFour ≡ Arithmetic.oneOver120
  ; Analytic.zetaMinusThreeEqualsOneOver120 =
      Transport.transportSourceBackedTheorem
        negativeIntegerSourceClaim
        (asConcreteSpecialValueTarget Z W)
        (record { Transport.objectWeld = weld })
  ; Analytic.reading =
      "Source-backed negative-integer theorem plus machine-owned Bernoulli arithmetic compiles zeta(-3)=1/120 on this exact local carrier."
  }

------------------------------------------------------------------------
-- COMPATIBILITY COMPILER TO THE OLDER GENERIC ANALYTIC RECEIPT
------------------------------------------------------------------------

asLegacyBernoulliAnalyticReceipt :
  ∀ {Z : Analytic.RiemannZetaContinuationCarrier} →
  Analytic.ZetaMinusThreeOneOver120Receipt Z →
  Arithmetic.ZetaMinusThreeBernoulliAnalyticReceipt
asLegacyBernoulliAnalyticReceipt {Z} receipt = record
  { Arithmetic.ZetaValue = Analytic.Complex Z
  ; Arithmetic.zetaMinusThree = Analytic.zeta Z (Analytic.minusThree Z)
  ; Arithmetic.BernoulliValue = Analytic.Bernoulli (Analytic.analytic receipt)
  ; Arithmetic.B4 = Analytic.B4 (Analytic.analytic receipt)
  ; Arithmetic.analyticContinuationAtMinusThree =
      Analytic.analyticContinuationExistsAtMinusThree (Analytic.analytic receipt)
  ; Arithmetic.bernoulliSpecialValueFormulaAtFour =
      Analytic.bernoulliSpecialValueTheorem (Analytic.analytic receipt)
  ; Arithmetic.bernoulliB4IdentifiedWithMinusOneOver30 =
      Analytic.b4EqualsMinusOneOverThirty (Analytic.analytic receipt)
  ; Arithmetic.zetaValueTransportToRational =
      Analytic.zeta Z (Analytic.minusThree Z)
      ≡ Analytic.embedRational Z Arithmetic.oneOver120
  }

record ReverseConcreteZetaObligations : Set where
  field
    localContinuationCarrierIdentified : Set
    localBernoulliConventionIdentified : Set
    localEulerMaclaurinRemainderSemanticsIdentified : Set
    localRationalEmbeddingIdentified : Set
    sameZetaObjectAcrossBothSourceClaims : Set

open ReverseConcreteZetaObligations public

data EulerMaclaurinCitationAutomaticallyConstructsLocalCarrier : Set where
data EqualRationalValueAutomaticallyIdentifiesContinuedZeta : Set where

citationDoesNotConstructCarrier : EulerMaclaurinCitationAutomaticallyConstructsLocalCarrier → ⊥
citationDoesNotConstructCarrier ()

valueDoesNotIdentifyZetaObject : EqualRationalValueAutomaticallyIdentifiesContinuedZeta → ⊥
valueDoesNotIdentifyZetaObject ()

record Status : Set where
  field
    eulerMaclaurinSourceTransportToConcreteReceiptOwned : Bool
    negativeIntegerSourceTransportToConcreteReceiptOwned : Bool
    bernoulliArithmeticCompilerOwned : Bool
    legacyAnalyticReceiptCompilerOwned : Bool
    sameObjectCarrierWeldStillRequired : Bool

    eulerMaclaurinSourceTransportToConcreteReceiptOwnedIsTrue :
      eulerMaclaurinSourceTransportToConcreteReceiptOwned ≡ true
    negativeIntegerSourceTransportToConcreteReceiptOwnedIsTrue :
      negativeIntegerSourceTransportToConcreteReceiptOwned ≡ true
    bernoulliArithmeticCompilerOwnedIsTrue : bernoulliArithmeticCompilerOwned ≡ true
    legacyAnalyticReceiptCompilerOwnedIsTrue : legacyAnalyticReceiptCompilerOwned ≡ true
    sameObjectCarrierWeldStillRequiredIsTrue : sameObjectCarrierWeldStillRequired ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { eulerMaclaurinSourceTransportToConcreteReceiptOwned = true
  ; negativeIntegerSourceTransportToConcreteReceiptOwned = true
  ; bernoulliArithmeticCompilerOwned = true
  ; legacyAnalyticReceiptCompilerOwned = true
  ; sameObjectCarrierWeldStillRequired = true
  ; eulerMaclaurinSourceTransportToConcreteReceiptOwnedIsTrue = refl
  ; negativeIntegerSourceTransportToConcreteReceiptOwnedIsTrue = refl
  ; bernoulliArithmeticCompilerOwnedIsTrue = refl
  ; legacyAnalyticReceiptCompilerOwnedIsTrue = refl
  ; sameObjectCarrierWeldStillRequiredIsTrue = refl
  }
