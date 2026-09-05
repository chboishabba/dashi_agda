module DASHI.Physics.QuantumVacuum.CasimirZetaSourceBackedDefectCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Analysis.ZetaMinusThreeAnalyticCutsetExact as Analytic
import DASHI.Analysis.ZetaMinusThreeBernoulliArithmeticExact as Arithmetic
import DASHI.Analysis.ZetaMinusThreeSourceBackedConcreteCompilerExact as SourceZeta
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.CasimirZetaMinusThreeBidiExact as CasimirZeta
import DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact as C720

------------------------------------------------------------------------
-- SOURCE-BACKED LOCAL ZETA(-3) -> LITERAL CASIMIR LONGITUDINAL DEFECT
--
-- The analytic source theorem now produces an exact local zeta receipt before
-- this module begins.  This owner pays only the application-specific same-object
-- map from that local zeta value carrier into the transformed Casimir defect's
-- `ZetaValue` carrier.
------------------------------------------------------------------------

record CasimirZetaDefectCarrierWeld
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    problem : CasimirZeta.CasimirLongitudinalZetaProblem kernel

    localZetaCarrier : Analytic.RiemannZetaContinuationCarrier
    localZetaReceipt :
      Analytic.ZetaMinusThreeOneOver120Receipt localZetaCarrier

    DefectInput : Set
    defectInput : DefectInput

    localToProblemZetaValue :
      Analytic.Complex localZetaCarrier →
      CasimirZeta.ZetaValue problem

    problemMinusThreeEvaluationIsLocalZeta :
      CasimirZeta.evaluateZeta problem
        (CasimirZeta.zetaFunction problem)
        (CasimirZeta.minusThreePoint problem)
      ≡ localToProblemZetaValue
          (Analytic.zeta localZetaCarrier
            (Analytic.minusThree localZetaCarrier))

    sameZetaValueCarrierSemantics : Set
    sameZetaFunctionObject : Set
    sameMinusThreePoint : Set

    sameCasimirLongitudinalDefect :
      CasimirZeta.sameDefectAfterTransformation problem

    reading : String

open CasimirZetaDefectCarrierWeld public

problemOneOver120Value :
  ∀ {kernel} →
  (W : CasimirZetaDefectCarrierWeld kernel) →
  CasimirZeta.ZetaValue (problem W)
problemOneOver120Value W =
  localToProblemZetaValue W
    (Analytic.embedRational
      (localZetaCarrier W)
      Arithmetic.oneOver120)

problemZetaMinusThreeEqualsOneOver120 :
  ∀ {kernel} (W : CasimirZetaDefectCarrierWeld kernel) →
  CasimirZeta.evaluateZeta (problem W)
    (CasimirZeta.zetaFunction (problem W))
    (CasimirZeta.minusThreePoint (problem W))
  ≡ problemOneOver120Value W
problemZetaMinusThreeEqualsOneOver120 W =
  trans
    (problemMinusThreeEvaluationIsLocalZeta W)
    (cong
      (localToProblemZetaValue W)
      (Analytic.zetaMinusThreeEqualsOneOver120 (localZetaReceipt W)))

legacyAnalyticReceipt :
  ∀ {kernel} →
  CasimirZetaDefectCarrierWeld kernel →
  Arithmetic.ZetaMinusThreeBernoulliAnalyticReceipt
legacyAnalyticReceipt W =
  SourceZeta.asLegacyBernoulliAnalyticReceipt (localZetaReceipt W)

compileCasimirZetaMinusThreeClosure :
  ∀ {kernel} (W : CasimirZetaDefectCarrierWeld kernel) →
  CasimirZeta.CasimirZetaMinusThreeClosure kernel (problem W)
compileCasimirZetaMinusThreeClosure W = record
  { CasimirZeta.bernoulliAnalyticReceipt = legacyAnalyticReceipt W
  ; CasimirZeta.sameZetaValueCarrier = sameZetaValueCarrierSemantics W
  ; CasimirZeta.sameZetaObject = sameZetaFunctionObject W
  ; CasimirZeta.rationalValueTransport =
      problemZetaMinusThreeEqualsOneOver120 W
  ; CasimirZeta.producesCasimirOneOver120 =
      problemZetaMinusThreeEqualsOneOver120 W
  ; CasimirZeta.sameLongitudinalDefect = sameCasimirLongitudinalDefect W
  ; CasimirZeta.reading =
      "The source-backed local zeta(-3)=1/120 receipt is transported onto the literal transformed Casimir longitudinal defect value carrier."
  }

compileCasimirZeta120Receipt :
  ∀ {kernel} (W : CasimirZetaDefectCarrierWeld kernel) →
  C720.ZetaMinusThree120Receipt
compileCasimirZeta120Receipt W = record
  { C720.Scalar = CasimirZeta.ZetaValue (problem W)
  ; C720.longitudinalInput = DefectInput W
  ; C720.zetaMinusThreeValue =
      CasimirZeta.evaluateZeta (problem W)
        (CasimirZeta.zetaFunction (problem W))
        (CasimirZeta.minusThreePoint (problem W))
  ; C720.analyticContinuationOrEquivalentFinitePart =
      Arithmetic.analyticContinuationAtMinusThree (legacyAnalyticReceipt W)
  ; C720.zetaMinusThreeEqualsOneOver120 =
      problemZetaMinusThreeEqualsOneOver120 W
  ; C720.sameCasimirLongitudinalDefect = sameCasimirLongitudinalDefect W
  ; C720.reading =
      "Same-object source-backed zeta(-3)=1/120 receipt for the Casimir longitudinal defect."
  }

compileCasimirZeta120Producer :
  ∀ {kernel} (W : CasimirZetaDefectCarrierWeld kernel) →
  CasimirZeta.CasimirZeta120Producer kernel
compileCasimirZeta120Producer W = record
  { CasimirZeta.problem = problem W
  ; CasimirZeta.closure = compileCasimirZetaMinusThreeClosure W
  ; CasimirZeta.receipt = compileCasimirZeta120Receipt W
  ; CasimirZeta.receiptUsesProblemDefect = sameCasimirLongitudinalDefect W
  ; CasimirZeta.reading =
      "Concrete source-backed zeta receipt compiled onto the same Casimir longitudinal defect consumed by the 720 assembly lane."
  }

record ReverseCasimirZetaDefectObligations : Set where
  field
    transformedDefectZetaCarrierMap : Set
    sameZetaFunctionObject : Set
    sameMinusThreePoint : Set
    sameCasimirLongitudinalDefect : Set

open ReverseCasimirZetaDefectObligations public

data ZetaValueEqualityAutomaticallyIdentifiesCasimirDefect : Set where

valueStillNeedsDefectWeld :
  ZetaValueEqualityAutomaticallyIdentifiesCasimirDefect → ⊥
valueStillNeedsDefectWeld ()

record Status : Set where
  field
    sourceBackedLocalZeta120CompilerOwned : Bool
    legacyAnalyticCompatibilityCompilerOwned : Bool
    casimirZetaClosureCompilerOwned : Bool
    casimir720ZetaReceiptCompilerOwned : Bool
    defectSameObjectWeldStillRequired : Bool

    sourceBackedLocalZeta120CompilerOwnedIsTrue : sourceBackedLocalZeta120CompilerOwned ≡ true
    legacyAnalyticCompatibilityCompilerOwnedIsTrue : legacyAnalyticCompatibilityCompilerOwned ≡ true
    casimirZetaClosureCompilerOwnedIsTrue : casimirZetaClosureCompilerOwned ≡ true
    casimir720ZetaReceiptCompilerOwnedIsTrue : casimir720ZetaReceiptCompilerOwned ≡ true
    defectSameObjectWeldStillRequiredIsTrue : defectSameObjectWeldStillRequired ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { sourceBackedLocalZeta120CompilerOwned = true
  ; legacyAnalyticCompatibilityCompilerOwned = true
  ; casimirZetaClosureCompilerOwned = true
  ; casimir720ZetaReceiptCompilerOwned = true
  ; defectSameObjectWeldStillRequired = true
  ; sourceBackedLocalZeta120CompilerOwnedIsTrue = refl
  ; legacyAnalyticCompatibilityCompilerOwnedIsTrue = refl
  ; casimirZetaClosureCompilerOwnedIsTrue = refl
  ; casimir720ZetaReceiptCompilerOwnedIsTrue = refl
  ; defectSameObjectWeldStillRequiredIsTrue = refl
  }
