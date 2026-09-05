module DASHI.Physics.QuantumVacuum.CasimirZetaDefectTransformationTraceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (trans; cong)

import DASHI.Analysis.ZetaMinusThreeAnalyticCutsetExact as Analytic
import DASHI.Analysis.ZetaMinusThreeBernoulliArithmeticExact as Arithmetic
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateRegulatedDifferenceBidiExact as Difference
import DASHI.Physics.QuantumVacuum.CasimirZetaMinusThreeBidiExact as CasimirZeta
import DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact as C720

------------------------------------------------------------------------
-- PROOF-BEARING LONGITUDINAL DEFECT -> ZETA TRANSFORMATION TRACE
--
-- Numerical agreement is not same-object identity.  This trace pins one
-- literal parameter/integrand of the discrete-minus-continuum Casimir defect,
-- maps its scalar value into the zeta carrier, and requires inhabited receipts
-- that the discrete term, continuum reference, subtraction convention and
-- finite-part transformation are the same physical/analytic object.
------------------------------------------------------------------------

record LongitudinalDefectTransformationTrace
    (kernel : Casimir.CasimirScalarModel)
    (P : CasimirZeta.CasimirLongitudinalZetaProblem kernel) : Set₁ where
  field
    parameter : Difference.Parameter (CasimirZeta.defect P)
    integrand : Difference.Integrand (CasimirZeta.defect P)

    originalDefectValue : Casimir.Scalar kernel
    originalDefectValueIsLiteralDefect :
      originalDefectValue ≡
      Difference.defect (CasimirZeta.defect P) parameter integrand

    scalarToZetaValue :
      Casimir.Scalar kernel → CasimirZeta.ZetaValue P

    transformedDefectIsTransportedOriginal :
      CasimirZeta.transformedDefectValue P ≡
      scalarToZetaValue originalDefectValue

    DiscreteLongitudinalTermPreserved : Set
    discreteLongitudinalTermPreservedEvidence :
      DiscreteLongitudinalTermPreserved

    ContinuumReferencePreserved : Set
    continuumReferencePreservedEvidence : ContinuumReferencePreserved

    SubtractionConventionPreserved : Set
    subtractionConventionPreservedEvidence : SubtractionConventionPreserved

    SeparationAndLongitudinalParameterPreserved : Set
    separationAndLongitudinalParameterPreservedEvidence :
      SeparationAndLongitudinalParameterPreserved

    RegulatorOrFinitePartPresentationPreserved : Set
    regulatorOrFinitePartPresentationPreservedEvidence :
      RegulatorOrFinitePartPresentationPreserved

    reading : String

open LongitudinalDefectTransformationTrace public

------------------------------------------------------------------------
-- Proof-bearing source-backed zeta value on the transformed literal defect.
------------------------------------------------------------------------

record ProofBearingCasimirZeta120
    (kernel : Casimir.CasimirScalarModel)
    (P : CasimirZeta.CasimirLongitudinalZetaProblem kernel)
    (T : LongitudinalDefectTransformationTrace kernel P) : Set₁ where
  field
    localZetaCarrier : Analytic.RiemannZetaContinuationCarrier
    localZetaReceipt : Analytic.ZetaMinusThreeOneOver120Receipt localZetaCarrier

    localToProblemZetaValue :
      Analytic.Complex localZetaCarrier → CasimirZeta.ZetaValue P

    problemMinusThreeEvaluationIsLocalZeta :
      CasimirZeta.evaluateZeta P
        (CasimirZeta.zetaFunction P)
        (CasimirZeta.minusThreePoint P)
      ≡ localToProblemZetaValue
          (Analytic.zeta localZetaCarrier
            (Analytic.minusThree localZetaCarrier))

    LocalRationalTransportIsSameCarrierMap : Set
    localRationalTransportIsSameCarrierMapEvidence :
      LocalRationalTransportIsSameCarrierMap

    reading : String

open ProofBearingCasimirZeta120 public

problemOneOver120Value :
  ∀ {kernel P T} →
  ProofBearingCasimirZeta120 kernel P T →
  CasimirZeta.ZetaValue P
problemOneOver120Value Z =
  localToProblemZetaValue Z
    (Analytic.embedRational
      (localZetaCarrier Z)
      Arithmetic.oneOver120)

problemZetaMinusThreeEqualsOneOver120 :
  ∀ {kernel P T} →
  (Z : ProofBearingCasimirZeta120 kernel P T) →
  CasimirZeta.evaluateZeta P
    (CasimirZeta.zetaFunction P)
    (CasimirZeta.minusThreePoint P)
  ≡ problemOneOver120Value Z
problemZetaMinusThreeEqualsOneOver120 Z =
  trans
    (problemMinusThreeEvaluationIsLocalZeta Z)
    (cong
      (localToProblemZetaValue Z)
      (Analytic.zetaMinusThreeEqualsOneOver120 (localZetaReceipt Z)))

transformedLiteralDefectEqualsOneOver120 :
  ∀ {kernel P T} →
  (Z : ProofBearingCasimirZeta120 kernel P T) →
  CasimirZeta.transformedDefectValue P ≡ problemOneOver120Value Z
transformedLiteralDefectEqualsOneOver120 {P = P} Z =
  trans
    (CasimirZeta.finitePartEqualsZetaMinusThree P)
    (problemZetaMinusThreeEqualsOneOver120 Z)

------------------------------------------------------------------------
-- Compatibility projection to the old 720 metadata surface.  The actual proof
-- remains in transformedLiteralDefectEqualsOneOver120 above.
------------------------------------------------------------------------

asLegacyZeta120Receipt :
  ∀ {kernel P T} →
  ProofBearingCasimirZeta120 kernel P T →
  C720.ZetaMinusThree120Receipt
asLegacyZeta120Receipt {P = P} {T = T} Z = record
  { C720.Scalar = CasimirZeta.ZetaValue P
  ; C720.longitudinalInput = Difference.Integrand (CasimirZeta.defect P)
  ; C720.zetaMinusThreeValue = CasimirZeta.transformedDefectValue P
  ; C720.analyticContinuationOrEquivalentFinitePart =
      Analytic.analyticContinuationAtMinusThree (localZetaReceipt Z)
  ; C720.zetaMinusThreeEqualsOneOver120 =
      CasimirZeta.transformedDefectValue P ≡ problemOneOver120Value Z
  ; C720.sameCasimirLongitudinalDefect =
      LongitudinalDefectTransformationTrace kernel P
  ; C720.reading =
      "Legacy 1/120 metadata projected from a proof-bearing literal-defect transformation trace."
  }

------------------------------------------------------------------------
-- Reverse proof search.
------------------------------------------------------------------------

record ReverseZetaTransformationTraceObligations : Set where
  field
    literalDefectParameterAndIntegrand : Set
    scalarCarrierMap : Set
    discreteTermPreservation : Set
    continuumReferencePreservation : Set
    subtractionConventionPreservation : Set
    separationParameterPreservation : Set
    finitePartPresentationPreservation : Set
    reading : String

open ReverseZetaTransformationTraceObligations public

data EqualNumericZetaValueAutomaticallySuppliesTransformationTrace : Set where

numericEqualityDoesNotIdentifyPhysicalDefect :
  EqualNumericZetaValueAutomaticallySuppliesTransformationTrace → ⊥
numericEqualityDoesNotIdentifyPhysicalDefect ()

record Status : Set where
  field
    proofBearingTransformationTraceOwned : Bool
    exactTransformedDefectOneOver120CompilerOwned : Bool
    legacy120AdapterOwned : Bool
    bareSameDefectSetLabelAccepted : Bool
    concretePhysicalTransformationTraceClosed : Bool

    proofBearingTransformationTraceOwnedIsTrue : proofBearingTransformationTraceOwned ≡ true
    exactTransformedDefectOneOver120CompilerOwnedIsTrue :
      exactTransformedDefectOneOver120CompilerOwned ≡ true
    legacy120AdapterOwnedIsTrue : legacy120AdapterOwned ≡ true
    bareSameDefectSetLabelAcceptedIsFalse : bareSameDefectSetLabelAccepted ≡ false
    concretePhysicalTransformationTraceClosedIsFalse :
      concretePhysicalTransformationTraceClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { proofBearingTransformationTraceOwned = true
  ; exactTransformedDefectOneOver120CompilerOwned = true
  ; legacy120AdapterOwned = true
  ; bareSameDefectSetLabelAccepted = false
  ; concretePhysicalTransformationTraceClosed = false
  ; proofBearingTransformationTraceOwnedIsTrue = refl
  ; exactTransformedDefectOneOver120CompilerOwnedIsTrue = refl
  ; legacy120AdapterOwnedIsTrue = refl
  ; bareSameDefectSetLabelAcceptedIsFalse = refl
  ; concretePhysicalTransformationTraceClosedIsFalse = refl
  }
