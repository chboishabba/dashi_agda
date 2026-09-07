module DASHI.Analysis.RiemannG2CertifiedFiniteNearEvaluationCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact as Minimal
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Cast

------------------------------------------------------------------------
-- PROOF-CARRYING FINITE CERTIFICATE -> SELECTED FINITE-NEAR PAYMENT
--
-- The near object is already finite.  This compiler makes the computational
-- route explicit: enumerate/evaluate a finite list, provide an inhabited
-- enclosure/Within certificate for its exact fold, identify that fold with the
-- selected window's literal `finitePoleNearSigned`, then provide the separate
-- consumer-budget extraction receipt.
--
-- No global exponential-sum theorem is inferred from finiteness alone.
------------------------------------------------------------------------

record CertifiedSelectedFiniteNearEvaluation
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula) : Set₁ where
  field
    carrier : Cert.FiniteAdditiveCarrier
    certificate : Cert.ProofCarryingFiniteSumEnclosure carrier

    scalarCarrierIdentity :
      Cert.Scalar carrier ≡ Weil.WeilTestSpace.Scalar space

    certifiedFiniteSumIsSelectedFiniteNear :
      Cast.cast scalarCarrierIdentity
        (Cert.foldScalars carrier
          (Cert.mapValues
            (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
            (Cert.ProofCarryingFiniteSumEnclosure.terms certificate)))
      ≡ Window.PoleNearTargetWindow.finitePoleNearSigned window

    evaluationReference : String

open CertifiedSelectedFiniteNearEvaluation public

compileSignedFiniteNearEvaluation :
  ∀ {space formula window} →
  CertifiedSelectedFiniteNearEvaluation space formula window →
  Eval.SignedFiniteNearEvaluationSurface
compileSignedFiniteNearEvaluation input =
  Eval.signed-finite-near-evaluation-surface
    (Cert.Scalar (carrier input))
    (Cert.ProofCarryingFiniteSumEnclosure.Error (certificate input))
    (Cert.foldScalars (carrier input)
      (Cert.mapValues
        (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm (certificate input))
        (Cert.ProofCarryingFiniteSumEnclosure.terms (certificate input))))
    (Cert.ProofCarryingFiniteSumEnclosure.approximant (certificate input))
    (Cert.ProofCarryingFiniteSumEnclosure.error (certificate input))
    (Cert.ProofCarryingFiniteSumEnclosure.Within (certificate input))
    (Cert.ProofCarryingFiniteSumEnclosure.finiteSumWithinApproximant
      (certificate input))
    (evaluationReference input)

record CertifiedSelectedFiniteNearBudgetInput
    {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    {window : Window.PoleNearTargetWindow space formula}
    (certified : CertifiedSelectedFiniteNearEvaluation space formula window)
    : Set₁ where
  private
    evaluation0 = compileSignedFiniteNearEvaluation certified
  field
    Budget : Set
    nearBudget : Budget

    ProducesRequiredUpper :
      Eval.SignedFiniteNearEvaluationSurface → Budget → Set

    producesRequiredUpper :
      ProducesRequiredUpper evaluation0 nearBudget

    budgetToSelectedScalar :
      Budget → Weil.WeilTestSpace.Scalar space

    SelectedUpper :
      Weil.WeilTestSpace.Scalar space →
      Weil.WeilTestSpace.Scalar space →
      Set

    evaluatorUpperBecomesSelectedUpper :
      ProducesRequiredUpper evaluation0 nearBudget →
      SelectedUpper
        (Window.PoleNearTargetWindow.finitePoleNearSigned window)
        (budgetToSelectedScalar nearBudget)

    budgetReference : String

open CertifiedSelectedFiniteNearBudgetInput public

compileEvaluationProducesBudget :
  ∀ {space formula window}
    {certified : CertifiedSelectedFiniteNearEvaluation space formula window} →
  CertifiedSelectedFiniteNearBudgetInput certified →
  Eval.EvaluationProducesBudget
    (compileSignedFiniteNearEvaluation certified)
compileEvaluationProducesBudget input = record
  { Eval.Budget = Budget input
  ; Eval.nearBudget = nearBudget input
  ; Eval.ProducesRequiredUpper = ProducesRequiredUpper input
  ; Eval.producesRequiredUpper = producesRequiredUpper input
  ; Eval.budgetReference = budgetReference input
  }

compileSelectedFiniteNearBudgetPayment :
  ∀ {space formula window}
    (certified : CertifiedSelectedFiniteNearEvaluation space formula window) →
  CertifiedSelectedFiniteNearBudgetInput certified →
  Minimal.SelectedFiniteNearBudgetPayment space formula window
compileSelectedFiniteNearBudgetPayment certified input = record
  { Minimal.evaluation = compileSignedFiniteNearEvaluation certified
  ; Minimal.budget = compileEvaluationProducesBudget input
  ; Minimal.scalarCarrierIdentity = scalarCarrierIdentity certified
  ; Minimal.signedNearValueIsSelectedFiniteNear =
      certifiedFiniteSumIsSelectedFiniteNear certified
  ; Minimal.budgetToSelectedScalar = budgetToSelectedScalar input
  ; Minimal.SelectedUpper = SelectedUpper input
  ; Minimal.evaluatorUpperBecomesSelectedUpper =
      evaluatorUpperBecomesSelectedUpper input
  ; Minimal.paymentReference = budgetReference input
  }

record CertifiedFiniteNearCompilerBoundary : Set where
  constructor certified-finite-near-compiler-boundary
  field
    finiteEnumerationAloneClosesNearEstimate : Bool
    finiteEnumerationAloneClosesNearEstimateIsFalse :
      finiteEnumerationAloneClosesNearEstimate ≡ false

    aggregateContainmentIsProofBearing : Bool
    aggregateContainmentIsProofBearingIsTrue :
      aggregateContainmentIsProofBearing ≡ true

    exactFoldIdentityWithSelectedNearRequired : Bool
    exactFoldIdentityWithSelectedNearRequiredIsTrue :
      exactFoldIdentityWithSelectedNearRequired ≡ true

    separateConsumerBudgetReceiptStillRequired : Bool
    separateConsumerBudgetReceiptStillRequiredIsTrue :
      separateConsumerBudgetReceiptStillRequired ≡ true

    certifiedFiniteSumCompilesMinimalSelectedPayment : Bool
    certifiedFiniteSumCompilesMinimalSelectedPaymentIsTrue :
      certifiedFiniteSumCompilesMinimalSelectedPayment ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalCertifiedFiniteNearCompilerBoundary : CertifiedFiniteNearCompilerBoundary
canonicalCertifiedFiniteNearCompilerBoundary =
  certified-finite-near-compiler-boundary
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
