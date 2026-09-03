module DASHI.Analysis.RiemannG2SelectedPoleNearFiniteEvaluationSameObjectExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotleExplicitCutoffCarrierLeanReturnExact as Cutoff
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact as Selected

------------------------------------------------------------------------
-- SELECTED TARGET WINDOW -> FINITE SIGNED EVALUATION, SAME OBJECT
--
-- The checked cutoff return already owns the finite near carrier, explicit far
-- shell, far decay and literal D_off cutoff transport.  The genuinely unpaid
-- analytic coordinate is the signed target-centred finite-near evaluation.
--
-- Eval.FiniteNearProducer is intentionally scalar-generic.  Therefore merely
-- possessing one does not show it evaluates the finitePoleNearSigned coordinate
-- of THIS selected PoleNearTargetWindow.  This owner makes that identity exact.
------------------------------------------------------------------------

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

record SelectedFiniteNearEvaluationAttachment
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    (finite : Eval.FiniteNearProducer) : Set₁ where
  private
    evaluation = Eval.FiniteNearProducer.evaluation finite

  field
    -- The evaluator's scalar language is literally the canonical scalar
    -- language of the selected Weil/explicit-formula object.
    scalarCarrierIdentity :
      Eval.SignedFiniteNearEvaluationSurface.Scalar evaluation
      ≡ Weil.WeilTestSpace.Scalar space

    -- After transporting along that carrier identity, the value evaluated by
    -- the finite producer is exactly the finite-near coordinate of the SAME
    -- selected PoleNearTargetWindow.
    signedNearValueIsSelectedWindowFiniteNear :
      subst (λ X → X) scalarCarrierIdentity
        (Eval.SignedFiniteNearEvaluationSurface.signedNearValue evaluation)
      ≡
      Window.PoleNearTargetWindow.finitePoleNearSigned
        (Selected.ActualSelectedPoleNearProducer.targetWindow selected)

    sameFiniteNearCarrierReference : String

open SelectedFiniteNearEvaluationAttachment public

------------------------------------------------------------------------
-- BUDGET TRANSPORT: GENERIC EVALUATOR BUDGET -> SELECTED WEIL SCALAR
--
-- EvaluationProducesBudget is deliberately consumer-generic: its Budget carrier
-- need not be the same type as the selected Weil scalar.  The only additional
-- representation payment needed after a same-object finite evaluation is a
-- consumer transport from that abstract Budget into the selected scalar plus a
-- proof that the evaluator's existing ProducesRequiredUpper receipt becomes the
-- selected finite-near upper relation.  Once this transport exists, extracting
-- the selected near budget is compiler output rather than fresh analysis.
------------------------------------------------------------------------

record SelectedFiniteNearBudgetTransport
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    (finite : Eval.FiniteNearProducer)
    (attachment :
      SelectedFiniteNearEvaluationAttachment space formula orbit selected finite)
    : Set₁ where
  private
    evaluation = Eval.FiniteNearProducer.evaluation finite
    budgetReceipt = Eval.FiniteNearProducer.budget finite

  field
    budgetToSelectedScalar :
      Eval.EvaluationProducesBudget.Budget budgetReceipt →
      Weil.WeilTestSpace.Scalar space

    SelectedUpper :
      Weil.WeilTestSpace.Scalar space →
      Weil.WeilTestSpace.Scalar space →
      Set

    evaluatorUpperBecomesSelectedUpper :
      Eval.EvaluationProducesBudget.ProducesRequiredUpper
        budgetReceipt
        evaluation
        (Eval.EvaluationProducesBudget.nearBudget budgetReceipt)
      →
      SelectedUpper
        (Window.PoleNearTargetWindow.finitePoleNearSigned
          (Selected.ActualSelectedPoleNearProducer.targetWindow selected))
        (budgetToSelectedScalar
          (Eval.EvaluationProducesBudget.nearBudget budgetReceipt))

    budgetTransportReference : String

open SelectedFiniteNearBudgetTransport public

selectedNearBudget :
  ∀ {space formula orbit selected finite attachment} →
  (transport :
    SelectedFiniteNearBudgetTransport
      space formula orbit selected finite attachment) →
  Weil.WeilTestSpace.Scalar space
selectedNearBudget {finite = finite} transport =
  budgetToSelectedScalar transport
    (Eval.EvaluationProducesBudget.nearBudget
      (Eval.FiniteNearProducer.budget finite))

selectedFiniteNearUpper :
  ∀ {space formula orbit selected finite attachment} →
  (transport :
    SelectedFiniteNearBudgetTransport
      space formula orbit selected finite attachment) →
  SelectedUpper transport
    (Window.PoleNearTargetWindow.finitePoleNearSigned
      (Selected.ActualSelectedPoleNearProducer.targetWindow selected))
    (selectedNearBudget transport)
selectedFiniteNearUpper {finite = finite} transport =
  evaluatorUpperBecomesSelectedUpper transport
    (Eval.EvaluationProducesBudget.producesRequiredUpper
      (Eval.FiniteNearProducer.budget finite))

------------------------------------------------------------------------
-- Checked-cutoff consequences: do not reopen carrier/far-shell mathematics.
------------------------------------------------------------------------

checkedFiniteNearCarrierAlreadyOwned :
  Cutoff.finiteSignedNearCarrierOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ true
checkedFiniteNearCarrierAlreadyOwned =
  Cutoff.finiteSignedNearCarrierOwnedIsTrue
    Cutoff.canonicalExplicitCutoffCarrierLeanReturn

checkedFarShellAlreadyOwned :
  Cutoff.explicitFarShellFormulaOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ true
checkedFarShellAlreadyOwned =
  Cutoff.explicitFarShellFormulaOwnedIsTrue
    Cutoff.canonicalExplicitCutoffCarrierLeanReturn

checkedArbitraryAccuracyCutoffAlreadyOwned :
  Cutoff.arbitraryAccuracyCutoffOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ true
checkedArbitraryAccuracyCutoffAlreadyOwned =
  Cutoff.arbitraryAccuracyCutoffOwnedIsTrue
    Cutoff.canonicalExplicitCutoffCarrierLeanReturn

checkedDoffTransportAlreadyOwned :
  Cutoff.literalDoffCutoffTransportOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ true
checkedDoffTransportAlreadyOwned =
  Cutoff.literalDoffCutoffTransportOwnedIsTrue
    Cutoff.canonicalExplicitCutoffCarrierLeanReturn

------------------------------------------------------------------------
-- Search compression.
------------------------------------------------------------------------

data SelectedFiniteNearPayment : Set where
  rebuildFiniteNearCarrier
  reproveFarShellDecay
  reproveArbitraryAccuracyCutoff
  reproveDoffCutoffTransport
  recoverSignedFiniteNearProducer
  weldEvaluationToSelectedWindowFiniteNear
  recoverBudgetTransportToSelectedScalar
  extractNearBudget
  : SelectedFiniteNearPayment

data PaymentStatus : Set where
  pruned live downstream : PaymentStatus

paymentStatus : SelectedFiniteNearPayment → PaymentStatus
paymentStatus rebuildFiniteNearCarrier = pruned
paymentStatus reproveFarShellDecay = pruned
paymentStatus reproveArbitraryAccuracyCutoff = pruned
paymentStatus reproveDoffCutoffTransport = pruned
paymentStatus recoverSignedFiniteNearProducer = live
paymentStatus weldEvaluationToSelectedWindowFiniteNear = live
paymentStatus recoverBudgetTransportToSelectedScalar = live
paymentStatus extractNearBudget = downstream

finiteCarrierRebuildPruned : paymentStatus rebuildFiniteNearCarrier ≡ pruned
finiteCarrierRebuildPruned = refl

farShellReproofPruned : paymentStatus reproveFarShellDecay ≡ pruned
farShellReproofPruned = refl

cutoffReproofPruned : paymentStatus reproveArbitraryAccuracyCutoff ≡ pruned
cutoffReproofPruned = refl

nearBudgetExtractionIsCompilerOutput :
  paymentStatus extractNearBudget ≡ downstream
nearBudgetExtractionIsCompilerOutput = refl

record SelectedFiniteNearSameObjectBoundary : Set where
  constructor selected-finite-near-same-object-boundary
  field
    finiteNearCarrierFreshMathematicsRequired : Bool
    finiteNearCarrierFreshMathematicsRequiredIsFalse :
      finiteNearCarrierFreshMathematicsRequired ≡ false

    farShellFreshMathematicsRequired : Bool
    farShellFreshMathematicsRequiredIsFalse :
      farShellFreshMathematicsRequired ≡ false

    finiteSignedEvaluationFreshMathematicsRequired : Bool
    finiteSignedEvaluationFreshMathematicsRequiredIsTrue :
      finiteSignedEvaluationFreshMathematicsRequired ≡ true

    arbitraryFiniteNearEvaluationIsConsumerSufficient : Bool
    arbitraryFiniteNearEvaluationIsConsumerSufficientIsFalse :
      arbitraryFiniteNearEvaluationIsConsumerSufficient ≡ false

    evaluatorMustUseSelectedWindowFiniteNear : Bool
    evaluatorMustUseSelectedWindowFiniteNearIsTrue :
      evaluatorMustUseSelectedWindowFiniteNear ≡ true

    genericEvaluatorBudgetAlreadyLivesInSelectedScalar : Bool
    genericEvaluatorBudgetAlreadyLivesInSelectedScalarIsFalse :
      genericEvaluatorBudgetAlreadyLivesInSelectedScalar ≡ false

    selectedBudgetExtractionNeedsFreshAnalyticEstimateAfterTransport : Bool
    selectedBudgetExtractionNeedsFreshAnalyticEstimateAfterTransportIsFalse :
      selectedBudgetExtractionNeedsFreshAnalyticEstimateAfterTransport ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalSelectedFiniteNearSameObjectBoundary :
  SelectedFiniteNearSameObjectBoundary
canonicalSelectedFiniteNearSameObjectBoundary =
  selected-finite-near-same-object-boundary
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    "The checked 8883 cutoff return already owns the finite near carrier, explicit far-shell modulus/decay, arbitrary-accuracy cutoff and literal D_off cutoff transport. Do not reprove them. The live zero-side analytic payment is an actual phase-preserving FiniteNearProducer whose evaluation scalar carrier is identified with the selected Weil scalar and whose signedNearValue transports to exactly finitePoleNearSigned of the SAME selected PoleNearTargetWindow. EvaluationProducesBudget is already owned by that producer; after supplying the consumer-relative Budget -> selected-Scalar transport and proving its ProducesRequiredUpper receipt becomes the selected upper relation, the selected near budget and upper receipt are compiler output. RH remains open."
