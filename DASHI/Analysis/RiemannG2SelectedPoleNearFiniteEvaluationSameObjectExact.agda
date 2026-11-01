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
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact as Selected

------------------------------------------------------------------------
-- SELECTED TARGET WINDOW -> FINITE SIGNED EVALUATION, SAME OBJECT
--
-- The checked cutoff return already owns the finite near carrier, explicit far
-- shell, far decay and literal D_off cutoff transport. The genuinely unpaid
-- analytic coordinate is the signed target-centred finite-near evaluation.
--
-- Eval.FiniteNearProducer is intentionally scalar-generic. Therefore merely
-- possessing one does not show it evaluates the finitePoleNearSigned coordinate
-- of THIS selected PoleNearTargetWindow. This owner makes that identity exact.
--
-- BIDI UPDATE: DirectFinitePoleNearProducer already contains an actual signed
-- value, approximant, error, Within relation and receipt. It therefore compiles
-- directly to the canonical SignedFiniteNearEvaluationSurface below. No second
-- evaluation surface is required for the direct route. Same-selected-window
-- identity and budget transport remain separate downstream payments.
------------------------------------------------------------------------

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

------------------------------------------------------------------------
-- DIRECT PRODUCER -> CANONICAL EVALUATION SURFACE
------------------------------------------------------------------------

directToSignedFiniteNearEvaluationSurface :
  Direct.DirectFinitePoleNearProducer → Eval.SignedFiniteNearEvaluationSurface
directToSignedFiniteNearEvaluationSurface d =
  Eval.signed-finite-near-evaluation-surface
    (Direct.DirectFinitePoleNearProducer.Scalar d)
    (Direct.DirectFinitePoleNearProducer.Scalar d)
    (Direct.DirectFinitePoleNearProducer.finiteSignedNearValue d)
    (Direct.DirectFinitePoleNearProducer.approximant d)
    (Direct.DirectFinitePoleNearProducer.error d)
    (Direct.DirectFinitePoleNearProducer.Within d)
    (Direct.DirectFinitePoleNearProducer.evaluationReceipt d)
    "compiled from DirectFinitePoleNearProducer; same signed value/approximant/error receipt"

record SelectedDirectEvaluationAttachment
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    (direct : Direct.DirectFinitePoleNearProducer) : Set₁ where
  private
    evaluation = directToSignedFiniteNearEvaluationSurface direct

  field
    scalarCarrierIdentity :
      Eval.SignedFiniteNearEvaluationSurface.Scalar evaluation
      ≡ Weil.WeilTestSpace.Scalar space

    signedNearValueIsSelectedWindowFiniteNear :
      subst (λ X → X) scalarCarrierIdentity
        (Eval.SignedFiniteNearEvaluationSurface.signedNearValue evaluation)
      ≡
      Window.PoleNearTargetWindow.finitePoleNearSigned
        (Selected.ActualSelectedPoleNearProducer.targetWindow selected)

    sameTargetRelativeGapCarrier : Set
    sameNearIndexCarrier : Set
    sameMultiplicityCarrier : Set
    directAttachmentReference : String

open SelectedDirectEvaluationAttachment public

------------------------------------------------------------------------
-- Existing generic finite-producer same-object attachment.
------------------------------------------------------------------------

record SelectedFiniteNearEvaluationAttachment
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    (finite : Eval.FiniteNearProducer) : Set₁ where
  private
    evaluation = Eval.FiniteNearProducer.evaluation finite

  field
    scalarCarrierIdentity :
      Eval.SignedFiniteNearEvaluationSurface.Scalar evaluation
      ≡ Weil.WeilTestSpace.Scalar space

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
  rebuildFiniteNearCarrier : SelectedFiniteNearPayment
  reproveFarShellDecay : SelectedFiniteNearPayment
  reproveArbitraryAccuracyCutoff : SelectedFiniteNearPayment
  reproveDoffCutoffTransport : SelectedFiniteNearPayment
  constructSecondEvaluationSurfaceForDirectRoute : SelectedFiniteNearPayment
  recoverDirectFinitePoleNearProducer : SelectedFiniteNearPayment
  attachDirectEvaluationToSelectedWindow : SelectedFiniteNearPayment
  recoverGenericFiniteNearProducerBudget : SelectedFiniteNearPayment
  recoverBudgetTransportToSelectedScalar : SelectedFiniteNearPayment
  extractNearBudget : SelectedFiniteNearPayment

data PaymentStatus : Set where
  pruned : PaymentStatus
  live : PaymentStatus
  downstream : PaymentStatus

paymentStatus : SelectedFiniteNearPayment → PaymentStatus
paymentStatus rebuildFiniteNearCarrier = pruned
paymentStatus reproveFarShellDecay = pruned
paymentStatus reproveArbitraryAccuracyCutoff = pruned
paymentStatus reproveDoffCutoffTransport = pruned
paymentStatus constructSecondEvaluationSurfaceForDirectRoute = pruned
paymentStatus recoverDirectFinitePoleNearProducer = live
paymentStatus attachDirectEvaluationToSelectedWindow = downstream
paymentStatus recoverGenericFiniteNearProducerBudget = downstream
paymentStatus recoverBudgetTransportToSelectedScalar = downstream
paymentStatus extractNearBudget = downstream

finiteCarrierRebuildPruned : paymentStatus rebuildFiniteNearCarrier ≡ pruned
finiteCarrierRebuildPruned = refl

farShellReproofPruned : paymentStatus reproveFarShellDecay ≡ pruned
farShellReproofPruned = refl

cutoffReproofPruned : paymentStatus reproveArbitraryAccuracyCutoff ≡ pruned
cutoffReproofPruned = refl

secondDirectEvaluationSurfacePruned :
  paymentStatus constructSecondEvaluationSurfaceForDirectRoute ≡ pruned
secondDirectEvaluationSurfacePruned = refl

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

    directProducerCompilesToCanonicalEvaluationSurface : Bool
    directProducerCompilesToCanonicalEvaluationSurfaceIsTrue :
      directProducerCompilesToCanonicalEvaluationSurface ≡ true

    secondDirectEvaluationSurfaceRequired : Bool
    secondDirectEvaluationSurfaceRequiredIsFalse :
      secondDirectEvaluationSurfaceRequired ≡ false

    directFiniteProducerFreshMathematicsRequired : Bool
    directFiniteProducerFreshMathematicsRequiredIsTrue :
      directFiniteProducerFreshMathematicsRequired ≡ true

    evaluatorMustUseSelectedWindowFiniteNear : Bool
    evaluatorMustUseSelectedWindowFiniteNearIsTrue :
      evaluatorMustUseSelectedWindowFiniteNear ≡ true

    selectedDirectAttachmentClosedHere : Bool
    selectedDirectAttachmentClosedHereIsFalse :
      selectedDirectAttachmentClosedHere ≡ false

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
    true refl
    false refl
    false refl
    false refl
    false refl
    "The checked cutoff return owns the finite near carrier and far shell. An actual DirectFinitePoleNearProducer now compiles mechanically to the canonical SignedFiniteNearEvaluationSurface, so do not construct a second evaluation interface. The live analytic payment is recovering that direct producer itself. After it exists, identify its scalar/signedNearValue with finitePoleNearSigned of the SAME ActualSelectedPoleNearProducer; then transport or construct the consumer budget on that same object. The selected attachment and budget remain open; RH is not derived."
