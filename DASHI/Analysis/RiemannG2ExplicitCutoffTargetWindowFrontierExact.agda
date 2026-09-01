module DASHI.Analysis.RiemannG2ExplicitCutoffTargetWindowFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleExplicitCutoffCarrierLeanReturnExact as Cutoff
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window

------------------------------------------------------------------------
-- CHECKED CUTOFF RETURN VS LITERAL EXPLICIT-FORMULA TARGET WINDOW
--
-- The 8883 checked-Lean return owns the finite near carrier, the explicit far
-- modulus, arbitrary-accuracy cutoff, and the literal D_off cutoff transport.
-- It does NOT transport a Lean proof term into Agda, and the Agda status owner
-- does not itself inhabit PoleNearTargetWindow.  Conversely, a
-- PoleNearTargetWindow already owns the exact spectralZeroForm
-- cluster+near+far equality needed downstream.
--
-- Hence the forward frontier is asymmetric:
--
--   cutoff/far machinery: mathematically owned in checked Lean;
--   literal Agda target-window spectral object: same-object attachment open;
--   finite signed near cancellation: analytic theorem open.
------------------------------------------------------------------------

data CutoffWindowPayment : Set where
  reproveFarShellDecay
  reproveFiniteNearCarrier
  transportLeanProofTermIntoAgda
  recoverLiteralPoleNearTargetWindow
  attachCheckedCutoffCoordinatesToSameWindow
  evaluateFiniteSignedNearCosine
  : CutoffWindowPayment

data PaymentStatus : Set where
  ownedExternally live pruned optional : PaymentStatus

paymentStatus : CutoffWindowPayment → PaymentStatus
paymentStatus reproveFarShellDecay = pruned
paymentStatus reproveFiniteNearCarrier = pruned
paymentStatus transportLeanProofTermIntoAgda = optional
paymentStatus recoverLiteralPoleNearTargetWindow = live
paymentStatus attachCheckedCutoffCoordinatesToSameWindow = live
paymentStatus evaluateFiniteSignedNearCosine = live

farShellReproofPruned : paymentStatus reproveFarShellDecay ≡ pruned
farShellReproofPruned = refl

finiteNearCarrierReproofPruned :
  paymentStatus reproveFiniteNearCarrier ≡ pruned
finiteNearCarrierReproofPruned = refl

checkedFarShellOwned :
  Cutoff.explicitFarShellFormulaOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ true
checkedFarShellOwned = refl

checkedFiniteNearCarrierOwned :
  Cutoff.finiteSignedNearCarrierOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ true
checkedFiniteNearCarrierOwned = refl

checkedDoffTransportOwned :
  Cutoff.literalDoffCutoffTransportOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ true
checkedDoffTransportOwned = refl

leanProofNotTransported :
  Cutoff.leanProofTransportedIntoAgda Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ false
leanProofNotTransported = refl

finiteNearCancellationStillOpen :
  Cutoff.finiteSignedNearCancellationClosed Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ false
finiteNearCancellationStillOpen = refl

record ExplicitCutoffTargetWindowFrontierBoundary : Set where
  constructor explicit-cutoff-target-window-frontier-boundary
  field
    checkedLeanCutoffMathematicsOwned : Bool
    checkedLeanCutoffMathematicsOwnedIsTrue :
      checkedLeanCutoffMathematicsOwned ≡ true

    checkedLeanReturnDirectlyInhabitsAgdaPoleNearTargetWindow : Bool
    checkedLeanReturnDirectlyInhabitsAgdaPoleNearTargetWindowIsFalse :
      checkedLeanReturnDirectlyInhabitsAgdaPoleNearTargetWindow ≡ false

    poleNearTargetWindowAlreadyCarriesRequiredSpectralEquality : Bool
    poleNearTargetWindowAlreadyCarriesRequiredSpectralEqualityIsTrue :
      poleNearTargetWindowAlreadyCarriesRequiredSpectralEquality ≡ true

    farShellNeedsFreshMathematics : Bool
    farShellNeedsFreshMathematicsIsFalse : farShellNeedsFreshMathematics ≡ false

    finiteNearCarrierNeedsFreshMathematics : Bool
    finiteNearCarrierNeedsFreshMathematicsIsFalse :
      finiteNearCarrierNeedsFreshMathematics ≡ false

    sameObjectTargetWindowAttachmentStillRequired : Bool
    sameObjectTargetWindowAttachmentStillRequiredIsTrue :
      sameObjectTargetWindowAttachmentStillRequired ≡ true

    finiteSignedNearEvaluationStillRequired : Bool
    finiteSignedNearEvaluationStillRequiredIsTrue :
      finiteSignedNearEvaluationStillRequired ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalExplicitCutoffTargetWindowFrontierBoundary :
  ExplicitCutoffTargetWindowFrontierBoundary
canonicalExplicitCutoffTargetWindowFrontierBoundary =
  explicit-cutoff-target-window-frontier-boundary
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    "The explicit-cutoff audit confirms the expected near/far machinery is already mathematically owned in the checked Lean return: finite nearOffFinset, every-cutoff far bound, decay and literal D_off cutoff transport. But the Agda return is provenance/theorem-shape only and does not itself inhabit PoleNearTargetWindow. Do not reprove the far shell or finite carrier. Recover the literal target-window object on the same selected test/cutoff, attach those checked coordinates, then spend analytic effort on the finite signed target-centred cosine evaluation. The historical H_W interface is downstream compiler output once that same-object target window is present. RH is not derived."
