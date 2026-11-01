module DASHI.Physics.Closure.NSCollapseEigenframeRatioDerivativeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Explicit boundary derivative receipt for collapseImpossible.
--
-- This module records the derivative of <omega,e2> / g12 along the
-- boundary.  It keeps the vorticity equation, the Rellich-Kato
-- eigenvector rotation formula, the gap derivative g12_t from GD1, the
-- numerator and denominator derivatives, the singular F123 term, the
-- intended cancellation target under |<omega,e2>|^2 <= C*g12^2, and the
-- remaining blockers for closing the estimate.
--
-- The record is a receipt only.  Theorem and Clay promotion stay false.

data NSCollapseEigenframeRatioDerivativeStatus : Set where
  explicitBoundaryDerivativeRecorded :
    NSCollapseEigenframeRatioDerivativeStatus

data NSCollapseEigenframeRatioDerivativeStage : Set where
  boundaryRatioIdentified :
    NSCollapseEigenframeRatioDerivativeStage

  vorticityEquationRecorded :
    NSCollapseEigenframeRatioDerivativeStage

  rellichKatoRotationFormulaRecorded :
    NSCollapseEigenframeRatioDerivativeStage

  gapDerivativeFromGD1Recorded :
    NSCollapseEigenframeRatioDerivativeStage

  numeratorDerivativeRecorded :
    NSCollapseEigenframeRatioDerivativeStage

  denominatorDerivativeRecorded :
    NSCollapseEigenframeRatioDerivativeStage

  singularF123TermIsolated :
    NSCollapseEigenframeRatioDerivativeStage

  cancellationTargetRecorded :
    NSCollapseEigenframeRatioDerivativeStage

  estimateBlockersRecorded :
    NSCollapseEigenframeRatioDerivativeStage

canonicalNSCollapseEigenframeRatioDerivativeStages :
  List NSCollapseEigenframeRatioDerivativeStage
canonicalNSCollapseEigenframeRatioDerivativeStages =
  boundaryRatioIdentified
  ∷ vorticityEquationRecorded
  ∷ rellichKatoRotationFormulaRecorded
  ∷ gapDerivativeFromGD1Recorded
  ∷ numeratorDerivativeRecorded
  ∷ denominatorDerivativeRecorded
  ∷ singularF123TermIsolated
  ∷ cancellationTargetRecorded
  ∷ estimateBlockersRecorded
  ∷ []

data NSCollapseEigenframeRatioDerivativeBlocker : Set where
  noClosedBoundaryFrameControl :
    NSCollapseEigenframeRatioDerivativeBlocker

  noSharpSignControlForSingularF123 :
    NSCollapseEigenframeRatioDerivativeBlocker

  noClosedRellichKatoEigenframeBound :
    NSCollapseEigenframeRatioDerivativeBlocker

  noDerivedAbsorptionConstant :
    NSCollapseEigenframeRatioDerivativeBlocker

  noEstimateClosureForCollapseImpossible :
    NSCollapseEigenframeRatioDerivativeBlocker

canonicalNSCollapseEigenframeRatioDerivativeBlockers :
  List NSCollapseEigenframeRatioDerivativeBlocker
canonicalNSCollapseEigenframeRatioDerivativeBlockers =
  noClosedBoundaryFrameControl
  ∷ noSharpSignControlForSingularF123
  ∷ noClosedRellichKatoEigenframeBound
  ∷ noDerivedAbsorptionConstant
  ∷ noEstimateClosureForCollapseImpossible
  ∷ []

vorticityEquationCanonicalText : String
vorticityEquationCanonicalText =
  "vorticity equation: d_t omega + (u . grad) omega = (omega . grad) u + nu Laplace omega"

rellichKatoRotationFormulaCanonicalText : String
rellichKatoRotationFormulaCanonicalText =
  "Rellich-Kato eigenvector rotation: d_t e2 = sum_{k != 2} <e_k, A_t e2> / (lambda_2 - lambda_k) * e_k"

gapDerivativeGD1CanonicalText : String
gapDerivativeGD1CanonicalText =
  "GD1 gap derivative: g12_t = lambda2_t - lambda1_t, recorded as the boundary gap evolution input"

numeratorDerivativeCanonicalText : String
numeratorDerivativeCanonicalText =
  "numerator derivative: d_t <omega,e2> = <d_t omega,e2> + <omega,d_t e2>"

denominatorDerivativeCanonicalText : String
denominatorDerivativeCanonicalText =
  "denominator derivative: d_t(g12^-1) = - g12_t / g12^2"

singularF123TermCanonicalText : String
singularF123TermCanonicalText =
  "singular F123 term: the boundary rotation contribution with 1/g12 structure that remains singular unless further cancellation is supplied"

cancellationTargetCanonicalText : String
cancellationTargetCanonicalText =
  "cancellation target: if |<omega,e2>|^2 <= C*g12^2 then the quotient derivative should be absorbable against the singular boundary term"

blockingEstimatesCanonicalText : String
blockingEstimatesCanonicalText =
  "blockers: no closed boundary frame control, no sharp sign control for F123, no closed Rellich-Kato eigenframe bound, no derived absorption constant, and no estimate closure for collapseImpossible"

derivativeReceiptBoundaryCanonicalText : String
derivativeReceiptBoundaryCanonicalText =
  "Boundary differentiation records <omega,e2>/g12, the vorticity equation, the Rellich-Kato eigenvector rotation formula, the GD1 gap derivative, the numerator and denominator derivatives, the singular F123 term, the target cancellation |<omega,e2>|^2 <= C*g12^2, and the remaining blockers; theorem and Clay promotion stay false."

data NSCollapseEigenframeRatioDerivativePromotion : Set where

nsCollapseEigenframeRatioDerivativePromotionImpossibleHere :
  NSCollapseEigenframeRatioDerivativePromotion →
  NSCollapseEigenframeRatioDerivativePromotion
nsCollapseEigenframeRatioDerivativePromotionImpossibleHere ()

record NSCollapseEigenframeRatioDerivativeReceipt : Setω where
  field
    status :
      NSCollapseEigenframeRatioDerivativeStatus

    statusIsRecorded :
      status ≡ explicitBoundaryDerivativeRecorded

    stageLedger :
      List NSCollapseEigenframeRatioDerivativeStage

    stageLedgerIsCanonical :
      stageLedger ≡ canonicalNSCollapseEigenframeRatioDerivativeStages

    vorticityEquationText :
      String

    vorticityEquationTextIsCanonical :
      vorticityEquationText ≡ vorticityEquationCanonicalText

    rellichKatoRotationFormulaText :
      String

    rellichKatoRotationFormulaTextIsCanonical :
      rellichKatoRotationFormulaText
      ≡ rellichKatoRotationFormulaCanonicalText

    gapDerivativeGD1Text :
      String

    gapDerivativeGD1TextIsCanonical :
      gapDerivativeGD1Text ≡ gapDerivativeGD1CanonicalText

    numeratorDerivativeText :
      String

    numeratorDerivativeTextIsCanonical :
      numeratorDerivativeText ≡ numeratorDerivativeCanonicalText

    denominatorDerivativeText :
      String

    denominatorDerivativeTextIsCanonical :
      denominatorDerivativeText ≡ denominatorDerivativeCanonicalText

    singularF123TermText :
      String

    singularF123TermTextIsCanonical :
      singularF123TermText ≡ singularF123TermCanonicalText

    cancellationTargetText :
      String

    cancellationTargetTextIsCanonical :
      cancellationTargetText ≡ cancellationTargetCanonicalText

    estimateBlockers :
      List NSCollapseEigenframeRatioDerivativeBlocker

    estimateBlockersIsCanonical :
      estimateBlockers ≡ canonicalNSCollapseEigenframeRatioDerivativeBlockers

    blockerSummaryText :
      String

    blockerSummaryTextIsCanonical :
      blockerSummaryText ≡ blockingEstimatesCanonicalText

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    receiptBoundaryText :
      String

    receiptBoundaryTextIsCanonical :
      receiptBoundaryText ≡ derivativeReceiptBoundaryCanonicalText

open NSCollapseEigenframeRatioDerivativeReceipt public

canonicalNSCollapseEigenframeRatioDerivativeReceipt :
  NSCollapseEigenframeRatioDerivativeReceipt
canonicalNSCollapseEigenframeRatioDerivativeReceipt =
  record
    { status =
        explicitBoundaryDerivativeRecorded
    ; statusIsRecorded =
        refl
    ; stageLedger =
        canonicalNSCollapseEigenframeRatioDerivativeStages
    ; stageLedgerIsCanonical =
        refl
    ; vorticityEquationText =
        vorticityEquationCanonicalText
    ; vorticityEquationTextIsCanonical =
        refl
    ; rellichKatoRotationFormulaText =
        rellichKatoRotationFormulaCanonicalText
    ; rellichKatoRotationFormulaTextIsCanonical =
        refl
    ; gapDerivativeGD1Text =
        gapDerivativeGD1CanonicalText
    ; gapDerivativeGD1TextIsCanonical =
        refl
    ; numeratorDerivativeText =
        numeratorDerivativeCanonicalText
    ; numeratorDerivativeTextIsCanonical =
        refl
    ; denominatorDerivativeText =
        denominatorDerivativeCanonicalText
    ; denominatorDerivativeTextIsCanonical =
        refl
    ; singularF123TermText =
        singularF123TermCanonicalText
    ; singularF123TermTextIsCanonical =
        refl
    ; cancellationTargetText =
        cancellationTargetCanonicalText
    ; cancellationTargetTextIsCanonical =
        refl
    ; estimateBlockers =
        canonicalNSCollapseEigenframeRatioDerivativeBlockers
    ; estimateBlockersIsCanonical =
        refl
    ; blockerSummaryText =
        blockingEstimatesCanonicalText
    ; blockerSummaryTextIsCanonical =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; receiptBoundaryText =
        derivativeReceiptBoundaryCanonicalText
    ; receiptBoundaryTextIsCanonical =
        refl
    }

canonicalNSCollapseEigenframeRatioDerivativeReceiptStatus :
  status canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ explicitBoundaryDerivativeRecorded
canonicalNSCollapseEigenframeRatioDerivativeReceiptStatus =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptStageLedger :
  stageLedger canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ canonicalNSCollapseEigenframeRatioDerivativeStages
canonicalNSCollapseEigenframeRatioDerivativeReceiptStageLedger =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptVorticityEquationText :
  vorticityEquationText canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ vorticityEquationCanonicalText
canonicalNSCollapseEigenframeRatioDerivativeReceiptVorticityEquationText =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptRellichKatoRotationFormulaText :
  rellichKatoRotationFormulaText canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ rellichKatoRotationFormulaCanonicalText
canonicalNSCollapseEigenframeRatioDerivativeReceiptRellichKatoRotationFormulaText =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptGapDerivativeGD1Text :
  gapDerivativeGD1Text canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ gapDerivativeGD1CanonicalText
canonicalNSCollapseEigenframeRatioDerivativeReceiptGapDerivativeGD1Text =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptNumeratorDerivativeText :
  numeratorDerivativeText canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ numeratorDerivativeCanonicalText
canonicalNSCollapseEigenframeRatioDerivativeReceiptNumeratorDerivativeText =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptDenominatorDerivativeText :
  denominatorDerivativeText canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ denominatorDerivativeCanonicalText
canonicalNSCollapseEigenframeRatioDerivativeReceiptDenominatorDerivativeText =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptSingularF123TermText :
  singularF123TermText canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ singularF123TermCanonicalText
canonicalNSCollapseEigenframeRatioDerivativeReceiptSingularF123TermText =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptCancellationTargetText :
  cancellationTargetText canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ cancellationTargetCanonicalText
canonicalNSCollapseEigenframeRatioDerivativeReceiptCancellationTargetText =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptEstimateBlockers :
  estimateBlockers canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ canonicalNSCollapseEigenframeRatioDerivativeBlockers
canonicalNSCollapseEigenframeRatioDerivativeReceiptEstimateBlockers =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptBlockerSummaryText :
  blockerSummaryText canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ blockingEstimatesCanonicalText
canonicalNSCollapseEigenframeRatioDerivativeReceiptBlockerSummaryText =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptTheoremPromotedIsFalse :
  theoremPromoted canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ false
canonicalNSCollapseEigenframeRatioDerivativeReceiptTheoremPromotedIsFalse =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptClayPromotedIsFalse :
  clayPromoted canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ false
canonicalNSCollapseEigenframeRatioDerivativeReceiptClayPromotedIsFalse =
  refl

canonicalNSCollapseEigenframeRatioDerivativeReceiptBoundaryText :
  receiptBoundaryText canonicalNSCollapseEigenframeRatioDerivativeReceipt
  ≡ derivativeReceiptBoundaryCanonicalText
canonicalNSCollapseEigenframeRatioDerivativeReceiptBoundaryText =
  refl

