module DASHI.Physics.Closure.JarlskogDiagnosticAnalysis where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.VubVtdFromFullCKM as Tail

------------------------------------------------------------------------
-- Jarlskog error decomposition for the current CKM diagnostic.

data JarlskogDiagnosticStatus : Set where
  jarlskogOvershootDecomposed :
    JarlskogDiagnosticStatus

data JarlskogDominantSource : Set where
  y13VubMagnitudeDominates :
    JarlskogDominantSource

data JarlskogDiagnosticBlocker : Set where
  y13MagnitudeWrongForPhysicalCKM :
    JarlskogDiagnosticBlocker

  heckePhaseBranchNotAuthorityBound :
    JarlskogDiagnosticBlocker

  physicalEigenbasisNotMatched :
    JarlskogDiagnosticBlocker

canonicalJarlskogDiagnosticBlockers :
  List JarlskogDiagnosticBlocker
canonicalJarlskogDiagnosticBlockers =
  y13MagnitudeWrongForPhysicalCKM
  ∷ heckePhaseBranchNotAuthorityBound
  ∷ physicalEigenbasisNotMatched
  ∷ []

data JarlskogDiagnosticPromotion : Set where

jarlskogDiagnosticPromotionImpossibleHere :
  JarlskogDiagnosticPromotion →
  ⊥
jarlskogDiagnosticPromotionImpossibleHere ()

record JarlskogDiagnosticAnalysisReceipt : Set where
  field
    status :
      JarlskogDiagnosticStatus

    fullCKMReceipt :
      Tail.VubVtdFromFullCKMReceipt

    fullCKMReceiptIsCanonical :
      fullCKMReceipt ≡ Tail.canonicalVubVtdFromFullCKMReceipt

    jarlskogOvershootFactor :
      Float

    lambdaContributionLabel :
      String

    vcbContributionLabel :
      String

    phaseContributionLabel :
      String

    vubContributionLabel :
      String

    dominantSource :
      JarlskogDominantSource

    requiredOverallSuppression :
      Float

    diagnosticConclusion :
      String

    jarlskogDiagnosticAnalysisRecorded :
      Bool

    jarlskogDiagnosticAnalysisRecordedIsTrue :
      jarlskogDiagnosticAnalysisRecorded ≡ true

    y13MagnitudeIdentifiedAsDominant :
      Bool

    y13MagnitudeIdentifiedAsDominantIsTrue :
      y13MagnitudeIdentifiedAsDominant ≡ true

    physicalCPDerived :
      Bool

    physicalCPDerivedIsFalse :
      physicalCPDerived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List JarlskogDiagnosticBlocker

    blockersAreCanonical :
      blockers ≡ canonicalJarlskogDiagnosticBlockers

    promotionFlags :
      List JarlskogDiagnosticPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open JarlskogDiagnosticAnalysisReceipt public

canonicalJarlskogDiagnosticAnalysisReceipt :
  JarlskogDiagnosticAnalysisReceipt
canonicalJarlskogDiagnosticAnalysisReceipt =
  record
    { status =
        jarlskogOvershootDecomposed
    ; fullCKMReceipt =
        Tail.canonicalVubVtdFromFullCKMReceipt
    ; fullCKMReceiptIsCanonical =
        refl
    ; jarlskogOvershootFactor =
        11.258791342416867
    ; lambdaContributionLabel =
        "lambda is already a close diagnostic; it is not the source of the 11.26x Jarlskog overshoot"
    ; vcbContributionLabel =
        "the deg23/A lane is percent-level, not order-of-magnitude"
    ; phaseContributionLabel =
        "delta_29 has a phase mismatch, but sin(delta_29) is order one"
    ; vubContributionLabel =
        "the present eigenbasis gives |V_ub| ~= 0.756, so the y13/eigenbasis magnitude dominates"
    ; dominantSource =
        y13VubMagnitudeDominates
    ; requiredOverallSuppression =
        0.08881948066952408
    ; diagnosticConclusion =
        "The current Jarlskog mismatch is a magnitude/eigenbasis problem, not primarily a phase problem"
    ; jarlskogDiagnosticAnalysisRecorded =
        true
    ; jarlskogDiagnosticAnalysisRecordedIsTrue =
        refl
    ; y13MagnitudeIdentifiedAsDominant =
        true
    ; y13MagnitudeIdentifiedAsDominantIsTrue =
        refl
    ; physicalCPDerived =
        false
    ; physicalCPDerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalJarlskogDiagnosticBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The Jarlskog diagnostic is intentionally negative"
        ∷ "The dominant failure is the current y13/eigenbasis magnitude convention"
        ∷ "No CP or CKM promotion is asserted"
        ∷ []
    }

