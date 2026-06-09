module DASHI.Physics.Closure.Deg23HilbertModularCandidateReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23ShimuraApproachReceipt as Shimura
import DASHI.Physics.Closure.HilbertModularVolumeReceipt as Hilbert

------------------------------------------------------------------------
-- Hilbert modular candidate tests for the deg23 residual.
--
-- This receipt is a systematic negative/candidate diagnostic.  It consumes
-- the existing Shimura-approach receipt and records natural Hilbert modular
-- volume / zeta_Q(sqrt(21))(-1) normalisations against the required
-- diagnostic deg23 ~= 14.302.  No tested normalisation derives the required
-- value, and no physical CKM promotion is constructed.

data Deg23HilbertModularCandidateStatus : Set where
  hilbertModularDeg23CandidatesTestedNegative :
    Deg23HilbertModularCandidateStatus

data Deg23HilbertModularCandidateTest : Set where
  zetaQsqrt21RawTest :
    Deg23HilbertModularCandidateTest

  zetaQsqrt21NaturalScaleTest :
    Deg23HilbertModularCandidateTest

  zetaQsqrt21FirstOrderAlphaScaleTest :
    Deg23HilbertModularCandidateTest

  zetaQsqrt21GeometricAlphaScaleTest :
    Deg23HilbertModularCandidateTest

canonicalDeg23HilbertModularCandidateTests :
  List Deg23HilbertModularCandidateTest
canonicalDeg23HilbertModularCandidateTests =
  zetaQsqrt21RawTest
  ∷ zetaQsqrt21NaturalScaleTest
  ∷ zetaQsqrt21FirstOrderAlphaScaleTest
  ∷ zetaQsqrt21GeometricAlphaScaleTest
  ∷ []

data Deg23HilbertModularCandidateBlocker : Set where
  hilbertModularVolumeReceiptInputIsDiagnosticOnly :
    Deg23HilbertModularCandidateBlocker

  zetaNormalisationDoesNotDeriveRequiredDeg23 :
    Deg23HilbertModularCandidateBlocker

  missingCMPeriodShimuraVolumeTheorem :
    Deg23HilbertModularCandidateBlocker

  missingAuthorityBindingForDeg23Normalisation :
    Deg23HilbertModularCandidateBlocker

canonicalDeg23HilbertModularCandidateBlockers :
  List Deg23HilbertModularCandidateBlocker
canonicalDeg23HilbertModularCandidateBlockers =
  hilbertModularVolumeReceiptInputIsDiagnosticOnly
  ∷ zetaNormalisationDoesNotDeriveRequiredDeg23
  ∷ missingCMPeriodShimuraVolumeTheorem
  ∷ missingAuthorityBindingForDeg23Normalisation
  ∷ []

data Deg23HilbertModularCandidatePromotion : Set where

deg23HilbertModularCandidatePromotionImpossibleHere :
  Deg23HilbertModularCandidatePromotion →
  ⊥
deg23HilbertModularCandidatePromotionImpossibleHere ()

zetaQsqrt21FormulaLabel : String
zetaQsqrt21FormulaLabel =
  "zeta_Q(sqrt21)(-1) = 1/3"

naturalScaleFormulaLabel : String
naturalScaleFormulaLabel =
  "42 * zeta_Q(sqrt21)(-1) = 14"

firstOrderScaleFormulaLabel : String
firstOrderScaleFormulaLabel =
  "42 * zeta_Q(sqrt21)(-1) * (1 + alpha1/2) ~= 14.28868"

geometricScaleFormulaLabel : String
geometricScaleFormulaLabel =
  "42 * zeta_Q(sqrt21)(-1) / (1 - alpha1/2) ~= 14.294758"

requiredDeg23Label : String
requiredDeg23Label =
  "required diagnostic deg23 ~= 14.302"

candidateConclusionLabel : String
candidateConclusionLabel =
  "natural Hilbert/zeta normalisations tested here do not derive deg23 ~= 14.302"

record Deg23HilbertModularCandidateReceipt : Set where
  field
    status :
      Deg23HilbertModularCandidateStatus

    shimuraApproachReceipt :
      Shimura.Deg23ShimuraApproachReceipt

    shimuraApproachReceiptIsCanonical :
      shimuraApproachReceipt ≡ Shimura.canonicalDeg23ShimuraApproachReceipt

    hilbertModularVolumeReceipt :
      Hilbert.HilbertModularVolumeReceipt

    hilbertModularVolumeReceiptIsCanonical :
      hilbertModularVolumeReceipt ≡ Hilbert.canonicalHilbertModularVolumeReceipt

    realQuadraticField :
      String

    realQuadraticFieldIsQsqrt21 :
      realQuadraticField ≡ "Q(sqrt(21))"

    hilbertModularVolumeReceiptPresent :
      Bool

    hilbertModularVolumeReceiptPresentIsTrue :
      hilbertModularVolumeReceiptPresent ≡ true

    zetaFormula :
      String

    zetaFormulaIsCanonical :
      zetaFormula ≡ zetaQsqrt21FormulaLabel

    zetaNumerator :
      Nat

    zetaNumeratorIsOne :
      zetaNumerator ≡ 1

    zetaDenominator :
      Nat

    zetaDenominatorIsThree :
      zetaDenominator ≡ 3

    testedNormalisations :
      List Deg23HilbertModularCandidateTest

    testedNormalisationsAreCanonical :
      testedNormalisations ≡ canonicalDeg23HilbertModularCandidateTests

    requiredDeg23 :
      Float

    requiredDeg23LabelField :
      String

    requiredDeg23LabelFieldIsCanonical :
      requiredDeg23LabelField ≡ requiredDeg23Label

    rawZetaValue :
      Float

    rawZetaMatchesRequired :
      Bool

    rawZetaMatchesRequiredIsFalse :
      rawZetaMatchesRequired ≡ false

    naturalScaleFormula :
      String

    naturalScaleFormulaIsCanonical :
      naturalScaleFormula ≡ naturalScaleFormulaLabel

    naturalScaleDeg23 :
      Float

    naturalScaleMatchesRequired :
      Bool

    naturalScaleMatchesRequiredIsFalse :
      naturalScaleMatchesRequired ≡ false

    firstOrderScaleFormula :
      String

    firstOrderScaleFormulaIsCanonical :
      firstOrderScaleFormula ≡ firstOrderScaleFormulaLabel

    firstOrderScaleDeg23 :
      Float

    firstOrderScaleMatchesRequired :
      Bool

    firstOrderScaleMatchesRequiredIsFalse :
      firstOrderScaleMatchesRequired ≡ false

    geometricScaleFormula :
      String

    geometricScaleFormulaIsCanonical :
      geometricScaleFormula ≡ geometricScaleFormulaLabel

    geometricScaleDeg23 :
      Float

    geometricScaleResidualToRequired :
      Float

    geometricScaleMatchesRequired :
      Bool

    geometricScaleMatchesRequiredIsFalse :
      geometricScaleMatchesRequired ≡ false

    anyHilbertNormalisationDerivesDeg23 :
      Bool

    anyHilbertNormalisationDerivesDeg23IsFalse :
      anyHilbertNormalisationDerivesDeg23 ≡ false

    candidateConclusion :
      String

    candidateConclusionIsCanonical :
      candidateConclusion ≡ candidateConclusionLabel

    systematicNegativeDiagnostic :
      Bool

    systematicNegativeDiagnosticIsTrue :
      systematicNegativeDiagnostic ≡ true

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    physicalVcbPromoted :
      Bool

    physicalVcbPromotedIsFalse :
      physicalVcbPromoted ≡ false

    blockers :
      List Deg23HilbertModularCandidateBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDeg23HilbertModularCandidateBlockers

    promotionFlags :
      List Deg23HilbertModularCandidatePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Deg23HilbertModularCandidateReceipt public

canonicalDeg23HilbertModularCandidateReceipt :
  Deg23HilbertModularCandidateReceipt
canonicalDeg23HilbertModularCandidateReceipt =
  record
    { status =
        hilbertModularDeg23CandidatesTestedNegative
    ; shimuraApproachReceipt =
        Shimura.canonicalDeg23ShimuraApproachReceipt
    ; shimuraApproachReceiptIsCanonical =
        refl
    ; hilbertModularVolumeReceipt =
        Hilbert.canonicalHilbertModularVolumeReceipt
    ; hilbertModularVolumeReceiptIsCanonical =
        refl
    ; realQuadraticField =
        "Q(sqrt(21))"
    ; realQuadraticFieldIsQsqrt21 =
        refl
    ; hilbertModularVolumeReceiptPresent =
        true
    ; hilbertModularVolumeReceiptPresentIsTrue =
        refl
    ; zetaFormula =
        zetaQsqrt21FormulaLabel
    ; zetaFormulaIsCanonical =
        refl
    ; zetaNumerator =
        1
    ; zetaNumeratorIsOne =
        refl
    ; zetaDenominator =
        3
    ; zetaDenominatorIsThree =
        refl
    ; testedNormalisations =
        canonicalDeg23HilbertModularCandidateTests
    ; testedNormalisationsAreCanonical =
        refl
    ; requiredDeg23 =
        14.302
    ; requiredDeg23LabelField =
        requiredDeg23Label
    ; requiredDeg23LabelFieldIsCanonical =
        refl
    ; rawZetaValue =
        0.3333333333333333
    ; rawZetaMatchesRequired =
        false
    ; rawZetaMatchesRequiredIsFalse =
        refl
    ; naturalScaleFormula =
        naturalScaleFormulaLabel
    ; naturalScaleFormulaIsCanonical =
        refl
    ; naturalScaleDeg23 =
        14.0
    ; naturalScaleMatchesRequired =
        false
    ; naturalScaleMatchesRequiredIsFalse =
        refl
    ; firstOrderScaleFormula =
        firstOrderScaleFormulaLabel
    ; firstOrderScaleFormulaIsCanonical =
        refl
    ; firstOrderScaleDeg23 =
        14.28868
    ; firstOrderScaleMatchesRequired =
        false
    ; firstOrderScaleMatchesRequiredIsFalse =
        refl
    ; geometricScaleFormula =
        geometricScaleFormulaLabel
    ; geometricScaleFormulaIsCanonical =
        refl
    ; geometricScaleDeg23 =
        14.294757908064284
    ; geometricScaleResidualToRequired =
        0.007242091935715482
    ; geometricScaleMatchesRequired =
        false
    ; geometricScaleMatchesRequiredIsFalse =
        refl
    ; anyHilbertNormalisationDerivesDeg23 =
        false
    ; anyHilbertNormalisationDerivesDeg23IsFalse =
        refl
    ; candidateConclusion =
        candidateConclusionLabel
    ; candidateConclusionIsCanonical =
        refl
    ; systematicNegativeDiagnostic =
        true
    ; systematicNegativeDiagnosticIsTrue =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; physicalVcbPromoted =
        false
    ; physicalVcbPromotedIsFalse =
        refl
    ; blockers =
        canonicalDeg23HilbertModularCandidateBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "This receipt consumes the Deg23ShimuraApproachReceipt candidate target"
        ∷ "HilbertModularVolumeReceipt supplies zeta_Q(sqrt21)(-1)=1/3 as a diagnostic input"
        ∷ "The zeta_Q(sqrt21)(-1)=1/3 normalisation and natural 42*zeta scale were tested"
        ∷ "First-order and geometric alpha rescalings were tested as candidate diagnostics"
        ∷ "None of the tested Hilbert/zeta normalisations derives the required deg23 approximately 14.302"
        ∷ "This is a systematic negative candidate diagnostic; physical Vcb and CKM promotion remain false"
        ∷ []
    }

deg23HilbertCandidateIsSystematicNegative :
  systematicNegativeDiagnostic canonicalDeg23HilbertModularCandidateReceipt
  ≡
  true
deg23HilbertCandidateIsSystematicNegative =
  refl

deg23HilbertCandidateDoesNotDeriveDeg23 :
  anyHilbertNormalisationDerivesDeg23
    canonicalDeg23HilbertModularCandidateReceipt
  ≡
  false
deg23HilbertCandidateDoesNotDeriveDeg23 =
  refl

deg23HilbertCandidateDoesNotPromoteCKM :
  physicalCKMPromoted canonicalDeg23HilbertModularCandidateReceipt
  ≡
  false
deg23HilbertCandidateDoesNotPromoteCKM =
  refl
