module DASHI.Physics.Closure.FaltingsHeightDeg23Receipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Faltings-height route for the p3-p5 deg23 residual.
--
-- This receipt records the precise diagnostic route, not a promotion.  The
-- correction to the natural deg23=14 readback would have to come from the CM
-- Faltings-height difference between the j=0, D=-3 lane and the j=-3375,
-- D=-7 lane.  The analytic L'/L values are not formalised in this repo, so the
-- route remains a numerical/CitationAuthority frontier.

data FaltingsHeightDeg23Status : Set where
  faltingsHeightCorrectionRouteRecorded :
    FaltingsHeightDeg23Status

data FaltingsHeightDeg23Blocker : Set where
  missingFormalCMFaltingsHeightEvaluation :
    FaltingsHeightDeg23Blocker

  missingNumericalCertifiedLDerivativeRatio :
    FaltingsHeightDeg23Blocker

  missingProofCorrectionResolvesDeg23Residual :
    FaltingsHeightDeg23Blocker

canonicalFaltingsHeightDeg23Blockers :
  List FaltingsHeightDeg23Blocker
canonicalFaltingsHeightDeg23Blockers =
  missingFormalCMFaltingsHeightEvaluation
  ∷ missingNumericalCertifiedLDerivativeRatio
  ∷ missingProofCorrectionResolvesDeg23Residual
  ∷ []

data FaltingsHeightDeg23Promotion : Set where

faltingsHeightDeg23PromotionImpossibleHere :
  FaltingsHeightDeg23Promotion →
  ⊥
faltingsHeightDeg23PromotionImpossibleHere ()

record FaltingsHeightDeg23Receipt : Set where
  field
    status :
      FaltingsHeightDeg23Status

    lowerCMDiscriminantAbs :
      Nat

    lowerCMDiscriminantAbsIsThree :
      lowerCMDiscriminantAbs ≡ 3

    upperCMDiscriminantAbs :
      Nat

    upperCMDiscriminantAbsIsSeven :
      upperCMDiscriminantAbs ≡ 7

    lowerJInvariantLabel :
      String

    upperJInvariantLabel :
      String

    cmFaltingsHeightFormula :
      String

    lowerLValueAuthorityLabel :
      String

    upperLValueAuthorityLabel :
      String

    correctionFactorFormula :
      String

    naturalDeg23 :
      Nat

    naturalDeg23IsFourteen :
      naturalDeg23 ≡ 14

    requiredDeg23Diagnostic :
      Float

    requiredDeg23DiagnosticLabel :
      String

    requiredCorrectionFactorLabel :
      String

    faltingsCorrectionComputedInRepo :
      Bool

    faltingsCorrectionComputedInRepoIsFalse :
      faltingsCorrectionComputedInRepo ≡ false

    faltingsCorrectionResolvesResidual :
      Bool

    faltingsCorrectionResolvesResidualIsFalse :
      faltingsCorrectionResolvesResidual ≡ false

    diagnosticRouteRecorded :
      Bool

    diagnosticRouteRecordedIsTrue :
      diagnosticRouteRecorded ≡ true

    physicalCKMPromotionConstructed :
      Bool

    physicalCKMPromotionConstructedIsFalse :
      physicalCKMPromotionConstructed ≡ false

    promotionFlags :
      List FaltingsHeightDeg23Promotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    blockers :
      List FaltingsHeightDeg23Blocker

    blockersAreCanonical :
      blockers ≡ canonicalFaltingsHeightDeg23Blockers

    receiptBoundary :
      List String

open FaltingsHeightDeg23Receipt public

canonicalFaltingsHeightDeg23Receipt :
  FaltingsHeightDeg23Receipt
canonicalFaltingsHeightDeg23Receipt =
  record
    { status =
        faltingsHeightCorrectionRouteRecorded
    ; lowerCMDiscriminantAbs =
        3
    ; lowerCMDiscriminantAbsIsThree =
        refl
    ; upperCMDiscriminantAbs =
        7
    ; upperCMDiscriminantAbsIsSeven =
        refl
    ; lowerJInvariantLabel =
        "E_{j=0}, CM discriminant -3"
    ; upperJInvariantLabel =
        "E_{j=-3375}, CM discriminant -7"
    ; cmFaltingsHeightFormula =
        "h_F(E_D)=-(1/2)log|d_K|-(1/2)log(2*pi)+(1/2)(L'/L)(1,chi_K)"
    ; lowerLValueAuthorityLabel =
        "D=-3: L(1,chi_-3) value known by CM class-number formula; L'/L not formalised here"
    ; upperLValueAuthorityLabel =
        "D=-7: L(1,chi_-7) value known by CM class-number formula; L'/L not formalised here"
    ; correctionFactorFormula =
        "candidate correction = exp(h_F(E_{j=0}) - h_F(E_{j=-3375}))"
    ; naturalDeg23 =
        14
    ; naturalDeg23IsFourteen =
        refl
    ; requiredDeg23Diagnostic =
        14.302
    ; requiredDeg23DiagnosticLabel =
        "required diagnostic deg23 = 14.302"
    ; requiredCorrectionFactorLabel =
        "required multiplicative correction is 14.302 / 14 = 1.021571..."
    ; faltingsCorrectionComputedInRepo =
        false
    ; faltingsCorrectionComputedInRepoIsFalse =
        refl
    ; faltingsCorrectionResolvesResidual =
        false
    ; faltingsCorrectionResolvesResidualIsFalse =
        refl
    ; diagnosticRouteRecorded =
        true
    ; diagnosticRouteRecordedIsTrue =
        refl
    ; physicalCKMPromotionConstructed =
        false
    ; physicalCKMPromotionConstructedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; blockers =
        canonicalFaltingsHeightDeg23Blockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "The Faltings-height route is the next admissible test for the 2.1 percent deg23 residual"
        ∷ "No certified L'/L numerical evaluation is formalised in Agda here"
        ∷ "The receipt therefore records a diagnostic route, not a correction or CKM promotion"
        ∷ []
    }

faltingsHeightDeg23RouteDoesNotPromoteCKM :
  physicalCKMPromotionConstructed canonicalFaltingsHeightDeg23Receipt ≡ false
faltingsHeightDeg23RouteDoesNotPromoteCKM =
  refl

