module DASHI.Physics.Closure.CKMPhaseFromCMFieldsReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM phase diagnostic from CM periods.
--
-- With the period formulae recorded here as positive real normalisations, the
-- principal argument of Omega_-7 / Omega_-4 is zero.  That does not match the
-- PDG CKM phase near 1.196 radians, so this route is diagnostic-negative until
-- a non-real CM embedding/period convention is derived.

data CKMPhaseFromCMFieldsStatus : Set where
  positiveRealPeriodRatioGivesZeroPhase :
    CKMPhaseFromCMFieldsStatus

data CKMPhaseBlocker : Set where
  missingNonRealCMEmbeddingChoice :
    CKMPhaseBlocker

  missingPhysicalCPPhaseAuthority :
    CKMPhaseBlocker

canonicalCKMPhaseBlockers :
  List CKMPhaseBlocker
canonicalCKMPhaseBlockers =
  missingNonRealCMEmbeddingChoice
  ∷ missingPhysicalCPPhaseAuthority
  ∷ []

data CKMPhasePromotion : Set where

ckmPhasePromotionImpossibleHere :
  CKMPhasePromotion →
  ⊥
ckmPhasePromotionImpossibleHere ()

record CKMPhaseFromCMFieldsReceipt : Set where
  field
    status :
      CKMPhaseFromCMFieldsStatus

    omegaMinus4Formula :
      String

    omegaMinus7Formula :
      String

    phaseFormula :
      String

    principalPhaseRadians :
      Float

    principalPhaseRadiansLabel :
      String

    pdgComparisonRadians :
      Float

    pdgComparisonRadiansLabel :
      String

    phaseMatchesPDG :
      Bool

    phaseMatchesPDGIsFalse :
      phaseMatchesPDG ≡ false

    cmPhaseDiagnosticRecorded :
      Bool

    cmPhaseDiagnosticRecordedIsTrue :
      cmPhaseDiagnosticRecorded ≡ true

    physicalCPPhaseDerived :
      Bool

    physicalCPPhaseDerivedIsFalse :
      physicalCPPhaseDerived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List CKMPhaseBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMPhaseBlockers

    promotionFlags :
      List CKMPhasePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMPhaseFromCMFieldsReceipt public

canonicalCKMPhaseFromCMFieldsReceipt :
  CKMPhaseFromCMFieldsReceipt
canonicalCKMPhaseFromCMFieldsReceipt =
  record
    { status =
        positiveRealPeriodRatioGivesZeroPhase
    ; omegaMinus4Formula =
        "Omega_-4 = Gamma(1/4)^2 / (4*sqrt(pi))"
    ; omegaMinus7Formula =
        "Omega_-7 = Gamma(1/7)Gamma(2/7)Gamma(4/7)/(2*pi*sqrt(7))"
    ; phaseFormula =
        "delta = arg(Omega_-7 / Omega_-4)"
    ; principalPhaseRadians =
        0.0
    ; principalPhaseRadiansLabel =
        "positive real period ratio has principal argument 0 radians"
    ; pdgComparisonRadians =
        1.196
    ; pdgComparisonRadiansLabel =
        "PDG CKM phase comparison near 1.196 radians"
    ; phaseMatchesPDG =
        false
    ; phaseMatchesPDGIsFalse =
        refl
    ; cmPhaseDiagnosticRecorded =
        true
    ; cmPhaseDiagnosticRecordedIsTrue =
        refl
    ; physicalCPPhaseDerived =
        false
    ; physicalCPPhaseDerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalCKMPhaseBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The supplied CM period formulae are positive real under the principal branch"
        ∷ "The resulting phase is 0, not the physical CKM CP phase"
        ∷ "A non-real CM embedding or additional DHR phase source is required"
        ∷ []
    }

ckmPhaseFromCMFieldsDoesNotMatchPDG :
  phaseMatchesPDG canonicalCKMPhaseFromCMFieldsReceipt ≡ false
ckmPhaseFromCMFieldsDoesNotMatchPDG =
  refl

