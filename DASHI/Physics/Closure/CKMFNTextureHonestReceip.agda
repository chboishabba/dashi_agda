module DASHI.Physics.Closure.CKMFNTextureHonestReceip where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM Froggatt-Nielsen texture honest receipt.
--
-- This receipt records the negative result of using symmetric
-- Froggatt-Nielsen texture diagonalisation with the carrier alphas as a CKM
-- derivation.  The resulting CKM entries miss physical CKM targets by factors
-- ranging from about 2 to about 3000, so the FN texture route is exploratory
-- and diagnostic only.
--
-- This does not invalidate alpha1 = sqrt(m_u/m_c) or
-- alpha2 = sqrt(m_c/m_t).  Those alphas remain Yukawa hierarchy diagnostics,
-- not CKM derivations.  The CKM programme uses carrier arithmetic directly.

data CKMFNTextureStatus : Set where
  symmetricFNTextureDiagonalisationFailsCKM :
    CKMFNTextureStatus

data FNTextureProgrammeRole : Set where
  exploratoryDiagnosticOnly :
    FNTextureProgrammeRole

data CKMProgrammeRole : Set where
  carrierArithmeticDirectly :
    CKMProgrammeRole

data FNTextureBlocker : Set where
  symmetricTextureMissesCKMByLargeFactors :
    FNTextureBlocker

  alphaDiagnosticsAreNotCKMDerivations :
    FNTextureBlocker

  noTerminalPhysicalCKMPromotion :
    FNTextureBlocker

canonicalFNTextureBlockers :
  List FNTextureBlocker
canonicalFNTextureBlockers =
  symmetricTextureMissesCKMByLargeFactors
  ∷ alphaDiagnosticsAreNotCKMDerivations
  ∷ noTerminalPhysicalCKMPromotion
  ∷ []

data CKMFNTexturePromotion : Set where

ckmFNTexturePromotionImpossibleHere :
  CKMFNTexturePromotion →
  ⊥
ckmFNTexturePromotionImpossibleHere ()

alpha1DiagnosticLabel : String
alpha1DiagnosticLabel =
  "alpha1 = sqrt(m_u/m_c)"

alpha2DiagnosticLabel : String
alpha2DiagnosticLabel =
  "alpha2 = sqrt(m_c/m_t)"

fnFailureLabel : String
fnFailureLabel =
  "symmetric FN texture diagonalisation with carrier alphas gives CKM entries wrong by factors 2-3000"

ckmProgrammeLabel : String
ckmProgrammeLabel =
  "CKM programme uses carrier arithmetic directly"

fnProgrammeLabel : String
fnProgrammeLabel =
  "FN programme is exploratory and diagnostic only"

record CKMFNTextureHonestReceip : Setω where
  field
    status :
      CKMFNTextureStatus

    statusIsFailure :
      status ≡ symmetricFNTextureDiagonalisationFailsCKM

    symmetricTextureDiagonalisationTested :
      Bool

    symmetricTextureDiagonalisationTestedIsTrue :
      symmetricTextureDiagonalisationTested ≡ true

    usedCarrierAlphas :
      Bool

    usedCarrierAlphasIsTrue :
      usedCarrierAlphas ≡ true

    ckmEntriesWrongByLargeFactors :
      Bool

    ckmEntriesWrongByLargeFactorsIsTrue :
      ckmEntriesWrongByLargeFactors ≡ true

    minimumWrongFactor :
      Nat

    minimumWrongFactorIsCanonical :
      minimumWrongFactor ≡ 2

    maximumWrongFactor :
      Nat

    maximumWrongFactorIsCanonical :
      maximumWrongFactor ≡ 3000

    representativeWrongFactor :
      Float

    representativeWrongFactorIsWithinHonestRange :
      representativeWrongFactor ≡ 3000.0

    failureSummary :
      String

    failureSummaryIsCanonical :
      failureSummary ≡ fnFailureLabel

    alpha1Diagnostic :
      String

    alpha1DiagnosticIsCanonical :
      alpha1Diagnostic ≡ alpha1DiagnosticLabel

    alpha2Diagnostic :
      String

    alpha2DiagnosticIsCanonical :
      alpha2Diagnostic ≡ alpha2DiagnosticLabel

    alphaDiagnosticsRemainValid :
      Bool

    alphaDiagnosticsRemainValidIsTrue :
      alphaDiagnosticsRemainValid ≡ true

    alphasAreYukawaHierarchyDiagnostics :
      Bool

    alphasAreYukawaHierarchyDiagnosticsIsTrue :
      alphasAreYukawaHierarchyDiagnostics ≡ true

    alphasAreCKMDerivations :
      Bool

    alphasAreCKMDerivationsIsFalse :
      alphasAreCKMDerivations ≡ false

    fnProgrammeRole :
      FNTextureProgrammeRole

    fnProgrammeRoleIsDiagnosticOnly :
      fnProgrammeRole ≡ exploratoryDiagnosticOnly

    ckmProgrammeRole :
      CKMProgrammeRole

    ckmProgrammeRoleIsCarrierArithmetic :
      ckmProgrammeRole ≡ carrierArithmeticDirectly

    ckmProgrammeDescription :
      String

    ckmProgrammeDescriptionIsCanonical :
      ckmProgrammeDescription ≡ ckmProgrammeLabel

    fnProgrammeDescription :
      String

    fnProgrammeDescriptionIsCanonical :
      fnProgrammeDescription ≡ fnProgrammeLabel

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalPhysicalCKMPromotionFlag :
      Bool

    terminalPhysicalCKMPromotionFlagIsFalse :
      terminalPhysicalCKMPromotionFlag ≡ false

    terminalCKMPromotionFlag :
      Bool

    terminalCKMPromotionFlagIsFalse :
      terminalCKMPromotionFlag ≡ false

    blockers :
      List FNTextureBlocker

    blockersAreCanonical :
      blockers ≡ canonicalFNTextureBlockers

    promotionFlags :
      List CKMFNTexturePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMFNTextureHonestReceip public

canonicalCKMFNTextureHonestReceip :
  CKMFNTextureHonestReceip
canonicalCKMFNTextureHonestReceip =
  record
    { status =
        symmetricFNTextureDiagonalisationFailsCKM
    ; statusIsFailure =
        refl
    ; symmetricTextureDiagonalisationTested =
        true
    ; symmetricTextureDiagonalisationTestedIsTrue =
        refl
    ; usedCarrierAlphas =
        true
    ; usedCarrierAlphasIsTrue =
        refl
    ; ckmEntriesWrongByLargeFactors =
        true
    ; ckmEntriesWrongByLargeFactorsIsTrue =
        refl
    ; minimumWrongFactor =
        2
    ; minimumWrongFactorIsCanonical =
        refl
    ; maximumWrongFactor =
        3000
    ; maximumWrongFactorIsCanonical =
        refl
    ; representativeWrongFactor =
        3000.0
    ; representativeWrongFactorIsWithinHonestRange =
        refl
    ; failureSummary =
        fnFailureLabel
    ; failureSummaryIsCanonical =
        refl
    ; alpha1Diagnostic =
        alpha1DiagnosticLabel
    ; alpha1DiagnosticIsCanonical =
        refl
    ; alpha2Diagnostic =
        alpha2DiagnosticLabel
    ; alpha2DiagnosticIsCanonical =
        refl
    ; alphaDiagnosticsRemainValid =
        true
    ; alphaDiagnosticsRemainValidIsTrue =
        refl
    ; alphasAreYukawaHierarchyDiagnostics =
        true
    ; alphasAreYukawaHierarchyDiagnosticsIsTrue =
        refl
    ; alphasAreCKMDerivations =
        false
    ; alphasAreCKMDerivationsIsFalse =
        refl
    ; fnProgrammeRole =
        exploratoryDiagnosticOnly
    ; fnProgrammeRoleIsDiagnosticOnly =
        refl
    ; ckmProgrammeRole =
        carrierArithmeticDirectly
    ; ckmProgrammeRoleIsCarrierArithmetic =
        refl
    ; ckmProgrammeDescription =
        ckmProgrammeLabel
    ; ckmProgrammeDescriptionIsCanonical =
        refl
    ; fnProgrammeDescription =
        fnProgrammeLabel
    ; fnProgrammeDescriptionIsCanonical =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalPhysicalCKMPromotionFlag =
        false
    ; terminalPhysicalCKMPromotionFlagIsFalse =
        refl
    ; terminalCKMPromotionFlag =
        false
    ; terminalCKMPromotionFlagIsFalse =
        refl
    ; blockers =
        canonicalFNTextureBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Symmetric FN texture diagonalisation with carrier alphas was tested honestly"
        ∷ "The resulting CKM entries are wrong by factors ranging from 2 to 3000"
        ∷ "This negative CKM result does not invalidate alpha1 = sqrt(m_u/m_c) or alpha2 = sqrt(m_c/m_t)"
        ∷ "Those alphas remain Yukawa hierarchy diagnostics, not CKM derivations"
        ∷ "CKM uses carrier arithmetic directly; FN remains exploratory and diagnostic only"
        ∷ "Physical CKM and terminal CKM promotion flags are false"
        ∷ []
    }

fnTextureCKMFailureRecorded :
  ckmEntriesWrongByLargeFactors canonicalCKMFNTextureHonestReceip
  ≡
  true
fnTextureCKMFailureRecorded =
  refl

fnTextureDoesNotInvalidateAlphaDiagnostics :
  alphaDiagnosticsRemainValid canonicalCKMFNTextureHonestReceip
  ≡
  true
fnTextureDoesNotInvalidateAlphaDiagnostics =
  refl

fnTextureKeepsPhysicalCKMClosed :
  physicalCKMPromoted canonicalCKMFNTextureHonestReceip
  ≡
  false
fnTextureKeepsPhysicalCKMClosed =
  refl

fnTextureKeepsTerminalCKMClosed :
  terminalCKMPromotionFlag canonicalCKMFNTextureHonestReceip
  ≡
  false
fnTextureKeepsTerminalCKMClosed =
  refl
