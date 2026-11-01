module DASHI.Physics.Closure.CKMArithmeticVsFNTextureReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM arithmetic versus Froggatt-Nielsen texture receipt.
--
-- This records the honest boundary of the CKM/Yukawa programme.  The
-- Froggatt-Nielsen texture construction with carrier alphas is retained as
-- a diagnostic for order-of-magnitude Yukawa hierarchy.  It is not promoted
-- as the derivation of precise CKM entries, because direct matrix
-- diagonalisation was found to miss the entries by factors ranging from
-- about 2 to about 3000.
--
-- The precise DASHI CKM entries remain arithmetic-first: lambda comes from
-- the Heegner/isogeny/Wolfenstein carrier structure, and |Vcb| comes from
-- isogeny degree.

data CKMArithmeticVsFNTextureStatus : Set where
  honestBoundaryRecorded :
    CKMArithmeticVsFNTextureStatus

data CKMArithmeticVsFNTextureBlocker : Set where
  fnDiagonalisationDoesNotReproducePreciseCKM :
    CKMArithmeticVsFNTextureBlocker

  fnTextureIsOnlyOrderOfMagnitudeYukawaDiagnostic :
    CKMArithmeticVsFNTextureBlocker

  preciseCKMRequiresHeegnerIsogenyWolfensteinArithmetic :
    CKMArithmeticVsFNTextureBlocker

canonicalCKMArithmeticVsFNTextureBlockers :
  List CKMArithmeticVsFNTextureBlocker
canonicalCKMArithmeticVsFNTextureBlockers =
  fnDiagonalisationDoesNotReproducePreciseCKM
  ∷ fnTextureIsOnlyOrderOfMagnitudeYukawaDiagnostic
  ∷ preciseCKMRequiresHeegnerIsogenyWolfensteinArithmetic
  ∷ []

data CKMArithmeticVsFNTexturePromotion : Set where

ckmArithmeticVsFNTexturePromotionImpossibleHere :
  CKMArithmeticVsFNTexturePromotion →
  ⊥
ckmArithmeticVsFNTexturePromotionImpossibleHere ()

yukawaProgrammeDiagnosticOnlyLabel : String
yukawaProgrammeDiagnosticOnlyLabel =
  "exploratory diagnostic only"

ckmProgrammeArithmeticFirstLabel : String
ckmProgrammeArithmeticFirstLabel =
  "arithmetic first"

fnDiagonalisationFailureRangeLabel : String
fnDiagonalisationFailureRangeLabel =
  "direct FN texture matrix diagonalisation missed precise CKM entries by factors about 2 to 3000"

lambdaArithmeticSourceLabel : String
lambdaArithmeticSourceLabel =
  "lambda from Heegner/isogeny/Wolfenstein carrier arithmetic"

vcbArithmeticSourceLabel : String
vcbArithmeticSourceLabel =
  "|Vcb| from isogeny degree"

record CKMArithmeticVsFNTextureReceipt : Set where
  field
    status :
      CKMArithmeticVsFNTextureStatus

    FNTextureIsDiagnosticOnly :
      Bool

    FNTextureIsDiagnosticOnlyIsTrue :
      FNTextureIsDiagnosticOnly ≡ true

    preciseCKMRequiresCarrierArithmetic :
      Bool

    preciseCKMRequiresCarrierArithmeticIsTrue :
      preciseCKMRequiresCarrierArithmetic ≡ true

    existingDASHILambdaAndVcbFromArithmetic :
      Bool

    existingDASHILambdaAndVcbFromArithmeticIsTrue :
      existingDASHILambdaAndVcbFromArithmetic ≡ true

    FNDiagonalisationFails :
      Bool

    FNDiagonalisationFailsIsTrue :
      FNDiagonalisationFails ≡ true

    yukawaProgramme :
      String

    yukawaProgrammeIsExploratoryDiagnosticOnly :
      yukawaProgramme ≡ yukawaProgrammeDiagnosticOnlyLabel

    ckmProgramme :
      String

    ckmProgrammeIsArithmeticFirst :
      ckmProgramme ≡ ckmProgrammeArithmeticFirstLabel

    carrierAlphasPhysicallyMeaningful :
      Bool

    carrierAlphasPhysicallyMeaningfulIsTrue :
      carrierAlphasPhysicallyMeaningful ≡ true

    fnTexturesGiveYukawaHierarchyOrderOfMagnitude :
      Bool

    fnTexturesGiveYukawaHierarchyOrderOfMagnitudeIsTrue :
      fnTexturesGiveYukawaHierarchyOrderOfMagnitude ≡ true

    fnTexturesReplaceArithmeticCKMDerivation :
      Bool

    fnTexturesReplaceArithmeticCKMDerivationIsFalse :
      fnTexturesReplaceArithmeticCKMDerivation ≡ false

    diagonalisationFailureRange :
      String

    diagonalisationFailureRangeIsCanonical :
      diagonalisationFailureRange ≡ fnDiagonalisationFailureRangeLabel

    lambdaSource :
      String

    lambdaSourceIsArithmetic :
      lambdaSource ≡ lambdaArithmeticSourceLabel

    vcbSource :
      String

    vcbSourceIsArithmetic :
      vcbSource ≡ vcbArithmeticSourceLabel

    blockers :
      List CKMArithmeticVsFNTextureBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMArithmeticVsFNTextureBlockers

    promotionFlags :
      List CKMArithmeticVsFNTexturePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMArithmeticVsFNTextureReceipt public

canonicalCKMArithmeticVsFNTextureReceipt :
  CKMArithmeticVsFNTextureReceipt
canonicalCKMArithmeticVsFNTextureReceipt =
  record
    { status =
        honestBoundaryRecorded
    ; FNTextureIsDiagnosticOnly =
        true
    ; FNTextureIsDiagnosticOnlyIsTrue =
        refl
    ; preciseCKMRequiresCarrierArithmetic =
        true
    ; preciseCKMRequiresCarrierArithmeticIsTrue =
        refl
    ; existingDASHILambdaAndVcbFromArithmetic =
        true
    ; existingDASHILambdaAndVcbFromArithmeticIsTrue =
        refl
    ; FNDiagonalisationFails =
        true
    ; FNDiagonalisationFailsIsTrue =
        refl
    ; yukawaProgramme =
        yukawaProgrammeDiagnosticOnlyLabel
    ; yukawaProgrammeIsExploratoryDiagnosticOnly =
        refl
    ; ckmProgramme =
        ckmProgrammeArithmeticFirstLabel
    ; ckmProgrammeIsArithmeticFirst =
        refl
    ; carrierAlphasPhysicallyMeaningful =
        true
    ; carrierAlphasPhysicallyMeaningfulIsTrue =
        refl
    ; fnTexturesGiveYukawaHierarchyOrderOfMagnitude =
        true
    ; fnTexturesGiveYukawaHierarchyOrderOfMagnitudeIsTrue =
        refl
    ; fnTexturesReplaceArithmeticCKMDerivation =
        false
    ; fnTexturesReplaceArithmeticCKMDerivationIsFalse =
        refl
    ; diagonalisationFailureRange =
        fnDiagonalisationFailureRangeLabel
    ; diagonalisationFailureRangeIsCanonical =
        refl
    ; lambdaSource =
        lambdaArithmeticSourceLabel
    ; lambdaSourceIsArithmetic =
        refl
    ; vcbSource =
        vcbArithmeticSourceLabel
    ; vcbSourceIsArithmetic =
        refl
    ; blockers =
        canonicalCKMArithmeticVsFNTextureBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "FN textures with carrier alphas give the correct order-of-magnitude Yukawa hierarchy"
        ∷ "FN texture diagonalisation does not reproduce precise CKM entries; computation found errors by factors about 2 to 3000"
        ∷ "Carrier alphas are physically meaningful diagnostics, but FN textures do not replace arithmetic CKM derivation"
        ∷ "Precise DASHI lambda comes from Heegner/isogeny/Wolfenstein carrier arithmetic"
        ∷ "Precise DASHI |Vcb| comes from isogeny degree"
        ∷ "Yukawa programme remains exploratory diagnostic only"
        ∷ "CKM programme remains arithmetic first"
        ∷ "No promotions are issued by this receipt"
        ∷ []
    }

fnTextureIsDiagnosticOnlyFlag :
  FNTextureIsDiagnosticOnly canonicalCKMArithmeticVsFNTextureReceipt
  ≡
  true
fnTextureIsDiagnosticOnlyFlag =
  refl

preciseCKMRequiresCarrierArithmeticFlag :
  preciseCKMRequiresCarrierArithmetic
    canonicalCKMArithmeticVsFNTextureReceipt
  ≡
  true
preciseCKMRequiresCarrierArithmeticFlag =
  refl

existingDASHILambdaAndVcbFromArithmeticFlag :
  existingDASHILambdaAndVcbFromArithmetic
    canonicalCKMArithmeticVsFNTextureReceipt
  ≡
  true
existingDASHILambdaAndVcbFromArithmeticFlag =
  refl

fnDiagonalisationFailsFlag :
  FNDiagonalisationFails canonicalCKMArithmeticVsFNTextureReceipt
  ≡
  true
fnDiagonalisationFailsFlag =
  refl

ckmArithmeticVsFNTextureNoPromotions :
  promotionFlags canonicalCKMArithmeticVsFNTextureReceipt
  ≡
  []
ckmArithmeticVsFNTextureNoPromotions =
  refl
