module DASHI.Physics.Closure.CKMHierarchyFromHeegnerPositionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM hierarchy from Heegner-position gap suppression.
--
-- This receipt tests the diagnostic model:
--
--   |Vub|_gap=2 ~= |Vus| * alpha1^2
--
-- against a PDG-sized |Vub| comparison target.  The model has the right
-- qualitative ordering |Vus| > |Vcb| > |Vub|, but the gap-2 numerical
-- estimate is about ten times too small.  It is therefore recorded as a
-- negative diagnostic only.

data CKMHierarchyFromHeegnerPositionStatus : Set where
  ckmHierarchyGapSuppressionNegativeDiagnostic :
    CKMHierarchyFromHeegnerPositionStatus

data CKMHierarchyFromHeegnerPositionBlocker : Set where
  gapSuppressionUnderpredictsVub :
    CKMHierarchyFromHeegnerPositionBlocker

  missingPhysicalHeegnerPositionToCKMMap :
    CKMHierarchyFromHeegnerPositionBlocker

  missingAcceptedVcbAndVubCarrierDerivation :
    CKMHierarchyFromHeegnerPositionBlocker

  missingPDGAuthorityPromotion :
    CKMHierarchyFromHeegnerPositionBlocker

canonicalCKMHierarchyFromHeegnerPositionBlockers :
  List CKMHierarchyFromHeegnerPositionBlocker
canonicalCKMHierarchyFromHeegnerPositionBlockers =
  gapSuppressionUnderpredictsVub
  ∷ missingPhysicalHeegnerPositionToCKMMap
  ∷ missingAcceptedVcbAndVubCarrierDerivation
  ∷ missingPDGAuthorityPromotion
  ∷ []

data CKMHierarchyFromHeegnerPositionPromotion : Set where

ckmHierarchyFromHeegnerPositionPromotionImpossibleHere :
  CKMHierarchyFromHeegnerPositionPromotion →
  ⊥
ckmHierarchyFromHeegnerPositionPromotionImpossibleHere ()

hierarchyQualitativeLabel : String
hierarchyQualitativeLabel =
  "|Vus| > |Vcb| > |Vub| is qualitatively the desired CKM hierarchy"

gapSuppressionFormulaLabel : String
gapSuppressionFormulaLabel =
  "|Vub|_gap=2 = |Vus| * alpha1^2"

negativeDiagnosticLabel : String
negativeDiagnosticLabel =
  "gap=2 estimate gives |Vub| ~= 0.000383 versus PDG-sized |Vub| ~= 0.00369, about 10x too small"

record CKMHierarchyFromHeegnerPositionReceipt : Setω where
  field
    status :
      CKMHierarchyFromHeegnerPositionStatus

    hierarchyQualitativeStatement :
      String

    hierarchyQualitativeStatementIsCanonical :
      hierarchyQualitativeStatement ≡ hierarchyQualitativeLabel

    gapSuppressionFormula :
      String

    gapSuppressionFormulaIsCanonical :
      gapSuppressionFormula ≡ gapSuppressionFormulaLabel

    alpha1Approx :
      Float

    vusCarrierApprox :
      Float

    positionalGap :
      Nat

    positionalGapIsTwo :
      positionalGap ≡ 2

    vubGapPrediction :
      Float

    pdgVubComparison :
      Float

    pdgOverPredictionApprox :
      Float

    negativeDiagnosticStatement :
      String

    negativeDiagnosticStatementIsCanonical :
      negativeDiagnosticStatement ≡ negativeDiagnosticLabel

    qualitativeHierarchyRecorded :
      Bool

    qualitativeHierarchyRecordedIsTrue :
      qualitativeHierarchyRecorded ≡ true

    gapSuppressionModelTested :
      Bool

    gapSuppressionModelTestedIsTrue :
      gapSuppressionModelTested ≡ true

    vubUnderpredicted :
      Bool

    vubUnderpredictedIsTrue :
      vubUnderpredicted ≡ true

    negativeDiagnosticRecorded :
      Bool

    negativeDiagnosticRecordedIsTrue :
      negativeDiagnosticRecorded ≡ true

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List CKMHierarchyFromHeegnerPositionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMHierarchyFromHeegnerPositionBlockers

    promotionFlags :
      List CKMHierarchyFromHeegnerPositionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMHierarchyFromHeegnerPositionReceipt public

canonicalCKMHierarchyFromHeegnerPositionReceipt :
  CKMHierarchyFromHeegnerPositionReceipt
canonicalCKMHierarchyFromHeegnerPositionReceipt =
  record
    { status =
        ckmHierarchyGapSuppressionNegativeDiagnostic
    ; hierarchyQualitativeStatement =
        hierarchyQualitativeLabel
    ; hierarchyQualitativeStatementIsCanonical =
        refl
    ; gapSuppressionFormula =
        gapSuppressionFormulaLabel
    ; gapSuppressionFormulaIsCanonical =
        refl
    ; alpha1Approx =
        0.04124
    ; vusCarrierApprox =
        0.224403
    ; positionalGap =
        2
    ; positionalGapIsTwo =
        refl
    ; vubGapPrediction =
        0.000383
    ; pdgVubComparison =
        0.00369
    ; pdgOverPredictionApprox =
        9.63
    ; negativeDiagnosticStatement =
        negativeDiagnosticLabel
    ; negativeDiagnosticStatementIsCanonical =
        refl
    ; qualitativeHierarchyRecorded =
        true
    ; qualitativeHierarchyRecordedIsTrue =
        refl
    ; gapSuppressionModelTested =
        true
    ; gapSuppressionModelTestedIsTrue =
        refl
    ; vubUnderpredicted =
        true
    ; vubUnderpredictedIsTrue =
        refl
    ; negativeDiagnosticRecorded =
        true
    ; negativeDiagnosticRecordedIsTrue =
        refl
    ; physicalVubPromoted =
        false
    ; physicalVubPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalCKMHierarchyFromHeegnerPositionBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The positional-gap model captures only the qualitative CKM ordering |Vus| > |Vcb| > |Vub|"
        ∷ "For gap=2 it predicts |Vub| ~= |Vus|*alpha1^2 ~= 0.000383"
        ∷ "The PDG-sized comparison |Vub| ~= 0.00369 is about 9.6 to 10 times larger"
        ∷ "This is a negative diagnostic and does not promote physical Vub or CKM"
        ∷ []
    }

ckmHierarchyGapSuppressionTested :
  gapSuppressionModelTested canonicalCKMHierarchyFromHeegnerPositionReceipt ≡ true
ckmHierarchyGapSuppressionTested =
  refl

ckmHierarchyVubUnderpredicted :
  vubUnderpredicted canonicalCKMHierarchyFromHeegnerPositionReceipt ≡ true
ckmHierarchyVubUnderpredicted =
  refl

ckmHierarchyDoesNotPromoteVub :
  physicalVubPromoted canonicalCKMHierarchyFromHeegnerPositionReceipt ≡ false
ckmHierarchyDoesNotPromoteVub =
  refl

ckmHierarchyDoesNotPromoteCKM :
  physicalCKMPromoted canonicalCKMHierarchyFromHeegnerPositionReceipt ≡ false
ckmHierarchyDoesNotPromoteCKM =
  refl

ckmHierarchyNoPhysicalPromotion :
  CKMHierarchyFromHeegnerPositionPromotion →
  ⊥
ckmHierarchyNoPhysicalPromotion =
  ckmHierarchyFromHeegnerPositionPromotionImpossibleHere
