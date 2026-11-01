module DASHI.Physics.Closure.CarrierWeaveDefectOriginRemark where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Carrier weave / residual-defect origin remark.
--
-- This is an origin/narrative receipt only.  It records the explanatory
-- vocabulary:
--
--   Warp = refinement depth
--   Weft = prime-lane address
--   Wax  = projection-defect binding
--
-- Residual defect accumulation may be compared, as vocabulary, to an
-- inter-ply fibre / refinement-continuity severing defect.  The OceanGate
-- analogy boundary is the latest narrow one: sanding penetrated about 15
-- plies within each superply and repeated about 8 times, producing a
-- systematic periodic inter-depth discontinuity / resonant defect.  The
-- primary defect is therefore not merely missing or removed Wax / epoxy
-- binding, and not merely the final exterior surface: Wax may exist, but
-- bind already severed warp/refinement threads.  Coarse QC may see
-- ply/fibre uniformity while missing inter-depth continuity.  This
-- comparison is not new mathematics, not a safety/materials theorem, and
-- not evidence for importing accident or longevity metaphors into the
-- carrier receipts.

data CarrierWeaveDefectOriginRemarkStatus : Set where
  originRemark_explanatoryVocabularyOnly :
    CarrierWeaveDefectOriginRemarkStatus

data WeaveTerm : Set where
  Warp :
    WeaveTerm

  Weft :
    WeaveTerm

  Wax :
    WeaveTerm

data CarrierRole : Set where
  refinementDepth :
    CarrierRole

  primeLaneAddress :
    CarrierRole

  projectionDefectBinding :
    CarrierRole

data AnalogyDiscipline : Set where
  residualDefectAccumulationAsInterPlyStressAnalogy :
    AnalogyDiscipline

data BlockedEvidenceMetaphor : Set where
  OceanGateMetaphor :
    BlockedEvidenceMetaphor

  LongevityMetaphor :
    BlockedEvidenceMetaphor

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

canonicalWeaveTerms :
  List WeaveTerm
canonicalWeaveTerms =
  Warp
  ∷ Weft
  ∷ Wax
  ∷ []

canonicalCarrierRoles :
  List CarrierRole
canonicalCarrierRoles =
  refinementDepth
  ∷ primeLaneAddress
  ∷ projectionDefectBinding
  ∷ []

canonicalAnalogyDiscipline :
  List AnalogyDiscipline
canonicalAnalogyDiscipline =
  residualDefectAccumulationAsInterPlyStressAnalogy
  ∷ []

canonicalBlockedEvidenceMetaphors :
  List BlockedEvidenceMetaphor
canonicalBlockedEvidenceMetaphors =
  OceanGateMetaphor
  ∷ LongevityMetaphor
  ∷ []

warpStatement :
  String
warpStatement =
  "Warp is explanatory vocabulary for refinement depth."

weftStatement :
  String
weftStatement =
  "Weft is explanatory vocabulary for prime-lane address."

waxStatement :
  String
waxStatement =
  "Wax is explanatory vocabulary for projection-defect binding; its presence does not imply intact warp/refinement continuity."

residualDefectAnalogyStatement :
  String
residualDefectAnalogyStatement =
  "Residual defect accumulation is analogous to inter-ply fibre/refinement-continuity severing only as explanatory vocabulary."

primaryDefectStatement :
  String
primaryDefectStatement =
  "Primary weave defect: systematic periodic inter-depth discontinuity / resonant defect from repeated about-15-ply penetration within each superply, not merely missing Wax/epoxy or final exterior surface."

waxBindsSeveredThreadsStatement :
  String
waxBindsSeveredThreadsStatement =
  "Wax may exist but bind severed warp/refinement threads."

qcContinuityBlindSpotStatement :
  String
qcContinuityBlindSpotStatement =
  "QC may see coarse ply/fibre uniformity and miss systematic periodic inter-depth continuity loss."

blockedMetaphorStatement :
  String
blockedMetaphorStatement =
  "OceanGate and longevity metaphors are explanatory vocabulary only; OceanGate is bounded to the about-15-plies-within-each-superply, about-8-repetitions resonant-defect analogy and is explicitly blocked from being receipted as evidence."

boundaryStatement :
  String
boundaryStatement =
  "Origin remark only: no new mathematics, no safety theorem, no materials theorem, and no evidential promotion are asserted."

record CarrierWeaveDefectOriginRemark : Set where
  field
    status :
      CarrierWeaveDefectOriginRemarkStatus

    statusIsOriginVocabularyOnly :
      status ≡ originRemark_explanatoryVocabularyOnly

    terms :
      List WeaveTerm

    termsAreCanonical :
      terms ≡ canonicalWeaveTerms

    roles :
      List CarrierRole

    rolesAreCanonical :
      roles ≡ canonicalCarrierRoles

    warpRole :
      CarrierRole

    warpRoleIsRefinementDepth :
      warpRole ≡ refinementDepth

    weftRole :
      CarrierRole

    weftRoleIsPrimeLaneAddress :
      weftRole ≡ primeLaneAddress

    waxRole :
      CarrierRole

    waxRoleIsProjectionDefectBinding :
      waxRole ≡ projectionDefectBinding

    warpSummary :
      String

    warpSummaryIsCanonical :
      warpSummary ≡ warpStatement

    weftSummary :
      String

    weftSummaryIsCanonical :
      weftSummary ≡ weftStatement

    waxSummary :
      String

    waxSummaryIsCanonical :
      waxSummary ≡ waxStatement

    analogyDiscipline :
      List AnalogyDiscipline

    analogyDisciplineIsCanonical :
      analogyDiscipline ≡ canonicalAnalogyDiscipline

    residualDefectAccumulationAnalogyAllowed :
      Bool

    residualDefectAccumulationAnalogyAllowedIsTrue :
      residualDefectAccumulationAnalogyAllowed ≡ true

    residualDefectAnalogySummary :
      String

    residualDefectAnalogySummaryIsCanonical :
      residualDefectAnalogySummary ≡ residualDefectAnalogyStatement

    primaryDefectSummary :
      String

    primaryDefectSummaryIsCanonical :
      primaryDefectSummary ≡ primaryDefectStatement

    waxBindsSeveredThreadsSummary :
      String

    waxBindsSeveredThreadsSummaryIsCanonical :
      waxBindsSeveredThreadsSummary ≡ waxBindsSeveredThreadsStatement

    qcContinuityBlindSpotSummary :
      String

    qcContinuityBlindSpotSummaryIsCanonical :
      qcContinuityBlindSpotSummary ≡ qcContinuityBlindSpotStatement

    explanatoryVocabularyOnly :
      Bool

    explanatoryVocabularyOnlyIsTrue :
      explanatoryVocabularyOnly ≡ true

    newMathematicsPromoted :
      Bool

    newMathematicsPromotedIsFalse :
      newMathematicsPromoted ≡ false

    safetyTheoremPromoted :
      Bool

    safetyTheoremPromotedIsFalse :
      safetyTheoremPromoted ≡ false

    materialsTheoremPromoted :
      Bool

    materialsTheoremPromotedIsFalse :
      materialsTheoremPromoted ≡ false

    blockedEvidenceMetaphors :
      List BlockedEvidenceMetaphor

    blockedEvidenceMetaphorsAreCanonical :
      blockedEvidenceMetaphors ≡ canonicalBlockedEvidenceMetaphors

    OceanGateMetaphorReceiptedAsEvidence :
      Bool

    OceanGateMetaphorReceiptedAsEvidenceIsFalse :
      OceanGateMetaphorReceiptedAsEvidence ≡ false

    longevityMetaphorReceiptedAsEvidence :
      Bool

    longevityMetaphorReceiptedAsEvidenceIsFalse :
      longevityMetaphorReceiptedAsEvidence ≡ false

    blockedMetaphorSummary :
      String

    blockedMetaphorSummaryIsCanonical :
      blockedMetaphorSummary ≡ blockedMetaphorStatement

    promotionFlags :
      List PromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ boundaryStatement

open CarrierWeaveDefectOriginRemark public

canonicalCarrierWeaveDefectOriginRemark :
  CarrierWeaveDefectOriginRemark
canonicalCarrierWeaveDefectOriginRemark =
  record
    { status =
        originRemark_explanatoryVocabularyOnly
    ; statusIsOriginVocabularyOnly =
        refl
    ; terms =
        canonicalWeaveTerms
    ; termsAreCanonical =
        refl
    ; roles =
        canonicalCarrierRoles
    ; rolesAreCanonical =
        refl
    ; warpRole =
        refinementDepth
    ; warpRoleIsRefinementDepth =
        refl
    ; weftRole =
        primeLaneAddress
    ; weftRoleIsPrimeLaneAddress =
        refl
    ; waxRole =
        projectionDefectBinding
    ; waxRoleIsProjectionDefectBinding =
        refl
    ; warpSummary =
        warpStatement
    ; warpSummaryIsCanonical =
        refl
    ; weftSummary =
        weftStatement
    ; weftSummaryIsCanonical =
        refl
    ; waxSummary =
        waxStatement
    ; waxSummaryIsCanonical =
        refl
    ; analogyDiscipline =
        canonicalAnalogyDiscipline
    ; analogyDisciplineIsCanonical =
        refl
    ; residualDefectAccumulationAnalogyAllowed =
        true
    ; residualDefectAccumulationAnalogyAllowedIsTrue =
        refl
    ; residualDefectAnalogySummary =
        residualDefectAnalogyStatement
    ; residualDefectAnalogySummaryIsCanonical =
        refl
    ; primaryDefectSummary =
        primaryDefectStatement
    ; primaryDefectSummaryIsCanonical =
        refl
    ; waxBindsSeveredThreadsSummary =
        waxBindsSeveredThreadsStatement
    ; waxBindsSeveredThreadsSummaryIsCanonical =
        refl
    ; qcContinuityBlindSpotSummary =
        qcContinuityBlindSpotStatement
    ; qcContinuityBlindSpotSummaryIsCanonical =
        refl
    ; explanatoryVocabularyOnly =
        true
    ; explanatoryVocabularyOnlyIsTrue =
        refl
    ; newMathematicsPromoted =
        false
    ; newMathematicsPromotedIsFalse =
        refl
    ; safetyTheoremPromoted =
        false
    ; safetyTheoremPromotedIsFalse =
        refl
    ; materialsTheoremPromoted =
        false
    ; materialsTheoremPromotedIsFalse =
        refl
    ; blockedEvidenceMetaphors =
        canonicalBlockedEvidenceMetaphors
    ; blockedEvidenceMetaphorsAreCanonical =
        refl
    ; OceanGateMetaphorReceiptedAsEvidence =
        false
    ; OceanGateMetaphorReceiptedAsEvidenceIsFalse =
        refl
    ; longevityMetaphorReceiptedAsEvidence =
        false
    ; longevityMetaphorReceiptedAsEvidenceIsFalse =
        refl
    ; blockedMetaphorSummary =
        blockedMetaphorStatement
    ; blockedMetaphorSummaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        boundaryStatement
    ; receiptBoundaryIsCanonical =
        refl
    }

warpWeftWaxRolesRecorded :
  roles canonicalCarrierWeaveDefectOriginRemark
  ≡
  canonicalCarrierRoles
warpWeftWaxRolesRecorded =
  refl

residualDefectAnalogyIsVocabularyOnly :
  residualDefectAccumulationAnalogyAllowed
    canonicalCarrierWeaveDefectOriginRemark
  ≡
  true
residualDefectAnalogyIsVocabularyOnly =
  refl

originRemarkPromotesNoNewMathematics :
  newMathematicsPromoted canonicalCarrierWeaveDefectOriginRemark
  ≡
  false
originRemarkPromotesNoNewMathematics =
  refl

originRemarkPromotesNoSafetyOrMaterialsTheorem :
  safetyTheoremPromoted canonicalCarrierWeaveDefectOriginRemark
  ≡
  false
originRemarkPromotesNoSafetyOrMaterialsTheorem =
  refl

OceanGateMetaphorIsNotEvidence :
  OceanGateMetaphorReceiptedAsEvidence
    canonicalCarrierWeaveDefectOriginRemark
  ≡
  false
OceanGateMetaphorIsNotEvidence =
  refl

longevityMetaphorIsNotEvidence :
  longevityMetaphorReceiptedAsEvidence
    canonicalCarrierWeaveDefectOriginRemark
  ≡
  false
longevityMetaphorIsNotEvidence =
  refl
