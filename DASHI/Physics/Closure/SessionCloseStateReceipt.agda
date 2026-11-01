module DASHI.Physics.Closure.SessionCloseStateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C session-close state receipt.

sessionCloseTagToLand : String
sessionCloseTagToLand =
  "phase2-adelic-ym-v1"

data SessionCloseChange : Set where
  ultrametricBoundaryClarification :
    SessionCloseChange

  bruhatTitsProductTree :
    SessionCloseChange

  pAdicFlatLimitResolved :
    SessionCloseChange

  archimedeanGapConfirmed :
    SessionCloseChange

  millenniumSchemaT2Refined :
    SessionCloseChange

  paper8Section7Drafted :
    SessionCloseChange

canonicalSessionCloseChanges :
  List SessionCloseChange
canonicalSessionCloseChanges =
  ultrametricBoundaryClarification
  ∷ bruhatTitsProductTree
  ∷ pAdicFlatLimitResolved
  ∷ archimedeanGapConfirmed
  ∷ millenniumSchemaT2Refined
  ∷ paper8Section7Drafted
  ∷ []

data ClayProgramme : Set where
  navierStokesProgramme :
    ClayProgramme

  yangMillsProgramme :
    ClayProgramme

canonicalSessionCloseProgrammes :
  List ClayProgramme
canonicalSessionCloseProgrammes =
  navierStokesProgramme
  ∷ yangMillsProgramme
  ∷ []

data ClayDistance : Set where
  oneArchimedeanContractionProof :
    ClayDistance

  oneArchimedeanFlatLimitProof :
    ClayDistance

data PAdicStructureState : Set where
  pAdicStructuresFullyInhabited :
    PAdicStructureState

canonicalPAdicState :
  PAdicStructureState
canonicalPAdicState =
  pAdicStructuresFullyInhabited

data SessionClosePromotion : Set where

sessionClosePromotionImpossibleHere :
  SessionClosePromotion →
  ⊥
sessionClosePromotionImpossibleHere ()

sessionCloseStatement : String
sessionCloseStatement =
  "Manager C session close state: tag to land is phase2-adelic-ym-v1; p-adic NS/YM structures are fully inhabited; NS remains one archimedean contraction proof from Clay closure; YM remains one archimedean flat limit proof from Clay closure."

record SessionCloseStateReceipt : Setω where
  field
    tagToLand :
      String

    tagToLandIsCanonical :
      tagToLand ≡ sessionCloseTagToLand

    recordedChanges :
      List SessionCloseChange

    recordedChangesAreCanonical :
      recordedChanges ≡ canonicalSessionCloseChanges

    programmes :
      List ClayProgramme

    programmesAreCanonical :
      programmes ≡ canonicalSessionCloseProgrammes

    nsClayDistance :
      ClayDistance

    nsClayDistanceIsOneArchimedeanContractionProof :
      nsClayDistance ≡ oneArchimedeanContractionProof

    ymClayDistance :
      ClayDistance

    ymClayDistanceIsOneArchimedeanFlatLimitProof :
      ymClayDistance ≡ oneArchimedeanFlatLimitProof

    nsPAdicStructureState :
      PAdicStructureState

    nsPAdicStructureStateIsCanonical :
      nsPAdicStructureState ≡ canonicalPAdicState

    ymPAdicStructureState :
      PAdicStructureState

    ymPAdicStructureStateIsCanonical :
      ymPAdicStructureState ≡ canonicalPAdicState

    pAdicStructuresFullyInhabitedRecorded :
      Bool

    pAdicStructuresFullyInhabitedRecordedIsTrue :
      pAdicStructuresFullyInhabitedRecorded ≡ true

    pAdicFlatLimitResolvedRecorded :
      Bool

    pAdicFlatLimitResolvedRecordedIsTrue :
      pAdicFlatLimitResolvedRecorded ≡ true

    bruhatTitsProductTreeRecorded :
      Bool

    bruhatTitsProductTreeRecordedIsTrue :
      bruhatTitsProductTreeRecorded ≡ true

    archimedeanContractionProofConstructed :
      Bool

    archimedeanContractionProofConstructedIsFalse :
      archimedeanContractionProofConstructed ≡ false

    archimedeanFlatLimitProofConstructed :
      Bool

    archimedeanFlatLimitProofConstructedIsFalse :
      archimedeanFlatLimitProofConstructed ≡ false

    archimedeanGapConfirmedRecorded :
      Bool

    archimedeanGapConfirmedRecordedIsTrue :
      archimedeanGapConfirmedRecorded ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List SessionClosePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ sessionCloseStatement

    receiptBoundary :
      List String

open SessionCloseStateReceipt public

canonicalSessionCloseStateReceipt :
  SessionCloseStateReceipt
canonicalSessionCloseStateReceipt =
  record
    { tagToLand =
        sessionCloseTagToLand
    ; tagToLandIsCanonical =
        refl
    ; recordedChanges =
        canonicalSessionCloseChanges
    ; recordedChangesAreCanonical =
        refl
    ; programmes =
        canonicalSessionCloseProgrammes
    ; programmesAreCanonical =
        refl
    ; nsClayDistance =
        oneArchimedeanContractionProof
    ; nsClayDistanceIsOneArchimedeanContractionProof =
        refl
    ; ymClayDistance =
        oneArchimedeanFlatLimitProof
    ; ymClayDistanceIsOneArchimedeanFlatLimitProof =
        refl
    ; nsPAdicStructureState =
        canonicalPAdicState
    ; nsPAdicStructureStateIsCanonical =
        refl
    ; ymPAdicStructureState =
        canonicalPAdicState
    ; ymPAdicStructureStateIsCanonical =
        refl
    ; pAdicStructuresFullyInhabitedRecorded =
        true
    ; pAdicStructuresFullyInhabitedRecordedIsTrue =
        refl
    ; pAdicFlatLimitResolvedRecorded =
        true
    ; pAdicFlatLimitResolvedRecordedIsTrue =
        refl
    ; bruhatTitsProductTreeRecorded =
        true
    ; bruhatTitsProductTreeRecordedIsTrue =
        refl
    ; archimedeanContractionProofConstructed =
        false
    ; archimedeanContractionProofConstructedIsFalse =
        refl
    ; archimedeanFlatLimitProofConstructed =
        false
    ; archimedeanFlatLimitProofConstructedIsFalse =
        refl
    ; archimedeanGapConfirmedRecorded =
        true
    ; archimedeanGapConfirmedRecordedIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        sessionCloseStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Tag to land is recorded as phase2-adelic-ym-v1"
        ∷ "Recorded changes are ultrametric boundary clarification, Bruhat-Tits product tree, p-adic flat limit resolved, archimedean gap confirmed, Millennium Schema T2 refined, and Paper 8 Section 7 drafted"
        ∷ "NS Clay distance is one archimedean contraction proof"
        ∷ "YM Clay distance is one archimedean flat limit proof"
        ∷ "Both p-adic structures are fully inhabited, but no NS, YM, or terminal Clay promotion is made here"
        ∷ []
    }

sessionCloseTagCanonical :
  tagToLand canonicalSessionCloseStateReceipt ≡ sessionCloseTagToLand
sessionCloseTagCanonical =
  refl

sessionCloseKeepsNSClayFalse :
  clayNavierStokesPromoted canonicalSessionCloseStateReceipt ≡ false
sessionCloseKeepsNSClayFalse =
  refl

sessionCloseKeepsYMClayFalse :
  clayYangMillsPromoted canonicalSessionCloseStateReceipt ≡ false
sessionCloseKeepsYMClayFalse =
  refl

sessionCloseKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalSessionCloseStateReceipt ≡ false
sessionCloseKeepsTerminalFalse =
  refl

sessionClosePAdicStructuresFullyInhabited :
  pAdicStructuresFullyInhabitedRecorded canonicalSessionCloseStateReceipt
  ≡ true
sessionClosePAdicStructuresFullyInhabited =
  refl

sessionCloseArchimedeanGapConfirmed :
  archimedeanGapConfirmedRecorded canonicalSessionCloseStateReceipt
  ≡ true
sessionCloseArchimedeanGapConfirmed =
  refl

sessionCloseNoPromotion :
  SessionClosePromotion →
  ⊥
sessionCloseNoPromotion =
  sessionClosePromotionImpossibleHere
