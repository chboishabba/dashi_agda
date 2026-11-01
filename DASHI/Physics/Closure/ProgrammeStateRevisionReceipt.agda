module DASHI.Physics.Closure.ProgrammeStateRevisionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Programme state revision receipt.
--
-- This C2 receipt records the revised programme map only.  It names four
-- active fronts and keeps the state descriptive: no Clay or terminal
-- promotion flags are introduced here.

data ProgrammeRevisionStatus : Set where
  programmeBroaderAndMorePreciselyMapped :
    ProgrammeRevisionStatus

data ProgrammeActiveFront : Set where
  yukawaTextureFront :
    ProgrammeActiveFront

  navierStokesLargeDataContractionFront :
    ProgrammeActiveFront

  yangMillsPAdicShimuraFlatLimitFront :
    ProgrammeActiveFront

  papersSixAndEightFront :
    ProgrammeActiveFront

canonicalProgrammeActiveFronts :
  List ProgrammeActiveFront
canonicalProgrammeActiveFronts =
  yukawaTextureFront
  ∷ navierStokesLargeDataContractionFront
  ∷ yangMillsPAdicShimuraFlatLimitFront
  ∷ papersSixAndEightFront
  ∷ []

data YukawaTextureRevision : Set where
  yukawaTextureOpenedAlphaOneAlphaTwoGJLeptonsOpen :
    YukawaTextureRevision

data NavierStokesRevision : Set where
  navierStokesConditionallyReducedToH118LargeDataContraction :
    NavierStokesRevision

data YangMillsRevision : Set where
  yangMillsPAdicShimuraFlatLimitBestCandidateGeometricGapOpen :
    YangMillsRevision

data PaperProgrammeRevision : Set where
  papersSixAndEightTrackedPaperEightSectionSevenMillenniumTowerSchema :
    PaperProgrammeRevision

yukawaTextureRevisionStatement : String
yukawaTextureRevisionStatement =
  "Yukawa texture front opened: alpha1 and alpha2 are identified, Georgi-Jarlskog is explained, and the lepton sector remains open."

navierStokesRevisionStatement : String
navierStokesRevisionStatement =
  "Navier-Stokes Clay front is conditionally reduced to a large-data contraction problem in H^{11/8}."

yangMillsRevisionStatement : String
yangMillsRevisionStatement =
  "Yang-Mills Clay front: the p-adic Shimura flat limit is the best current candidate, with the geometric gap obstruction recorded."

paperProgrammeRevisionStatement : String
paperProgrammeRevisionStatement =
  "Papers 6 and 8 remain active; Paper 8 gains Section 7, the Millennium Tower Schema."

programmeStateRevisionStatement : String
programmeStateRevisionStatement =
  "Revised programme state: the programme is broader and more precisely mapped across Yukawa texture, NS H^{11/8} contraction, YM p-adic Shimura flat limit, and Papers 6/8."

record ProgrammeStateRevisionReceipt : Setω where
  field
    status :
      ProgrammeRevisionStatus

    fronts :
      List ProgrammeActiveFront

    frontsAreCanonical :
      fronts ≡ canonicalProgrammeActiveFronts

    yukawaTextureRevision :
      YukawaTextureRevision

    yukawaTextureOpened :
      Bool

    yukawaTextureOpenedIsTrue :
      yukawaTextureOpened ≡ true

    alphaOneIdentified :
      Bool

    alphaOneIdentifiedIsTrue :
      alphaOneIdentified ≡ true

    alphaTwoIdentified :
      Bool

    alphaTwoIdentifiedIsTrue :
      alphaTwoIdentified ≡ true

    georgiJarlskogExplained :
      Bool

    georgiJarlskogExplainedIsTrue :
      georgiJarlskogExplained ≡ true

    leptonSectorOpen :
      Bool

    leptonSectorOpenIsTrue :
      leptonSectorOpen ≡ true

    navierStokesRevision :
      NavierStokesRevision

    nsConditionallyReducedToLargeDataH118Contraction :
      Bool

    nsConditionallyReducedToLargeDataH118ContractionIsTrue :
      nsConditionallyReducedToLargeDataH118Contraction ≡ true

    yangMillsRevision :
      YangMillsRevision

    ymPAdicShimuraFlatLimitBestCandidate :
      Bool

    ymPAdicShimuraFlatLimitBestCandidateIsTrue :
      ymPAdicShimuraFlatLimitBestCandidate ≡ true

    ymGeometricGapObstructionRecorded :
      Bool

    ymGeometricGapObstructionRecordedIsTrue :
      ymGeometricGapObstructionRecorded ≡ true

    paperProgrammeRevision :
      PaperProgrammeRevision

    papersSixAndEightActive :
      Bool

    papersSixAndEightActiveIsTrue :
      papersSixAndEightActive ≡ true

    paperEightSectionSevenMillenniumTowerSchemaAdded :
      Bool

    paperEightSectionSevenMillenniumTowerSchemaAddedIsTrue :
      paperEightSectionSevenMillenniumTowerSchemaAdded ≡ true

    programmeBroader :
      Bool

    programmeBroaderIsTrue :
      programmeBroader ≡ true

    programmeMorePreciselyMapped :
      Bool

    programmeMorePreciselyMappedIsTrue :
      programmeMorePreciselyMapped ≡ true

    yukawaStatement :
      String

    yukawaStatementIsCanonical :
      yukawaStatement ≡ yukawaTextureRevisionStatement

    navierStokesStatement :
      String

    navierStokesStatementIsCanonical :
      navierStokesStatement ≡ navierStokesRevisionStatement

    yangMillsStatement :
      String

    yangMillsStatementIsCanonical :
      yangMillsStatement ≡ yangMillsRevisionStatement

    paperStatement :
      String

    paperStatementIsCanonical :
      paperStatement ≡ paperProgrammeRevisionStatement

    statement :
      String

    statementIsCanonical :
      statement ≡ programmeStateRevisionStatement

    receiptBoundary :
      List String

open ProgrammeStateRevisionReceipt public

canonicalProgrammeStateRevisionReceipt :
  ProgrammeStateRevisionReceipt
canonicalProgrammeStateRevisionReceipt =
  record
    { status =
        programmeBroaderAndMorePreciselyMapped
    ; fronts =
        canonicalProgrammeActiveFronts
    ; frontsAreCanonical =
        refl
    ; yukawaTextureRevision =
        yukawaTextureOpenedAlphaOneAlphaTwoGJLeptonsOpen
    ; yukawaTextureOpened =
        true
    ; yukawaTextureOpenedIsTrue =
        refl
    ; alphaOneIdentified =
        true
    ; alphaOneIdentifiedIsTrue =
        refl
    ; alphaTwoIdentified =
        true
    ; alphaTwoIdentifiedIsTrue =
        refl
    ; georgiJarlskogExplained =
        true
    ; georgiJarlskogExplainedIsTrue =
        refl
    ; leptonSectorOpen =
        true
    ; leptonSectorOpenIsTrue =
        refl
    ; navierStokesRevision =
        navierStokesConditionallyReducedToH118LargeDataContraction
    ; nsConditionallyReducedToLargeDataH118Contraction =
        true
    ; nsConditionallyReducedToLargeDataH118ContractionIsTrue =
        refl
    ; yangMillsRevision =
        yangMillsPAdicShimuraFlatLimitBestCandidateGeometricGapOpen
    ; ymPAdicShimuraFlatLimitBestCandidate =
        true
    ; ymPAdicShimuraFlatLimitBestCandidateIsTrue =
        refl
    ; ymGeometricGapObstructionRecorded =
        true
    ; ymGeometricGapObstructionRecordedIsTrue =
        refl
    ; paperProgrammeRevision =
        papersSixAndEightTrackedPaperEightSectionSevenMillenniumTowerSchema
    ; papersSixAndEightActive =
        true
    ; papersSixAndEightActiveIsTrue =
        refl
    ; paperEightSectionSevenMillenniumTowerSchemaAdded =
        true
    ; paperEightSectionSevenMillenniumTowerSchemaAddedIsTrue =
        refl
    ; programmeBroader =
        true
    ; programmeBroaderIsTrue =
        refl
    ; programmeMorePreciselyMapped =
        true
    ; programmeMorePreciselyMappedIsTrue =
        refl
    ; yukawaStatement =
        yukawaTextureRevisionStatement
    ; yukawaStatementIsCanonical =
        refl
    ; navierStokesStatement =
        navierStokesRevisionStatement
    ; navierStokesStatementIsCanonical =
        refl
    ; yangMillsStatement =
        yangMillsRevisionStatement
    ; yangMillsStatementIsCanonical =
        refl
    ; paperStatement =
        paperProgrammeRevisionStatement
    ; paperStatementIsCanonical =
        refl
    ; statement =
        programmeStateRevisionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        yukawaTextureRevisionStatement
        ∷ navierStokesRevisionStatement
        ∷ yangMillsRevisionStatement
        ∷ paperProgrammeRevisionStatement
        ∷ programmeStateRevisionStatement
        ∷ []
    }
