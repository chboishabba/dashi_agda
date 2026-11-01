module DASHI.Physics.Closure.FinalPaperSectionTriageReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C task C4: final paper-section triage receipt.
--
-- This is a governance/status receipt only.  It records the final section
-- triage for Papers 6 and 8, names the Paper 8 Section 3 conductor exhaustion
-- table as the most important completion task, and keeps promotion flags false.

data Paper6ReviewGate : Set where
  afterSections4to6 :
    Paper6ReviewGate

data Paper8BottleneckSection : Set where
  section3ConductorExhaustionTable :
    Paper8BottleneckSection

paper8BottleneckSectionLabel : String
paper8BottleneckSectionLabel =
  "3 exhaustion table"

data PaperSectionStatus : Set where
  complete :
    PaperSectionStatus

  assigned :
    PaperSectionStatus

data Paper6Section : Set where
  paper6Section1 :
    Paper6Section

  paper6Section2 :
    Paper6Section

  paper6Section3 :
    Paper6Section

  paper6Section4 :
    Paper6Section

  paper6Section5 :
    Paper6Section

  paper6Section6 :
    Paper6Section

data Paper8Section : Set where
  paper8Section1 :
    Paper8Section

  paper8Section2 :
    Paper8Section

  paper8Section3 :
    Paper8Section

  paper8Section4 :
    Paper8Section

  paper8Section5 :
    Paper8Section

  paper8Section6 :
    Paper8Section

record Paper6SectionLine : Set where
  field
    section :
      Paper6Section

    status :
      PaperSectionStatus

open Paper6SectionLine public

record Paper8SectionLine : Set where
  field
    section :
      Paper8Section

    status :
      PaperSectionStatus

open Paper8SectionLine public

paper6Sections1to3Complete :
  List Paper6SectionLine
paper6Sections1to3Complete =
  record { section = paper6Section1 ; status = complete }
  ∷ record { section = paper6Section2 ; status = complete }
  ∷ record { section = paper6Section3 ; status = complete }
  ∷ []

paper6Sections4to6Assigned :
  List Paper6SectionLine
paper6Sections4to6Assigned =
  record { section = paper6Section4 ; status = assigned }
  ∷ record { section = paper6Section5 ; status = assigned }
  ∷ record { section = paper6Section6 ; status = assigned }
  ∷ []

paper8Sections1to4Assigned :
  List Paper8SectionLine
paper8Sections1to4Assigned =
  record { section = paper8Section1 ; status = assigned }
  ∷ record { section = paper8Section2 ; status = assigned }
  ∷ record { section = paper8Section3 ; status = assigned }
  ∷ record { section = paper8Section4 ; status = assigned }
  ∷ []

paper8Sections5to6Complete :
  List Paper8SectionLine
paper8Sections5to6Complete =
  record { section = paper8Section5 ; status = complete }
  ∷ record { section = paper8Section6 ; status = complete }
  ∷ []

data FinalPaperSectionTriagePromotion : Set where

finalPaperSectionTriagePromotionImpossibleHere :
  FinalPaperSectionTriagePromotion →
  ⊥
finalPaperSectionTriagePromotionImpossibleHere ()

finalPaperSectionTriageStatement : String
finalPaperSectionTriageStatement =
  "Paper 6 reaches internal-review readiness only after Sections 4-6; Paper 8 bottleneck is Section 3 conductor exhaustion table; Paper 6 Sections 1-3 complete and 4-6 assigned; Paper 8 Sections 1-4 assigned and 5-6 complete."

record FinalPaperSectionTriageReceipt : Setω where
  field
    paper6ReadyForInternalReview :
      Paper6ReviewGate

    paper6ReadyForInternalReviewIsAfterSections4to6 :
      paper6ReadyForInternalReview ≡ afterSections4to6

    paper8BottleneckSection :
      Paper8BottleneckSection

    paper8BottleneckSectionIsSection3ConductorExhaustionTable :
      paper8BottleneckSection ≡ section3ConductorExhaustionTable

    paper8BottleneckSectionRecordedAs :
      String

    paper8BottleneckSectionRecordedAsCanonical :
      paper8BottleneckSectionRecordedAs ≡ paper8BottleneckSectionLabel

    paper6CompleteSections :
      List Paper6SectionLine

    paper6CompleteSectionsAre1to3 :
      paper6CompleteSections ≡ paper6Sections1to3Complete

    paper6AssignedSections :
      List Paper6SectionLine

    paper6AssignedSectionsAre4to6 :
      paper6AssignedSections ≡ paper6Sections4to6Assigned

    paper8AssignedSections :
      List Paper8SectionLine

    paper8AssignedSectionsAre1to4 :
      paper8AssignedSections ≡ paper8Sections1to4Assigned

    paper8CompleteSections :
      List Paper8SectionLine

    paper8CompleteSectionsAre5to6 :
      paper8CompleteSections ≡ paper8Sections5to6Complete

    section3ConductorExhaustionTableMostImportantCompletionTask :
      Bool

    section3ConductorExhaustionTableMostImportantCompletionTaskIsTrue :
      section3ConductorExhaustionTableMostImportantCompletionTask ≡ true

    governanceOnly :
      Bool

    governanceOnlyIsTrue :
      governanceOnly ≡ true

    paper6PromotionFlag :
      Bool

    paper6PromotionFlagIsFalse :
      paper6PromotionFlag ≡ false

    paper8PromotionFlag :
      Bool

    paper8PromotionFlagIsFalse :
      paper8PromotionFlag ≡ false

    internalReviewPromoted :
      Bool

    internalReviewPromotedIsFalse :
      internalReviewPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List FinalPaperSectionTriagePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ finalPaperSectionTriageStatement

    receiptBoundary :
      List String

open FinalPaperSectionTriageReceipt public

canonicalFinalPaperSectionTriageReceipt :
  FinalPaperSectionTriageReceipt
canonicalFinalPaperSectionTriageReceipt =
  record
    { paper6ReadyForInternalReview =
        afterSections4to6
    ; paper6ReadyForInternalReviewIsAfterSections4to6 =
        refl
    ; paper8BottleneckSection =
        section3ConductorExhaustionTable
    ; paper8BottleneckSectionIsSection3ConductorExhaustionTable =
        refl
    ; paper8BottleneckSectionRecordedAs =
        paper8BottleneckSectionLabel
    ; paper8BottleneckSectionRecordedAsCanonical =
        refl
    ; paper6CompleteSections =
        paper6Sections1to3Complete
    ; paper6CompleteSectionsAre1to3 =
        refl
    ; paper6AssignedSections =
        paper6Sections4to6Assigned
    ; paper6AssignedSectionsAre4to6 =
        refl
    ; paper8AssignedSections =
        paper8Sections1to4Assigned
    ; paper8AssignedSectionsAre1to4 =
        refl
    ; paper8CompleteSections =
        paper8Sections5to6Complete
    ; paper8CompleteSectionsAre5to6 =
        refl
    ; section3ConductorExhaustionTableMostImportantCompletionTask =
        true
    ; section3ConductorExhaustionTableMostImportantCompletionTaskIsTrue =
        refl
    ; governanceOnly =
        true
    ; governanceOnlyIsTrue =
        refl
    ; paper6PromotionFlag =
        false
    ; paper6PromotionFlagIsFalse =
        refl
    ; paper8PromotionFlag =
        false
    ; paper8PromotionFlagIsFalse =
        refl
    ; internalReviewPromoted =
        false
    ; internalReviewPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        finalPaperSectionTriageStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Manager C task C4 records paper-section triage only"
        ∷ "paper6ReadyForInternalReview is afterSections4to6"
        ∷ "paper8BottleneckSection is 3 exhaustion table"
        ∷ "Paper 6 Sections 1-3 are complete and Sections 4-6 are assigned"
        ∷ "Paper 8 Sections 1-4 are assigned and Sections 5-6 are complete"
        ∷ "Section 3 conductor exhaustion table is the most important completion task"
        ∷ "No Paper 6, Paper 8, internal-review, or terminal promotion flag is raised"
        ∷ []
    }

finalPaperSectionTriageKeepsPaper6PromotionFalse :
  paper6PromotionFlag canonicalFinalPaperSectionTriageReceipt ≡ false
finalPaperSectionTriageKeepsPaper6PromotionFalse =
  refl

finalPaperSectionTriageKeepsPaper8PromotionFalse :
  paper8PromotionFlag canonicalFinalPaperSectionTriageReceipt ≡ false
finalPaperSectionTriageKeepsPaper8PromotionFalse =
  refl

finalPaperSectionTriageKeepsTerminalFalse :
  terminalClaimPromoted canonicalFinalPaperSectionTriageReceipt ≡ false
finalPaperSectionTriageKeepsTerminalFalse =
  refl

finalPaperSectionTriageNoPromotion :
  FinalPaperSectionTriagePromotion →
  ⊥
finalPaperSectionTriageNoPromotion =
  finalPaperSectionTriagePromotionImpossibleHere
