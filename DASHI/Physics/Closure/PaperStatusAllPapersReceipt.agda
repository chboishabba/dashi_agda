module DASHI.Physics.Closure.PaperStatusAllPapersReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayRoadmapAssignmentPrep as Prep
import DASHI.Physics.Closure.Deg23SummaryAndFutureDirectionReceipt as Deg23

data PaperFrontierStatus : Set where
  paper1FormalMethodsStatus :
    PaperFrontierStatus

  paper2GRGeometryStatus :
    PaperFrontierStatus

  paper3QFTGaugeStatus :
    PaperFrontierStatus

  paper4PhysicalHilbertStatus :
    PaperFrontierStatus

  paper5MatterGaugeStatus :
    PaperFrontierStatus

  paper6DiagnosticLetterReady :
    PaperFrontierStatus

  paper7InternalOnly :
    PaperFrontierStatus

  paper8ConjecturePaperReady :
    PaperFrontierStatus

  clayYMPaperNotReady :
    PaperFrontierStatus

  clayNSPaperNotReady :
    PaperFrontierStatus

canonicalPaperFrontierStatuses : List PaperFrontierStatus
canonicalPaperFrontierStatuses =
  paper1FormalMethodsStatus
  ∷ paper2GRGeometryStatus
  ∷ paper3QFTGaugeStatus
  ∷ paper4PhysicalHilbertStatus
  ∷ paper5MatterGaugeStatus
  ∷ paper6DiagnosticLetterReady
  ∷ paper7InternalOnly
  ∷ paper8ConjecturePaperReady
  ∷ clayYMPaperNotReady
  ∷ clayNSPaperNotReady
  ∷ []

data PaperStatusPromotion : Set where

paperStatusPromotionImpossibleHere :
  PaperStatusPromotion →
  ⊥
paperStatusPromotionImpossibleHere ()

record PaperStatusAllPapersReceipt : Setω where
  field
    clayPrep :
      Prep.ClayRoadmapAssignmentPrep

    clayPrepKeepsYMFalse :
      Prep.clayYangMillsPromoted clayPrep ≡ false

    clayPrepKeepsNSFalse :
      Prep.clayNavierStokesPromoted clayPrep ≡ false

    deg23Summary :
      Deg23.Deg23SummaryAndFutureDirectionReceipt

    deg23ResidualStillFalse :
      Deg23.deg23ResidualExplained deg23Summary ≡ false

    trackedPaperCount :
      Nat

    trackedPaperCountIsEight :
      trackedPaperCount ≡ 8

    papersOneToFiveStatusRecorded :
      Bool

    papersOneToFiveStatusRecordedIsTrue :
      papersOneToFiveStatusRecorded ≡ true

    paper6SubmissionReadyAsDiagnostic :
      Bool

    paper6SubmissionReadyAsDiagnosticIsTrue :
      paper6SubmissionReadyAsDiagnostic ≡ true

    paper8SubmissionReadyAsConjecture :
      Bool

    paper8SubmissionReadyAsConjectureIsTrue :
      paper8SubmissionReadyAsConjecture ≡ true

    paper7InternalOnlyFlag :
      Bool

    paper7InternalOnlyFlagIsTrue :
      paper7InternalOnlyFlag ≡ true

    clayYMSubmissionReady :
      Bool

    clayYMSubmissionReadyIsFalse :
      clayYMSubmissionReady ≡ false

    clayNSSubmissionReady :
      Bool

    clayNSSubmissionReadyIsFalse :
      clayNSSubmissionReady ≡ false

    statuses :
      List PaperFrontierStatus

    statusesAreCanonical :
      statuses ≡ canonicalPaperFrontierStatuses

    allPapersStatusRecorded :
      Bool

    allPapersStatusRecordedIsTrue :
      allPapersStatusRecorded ≡ true

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    exactPhysicalCKMPromoted :
      Bool

    exactPhysicalCKMPromotedIsFalse :
      exactPhysicalCKMPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotionFlags :
      List PaperStatusPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open PaperStatusAllPapersReceipt public

canonicalPaperStatusAllPapersReceipt :
  PaperStatusAllPapersReceipt
canonicalPaperStatusAllPapersReceipt =
  record
    { clayPrep =
        Prep.canonicalClayRoadmapAssignmentPrep
    ; clayPrepKeepsYMFalse =
        refl
    ; clayPrepKeepsNSFalse =
        refl
    ; deg23Summary =
        Deg23.canonicalDeg23SummaryAndFutureDirectionReceipt
    ; deg23ResidualStillFalse =
        refl
    ; trackedPaperCount =
        8
    ; trackedPaperCountIsEight =
        refl
    ; papersOneToFiveStatusRecorded =
        true
    ; papersOneToFiveStatusRecordedIsTrue =
        refl
    ; paper6SubmissionReadyAsDiagnostic =
        true
    ; paper6SubmissionReadyAsDiagnosticIsTrue =
        refl
    ; paper8SubmissionReadyAsConjecture =
        true
    ; paper8SubmissionReadyAsConjectureIsTrue =
        refl
    ; paper7InternalOnlyFlag =
        true
    ; paper7InternalOnlyFlagIsTrue =
        refl
    ; clayYMSubmissionReady =
        false
    ; clayYMSubmissionReadyIsFalse =
        refl
    ; clayNSSubmissionReady =
        false
    ; clayNSSubmissionReadyIsFalse =
        refl
    ; statuses =
        canonicalPaperFrontierStatuses
    ; statusesAreCanonical =
        refl
    ; allPapersStatusRecorded =
        true
    ; allPapersStatusRecordedIsTrue =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; exactPhysicalCKMPromoted =
        false
    ; exactPhysicalCKMPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotionFlags =
        [] {A = PaperStatusPromotion}
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records Papers 1-8 as a documentation/status snapshot."
        ∷ "Paper 6 diagnostic letter true; Paper 8 conjecture true; Paper 7 internal only."
        ∷ "Clay YM and Clay NS papers are not submission-ready proof papers."
        ∷ "No exact physical CKM, exact Standard Model, Clay, or terminal promotion is asserted."
        ∷ []
    }

paperStatusAllPapersKeepsTerminalFalse :
  terminalClaimPromoted canonicalPaperStatusAllPapersReceipt ≡ false
paperStatusAllPapersKeepsTerminalFalse =
  refl

paperStatusAllPapersKeepsExactCKMFalse :
  exactPhysicalCKMPromoted canonicalPaperStatusAllPapersReceipt ≡ false
paperStatusAllPapersKeepsExactCKMFalse =
  refl
