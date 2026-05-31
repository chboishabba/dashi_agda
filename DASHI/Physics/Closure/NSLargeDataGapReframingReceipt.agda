module DASHI.Physics.Closure.NSLargeDataGapReframingReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.NSLargeDataContractionInputRequest
  using (nsLargeDataContractionInputRequestStatement)
open import DASHI.Physics.Closure.NSFlowPreservationBoundReceipt
  using
    ( NSFlowPreservationBoundReceipt
    ; canonicalNSFlowPreservationBoundReceipt
    )
open import DASHI.Physics.Closure.NSH118ThresholdReceipt
  using
    ( NSH118ThresholdReceipt
    ; canonicalNSH118ThresholdReceipt
    )
open import DASHI.Physics.Closure.AdjacentOnlyVortexStretchingReceipt
  using
    ( AdjacentOnlyVortexStretchingReceipt
    ; canonicalAdjacentOnlyVortexStretchingReceipt
    )

------------------------------------------------------------------------
-- Navier-Stokes large-data gap reframing receipt.
--
-- This receipt corrects the earlier NSLargeDataContractionInputRequest
-- framing.  The prior request framed the missing large-data step as a
-- large-data contraction input.  That is the wrong object: contraction
-- arguments are small-data/local-radius mechanisms only.  The corrected
-- gap is a global H^{11/8} energy bound for carrier-structured initial
-- data of arbitrary norm, with no blow-up of the H^{11/8} bound.
--
-- Candidate mechanism only: cross-lane flow-preservation suppression plus
-- within-lane adjacent-only dissipation dominance would combine to give
-- d/dt E <= 0 for every E > 0.  This receipt does not prove that
-- inequality and makes no Clay/global terminal promotion.

data NSLargeDataGapReframingStatus : Set where
  previousContractionInputRequestRecorded :
    NSLargeDataGapReframingStatus

  previousLargeDataContractionFramingWrong :
    NSLargeDataGapReframingStatus

  contractionArgumentsSmallDataOnly :
    NSLargeDataGapReframingStatus

  correctGapGlobalH118BoundForArbitraryNorm :
    NSLargeDataGapReframingStatus

  adjacentOnlyPlusFlowPreservationMechanismCandidate :
    NSLargeDataGapReframingStatus

  energyMonotonicityCandidateOnly :
    NSLargeDataGapReframingStatus

  noClayOrGlobalTerminalPromotion :
    NSLargeDataGapReframingStatus

canonicalNSLargeDataGapReframingStatus :
  List NSLargeDataGapReframingStatus
canonicalNSLargeDataGapReframingStatus =
  previousContractionInputRequestRecorded
  ∷ previousLargeDataContractionFramingWrong
  ∷ contractionArgumentsSmallDataOnly
  ∷ correctGapGlobalH118BoundForArbitraryNorm
  ∷ adjacentOnlyPlusFlowPreservationMechanismCandidate
  ∷ energyMonotonicityCandidateOnly
  ∷ noClayOrGlobalTerminalPromotion
  ∷ []

data NSLargeDataCorrectApproach : Set where
  globalEnergyBound :
    NSLargeDataCorrectApproach

data NSLargeDataMechanismCandidate : Set where
  adjacentOnlyPlusFlowPreservation :
    NSLargeDataMechanismCandidate

data NSLargeDataGapReframingPromotion : Set where

nsLargeDataGapReframingPromotionImpossibleHere :
  NSLargeDataGapReframingPromotion →
  ⊥
nsLargeDataGapReframingPromotionImpossibleHere ()

previousContractionFramingStatement : String
previousContractionFramingStatement =
  "Previous NSLargeDataContractionInputRequest framed the large-data H^{11/8} gap as a large-data contraction input; this receipt records that framing as wrong because contraction arguments are small-data only."

correctLargeDataGapStatement : String
correctLargeDataGapStatement =
  "Correct NS large-data gap: for carrier-structured u_0 in H^{11/8} of arbitrary norm, prove a global H^{11/8} bound that does not blow up."

largeDataGapMechanismCandidateStatement : String
largeDataGapMechanismCandidateStatement =
  "Mechanism candidate: cross-lane flow-preservation suppression plus within-lane adjacent-only dissipation dominance combine to give d/dt E <= 0 for all E > 0."

nsLargeDataGapReframingStatement : String
nsLargeDataGapReframingStatement =
  "NS large-data gap reframed: the prior contraction-input framing was wrong, since contraction is small-data only; the correct target is a non-blow-up global H^{11/8} energy bound for carrier-structured arbitrary-norm data, with adjacentOnlyPlusFlowPreservation recorded only as a mechanism candidate and no Clay/global terminal promotion."

record NSLargeDataGapReframingReceipt : Setω where
  field
    status :
      List NSLargeDataGapReframingStatus

    statusIsCanonical :
      status ≡ canonicalNSLargeDataGapReframingStatus

    priorRequestImported :
      Bool

    priorRequestImportedIsTrue :
      priorRequestImported ≡ true

    priorRequestStatement :
      String

    priorRequestStatementIsCanonical :
      priorRequestStatement ≡ nsLargeDataContractionInputRequestStatement

    previousFraming :
      String

    previousFramingIsCanonical :
      previousFraming ≡ previousContractionFramingStatement

    nsLargeDataGapReframed :
      Bool

    nsLargeDataGapReframedIsTrue :
      nsLargeDataGapReframed ≡ true

    previousNSLargeDataContractionInputRequestFramedGapAsLargeDataContraction :
      Bool

    previousNSLargeDataContractionInputRequestFramedGapAsLargeDataContractionIsTrue :
      previousNSLargeDataContractionInputRequestFramedGapAsLargeDataContraction
      ≡
      true

    previousLargeDataContractionFramingIsWrong :
      Bool

    previousLargeDataContractionFramingIsWrongIsTrue :
      previousLargeDataContractionFramingIsWrong ≡ true

    contractionApproachIsSmallDataOnly :
      Bool

    contractionApproachIsSmallDataOnlyIsTrue :
      contractionApproachIsSmallDataOnly ≡ true

    correctApproach :
      NSLargeDataCorrectApproach

    correctApproachIsGlobalEnergyBound :
      correctApproach ≡ globalEnergyBound

    correctGap :
      String

    correctGapIsCanonical :
      correctGap ≡ correctLargeDataGapStatement

    carrierStructuredU0Recorded :
      Bool

    carrierStructuredU0RecordedIsTrue :
      carrierStructuredU0Recorded ≡ true

    hElevenEighthsInitialDataRecorded :
      Bool

    hElevenEighthsInitialDataRecordedIsTrue :
      hElevenEighthsInitialDataRecorded ≡ true

    arbitraryNormRecorded :
      Bool

    arbitraryNormRecordedIsTrue :
      arbitraryNormRecorded ≡ true

    globalH118BoundTargetRecorded :
      Bool

    globalH118BoundTargetRecordedIsTrue :
      globalH118BoundTargetRecorded ≡ true

    nonBlowUpBoundTargetRecorded :
      Bool

    nonBlowUpBoundTargetRecordedIsTrue :
      nonBlowUpBoundTargetRecorded ≡ true

    mechanismCandidate :
      NSLargeDataMechanismCandidate

    mechanismCandidateIsAdjacentOnlyPlusFlowPreservation :
      mechanismCandidate ≡ adjacentOnlyPlusFlowPreservation

    mechanismCandidateStatement :
      String

    mechanismCandidateStatementIsCanonical :
      mechanismCandidateStatement ≡ largeDataGapMechanismCandidateStatement

    flowPreservationReceipt :
      NSFlowPreservationBoundReceipt

    flowPreservationReceiptReferenced :
      Bool

    flowPreservationReceiptReferencedIsTrue :
      flowPreservationReceiptReferenced ≡ true

    adjacentOnlyReceipt :
      AdjacentOnlyVortexStretchingReceipt

    adjacentOnlyReceiptReferenced :
      Bool

    adjacentOnlyReceiptReferencedIsTrue :
      adjacentOnlyReceiptReferenced ≡ true

    h118ThresholdReceipt :
      NSH118ThresholdReceipt

    h118ThresholdReceiptReferenced :
      Bool

    h118ThresholdReceiptReferencedIsTrue :
      h118ThresholdReceiptReferenced ≡ true

    crossLaneFlowPreservationSuppressionRecorded :
      Bool

    crossLaneFlowPreservationSuppressionRecordedIsTrue :
      crossLaneFlowPreservationSuppressionRecorded ≡ true

    withinLaneAdjacentOnlyDissipationDominanceRecorded :
      Bool

    withinLaneAdjacentOnlyDissipationDominanceRecordedIsTrue :
      withinLaneAdjacentOnlyDissipationDominanceRecorded ≡ true

    energyInequalityTarget :
      String

    energyInequalityTargetIsCanonical :
      energyInequalityTarget ≡ "d/dt E <= 0 for all E > 0"

    energyInequalityProved :
      Bool

    energyInequalityProvedIsFalse :
      energyInequalityProved ≡ false

    largeDataContractionTheoremConstructed :
      Bool

    largeDataContractionTheoremConstructedIsFalse :
      largeDataContractionTheoremConstructed ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalPromotionPromoted :
      Bool

    terminalPromotionPromotedIsFalse :
      terminalPromotionPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsLargeDataGapReframingStatement

    promotionFlags :
      List NSLargeDataGapReframingPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSLargeDataGapReframingReceipt public

canonicalNSLargeDataGapReframingReceipt :
  NSLargeDataGapReframingReceipt
canonicalNSLargeDataGapReframingReceipt =
  record
    { status =
        canonicalNSLargeDataGapReframingStatus
    ; statusIsCanonical =
        refl
    ; priorRequestImported =
        true
    ; priorRequestImportedIsTrue =
        refl
    ; priorRequestStatement =
        nsLargeDataContractionInputRequestStatement
    ; priorRequestStatementIsCanonical =
        refl
    ; previousFraming =
        previousContractionFramingStatement
    ; previousFramingIsCanonical =
        refl
    ; nsLargeDataGapReframed =
        true
    ; nsLargeDataGapReframedIsTrue =
        refl
    ; previousNSLargeDataContractionInputRequestFramedGapAsLargeDataContraction =
        true
    ; previousNSLargeDataContractionInputRequestFramedGapAsLargeDataContractionIsTrue =
        refl
    ; previousLargeDataContractionFramingIsWrong =
        true
    ; previousLargeDataContractionFramingIsWrongIsTrue =
        refl
    ; contractionApproachIsSmallDataOnly =
        true
    ; contractionApproachIsSmallDataOnlyIsTrue =
        refl
    ; correctApproach =
        globalEnergyBound
    ; correctApproachIsGlobalEnergyBound =
        refl
    ; correctGap =
        correctLargeDataGapStatement
    ; correctGapIsCanonical =
        refl
    ; carrierStructuredU0Recorded =
        true
    ; carrierStructuredU0RecordedIsTrue =
        refl
    ; hElevenEighthsInitialDataRecorded =
        true
    ; hElevenEighthsInitialDataRecordedIsTrue =
        refl
    ; arbitraryNormRecorded =
        true
    ; arbitraryNormRecordedIsTrue =
        refl
    ; globalH118BoundTargetRecorded =
        true
    ; globalH118BoundTargetRecordedIsTrue =
        refl
    ; nonBlowUpBoundTargetRecorded =
        true
    ; nonBlowUpBoundTargetRecordedIsTrue =
        refl
    ; mechanismCandidate =
        adjacentOnlyPlusFlowPreservation
    ; mechanismCandidateIsAdjacentOnlyPlusFlowPreservation =
        refl
    ; mechanismCandidateStatement =
        largeDataGapMechanismCandidateStatement
    ; mechanismCandidateStatementIsCanonical =
        refl
    ; flowPreservationReceipt =
        canonicalNSFlowPreservationBoundReceipt
    ; flowPreservationReceiptReferenced =
        true
    ; flowPreservationReceiptReferencedIsTrue =
        refl
    ; adjacentOnlyReceipt =
        canonicalAdjacentOnlyVortexStretchingReceipt
    ; adjacentOnlyReceiptReferenced =
        true
    ; adjacentOnlyReceiptReferencedIsTrue =
        refl
    ; h118ThresholdReceipt =
        canonicalNSH118ThresholdReceipt
    ; h118ThresholdReceiptReferenced =
        true
    ; h118ThresholdReceiptReferencedIsTrue =
        refl
    ; crossLaneFlowPreservationSuppressionRecorded =
        true
    ; crossLaneFlowPreservationSuppressionRecordedIsTrue =
        refl
    ; withinLaneAdjacentOnlyDissipationDominanceRecorded =
        true
    ; withinLaneAdjacentOnlyDissipationDominanceRecordedIsTrue =
        refl
    ; energyInequalityTarget =
        "d/dt E <= 0 for all E > 0"
    ; energyInequalityTargetIsCanonical =
        refl
    ; energyInequalityProved =
        false
    ; energyInequalityProvedIsFalse =
        refl
    ; largeDataContractionTheoremConstructed =
        false
    ; largeDataContractionTheoremConstructedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionPromoted =
        false
    ; terminalPromotionPromotedIsFalse =
        refl
    ; statement =
        nsLargeDataGapReframingStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "nsLargeDataGapReframed = true"
        ∷ "Previous NSLargeDataContractionInputRequest framed the gap as large-data contraction"
        ∷ "That framing is wrong: contractionApproachIsSmallDataOnly = true"
        ∷ "correctApproach = globalEnergyBound"
        ∷ "Correct gap: carrier-structured u_0 in H^{11/8}, arbitrary norm, global H^{11/8} bound without blow-up"
        ∷ "mechanismCandidate = adjacentOnlyPlusFlowPreservation"
        ∷ "Candidate target: d/dt E <= 0 for all E > 0"
        ∷ "Energy inequality is not proved in this receipt"
        ∷ "No Clay/global terminal promotion"
        ∷ []
    }

nsLargeDataGapReframedIsSet :
  nsLargeDataGapReframed canonicalNSLargeDataGapReframingReceipt
  ≡
  true
nsLargeDataGapReframedIsSet =
  refl

nsLargeDataContractionApproachSmallDataOnly :
  contractionApproachIsSmallDataOnly canonicalNSLargeDataGapReframingReceipt
  ≡
  true
nsLargeDataContractionApproachSmallDataOnly =
  refl

nsLargeDataCorrectApproachIsGlobalEnergyBound :
  correctApproach canonicalNSLargeDataGapReframingReceipt
  ≡
  globalEnergyBound
nsLargeDataCorrectApproachIsGlobalEnergyBound =
  refl

nsLargeDataMechanismCandidateIsAdjacentOnlyPlusFlowPreservation :
  mechanismCandidate canonicalNSLargeDataGapReframingReceipt
  ≡
  adjacentOnlyPlusFlowPreservation
nsLargeDataMechanismCandidateIsAdjacentOnlyPlusFlowPreservation =
  refl

nsLargeDataEnergyInequalityNotProvedHere :
  energyInequalityProved canonicalNSLargeDataGapReframingReceipt
  ≡
  false
nsLargeDataEnergyInequalityNotProvedHere =
  refl

nsLargeDataGapReframingDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSLargeDataGapReframingReceipt
  ≡
  false
nsLargeDataGapReframingDoesNotPromoteGlobalRegularity =
  refl

nsLargeDataGapReframingDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSLargeDataGapReframingReceipt
  ≡
  false
nsLargeDataGapReframingDoesNotPromoteClay =
  refl

nsLargeDataGapReframingNoTerminalPromotion :
  terminalPromotionPromoted canonicalNSLargeDataGapReframingReceipt
  ≡
  false
nsLargeDataGapReframingNoTerminalPromotion =
  refl

nsLargeDataGapReframingNoPromotion :
  NSLargeDataGapReframingPromotion →
  ⊥
nsLargeDataGapReframingNoPromotion =
  nsLargeDataGapReframingPromotionImpossibleHere
