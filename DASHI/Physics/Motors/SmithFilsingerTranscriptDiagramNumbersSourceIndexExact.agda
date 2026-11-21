module DASHI.Physics.Motors.SmithFilsingerTranscriptDiagramNumbersSourceIndexExact where

-- Source-first corrected reading of user's earlier transcript + the
-- user-supplied Darrer/Kelly 147-page Smith diagram audit. The original
-- photos/PDF are not re-attached here. These numbers ALREADY EXIST in source
-- transcriptions, but belong to DIFFERENT physical occasions and authority
-- strata. NO historical source-to-pin continuity or synchronized v*i result.
--
-- Canonical machine-readable audit:
-- Artifacts/smith-filsinger/source_indexed_transcript_diagram_values_20261122.json

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.SmithFilsingerReflectedPortBidiExact as Reel
import DASHI.Physics.Motors.DonSmithOriginalPDFDiagramBidiExact as Smith

data Contradiction : Set where

data SourceOccasion : Set where
  zvsShuntReel : SourceOccasion             -- DfiqPnkPnP5
  earlyVoltageAndAudio : SourceOccasion     -- ~15V/~6-7.3W/~1500V, time unpaired
  earthThreeElectrodeReel : SourceOccasion  -- Dfi1D7CPzyM
  whiteCapEarthNarration : SourceOccasion   -- exact occasion unresolved
  midpointSparkTranscript : SourceOccasion -- Dfu9Jseviz9 candidate attribution
  smithKellyDarrerPDF : SourceOccasion       -- historical/editorial compilation

data EvidenceTier : Set where
  narratedComponent : EvidenceTier
  narratedAlternative : EvidenceTier
  reportedMeterDisplay : EvidenceTier
  olderObservationUnpaired : EvidenceTier
  userTranscribedProposal : EvidenceTier
  sourceCompiledDiagram : EvidenceTier

data QuantityUnit : Set where
  microfarad : QuantityUnit
  megohm : QuantityUnit
  volt : QuantityUnit
  tenthVolt : QuantityUnit
  tenthWatt : QuantityUnit
  hertz : QuantityUnit
  turns : QuantityUnit
  degrees : QuantityUnit
  count : QuantityUnit
  inch hundredthInch hundredthTurn nanofarad watt : QuantityUnit
  pdfPage : QuantityUnit

-- Unlike a generic Datum {occasion:String}, each source item is indexed
-- BY its original occasion and cannot be silently used as a different
-- physical experiment. Source identity != measured time-domain pin identity.
data SourceNumber : SourceOccasion → Set where
  zvsCapApproximately33TenthsMicrofarad : SourceNumber zvsShuntReel
  zvsOneMegohm zvsTwoMegohm zvsFourMegohm : SourceNumber zvsShuntReel
  olderFifteenVolt olderPowerSixtyTenths olderPowerSeventyThreeTenths :
    SourceNumber earlyVoltageAndAudio
  olderFifteenHundredVolt olderAcoustic7800Hertz :
    SourceNumber earlyVoltageAndAudio
  earthThreeContacts : SourceNumber earthThreeElectrodeReel
  earthDisplayThirtyEightTenthsVolt : SourceNumber earthThreeElectrodeReel
  earthDisplayFourTenthsWatt : SourceNumber earthThreeElectrodeReel
  earthTwoCapsDisplayFortyEightVolt : SourceNumber earthThreeElectrodeReel
  whiteCap333HundredthsMicrofarad : SourceNumber whiteCapEarthNarration
  midpointFourDiodes : SourceNumber midpointSparkTranscript
  midpointCapTwentyThousandVolt midpointCapOneMicrofarad :
    SourceNumber midpointSparkTranscript
  midpointAlternateTenThousandVolt midpointAlternateTwoMicrofarad :
    SourceNumber midpointSparkTranscript
  midpointApproxFourThousandVolt : SourceNumber midpointSparkTranscript
  smithFigureTenPage smithFigureElevenPage smithFigureFortyPage :
    SourceNumber smithKellyDarrerPDF
  smithSplitSecondaryFirstSeventeen smithSplitSecondarySecondSeventeen :
    SourceNumber smithKellyDarrerPDF
  smithIllustrativeTwoHundredFortyDegree :
    SourceNumber smithKellyDarrerPDF
  smithIllustrativeL2HalfOneHundredSixtyInch :
    SourceNumber smithKellyDarrerPDF
  smithIllustrativeL1FortyInch :
    SourceNumber smithKellyDarrerPDF
  smithIllustrativeL1TwoHundredTwentyFiveHundredthInch :
    SourceNumber smithKellyDarrerPDF
  smithApproxL1FiveHundredSixtyFiveHundredthTurns :
    SourceNumber smithKellyDarrerPDF
  smithOptionalParallelFortySevenNanofarad :
    SourceNumber smithKellyDarrerPDF
  smithClaimedTwoThousandVolt :
    SourceNumber smithKellyDarrerPDF
  smithClaimedSixThousandWatt :
    SourceNumber smithKellyDarrerPDF

numberUnit : ∀ {o} → SourceNumber o → QuantityUnit
numberUnit zvsCapApproximately33TenthsMicrofarad = microfarad
numberUnit zvsOneMegohm = megohm
numberUnit zvsTwoMegohm = megohm
numberUnit zvsFourMegohm = megohm
numberUnit olderFifteenVolt = volt
numberUnit olderPowerSixtyTenths = tenthWatt
numberUnit olderPowerSeventyThreeTenths = tenthWatt
numberUnit olderFifteenHundredVolt = volt
numberUnit olderAcoustic7800Hertz = hertz
numberUnit earthThreeContacts = count
numberUnit earthDisplayThirtyEightTenthsVolt = tenthVolt
numberUnit earthDisplayFourTenthsWatt = tenthWatt
numberUnit earthTwoCapsDisplayFortyEightVolt = volt
numberUnit whiteCap333HundredthsMicrofarad = microfarad
numberUnit midpointFourDiodes = count
numberUnit midpointCapTwentyThousandVolt = volt
numberUnit midpointCapOneMicrofarad = microfarad
numberUnit midpointAlternateTenThousandVolt = volt
numberUnit midpointAlternateTwoMicrofarad = microfarad
numberUnit midpointApproxFourThousandVolt = volt
numberUnit smithFigureTenPage = pdfPage
numberUnit smithFigureElevenPage = pdfPage
numberUnit smithFigureFortyPage = pdfPage
numberUnit smithSplitSecondaryFirstSeventeen = turns
numberUnit smithSplitSecondarySecondSeventeen = turns
numberUnit smithIllustrativeTwoHundredFortyDegree = degrees
numberUnit smithIllustrativeL2HalfOneHundredSixtyInch = inch
numberUnit smithIllustrativeL1FortyInch = inch
numberUnit smithIllustrativeL1TwoHundredTwentyFiveHundredthInch = hundredthInch
numberUnit smithApproxL1FiveHundredSixtyFiveHundredthTurns = hundredthTurn
numberUnit smithOptionalParallelFortySevenNanofarad = nanofarad
numberUnit smithClaimedTwoThousandVolt = volt
numberUnit smithClaimedSixThousandWatt = watt

-- Rational interpretation belongs to a SEPARATE measured unit/convention.
-- A value of 38 in tenthVolt is not 38V; 33 in tenth-µF != 333 in
-- hundredth-µF; and any rated 20kV is not an observed 20kV terminal.
numberMagnitude : ∀ {o} → SourceNumber o → Nat
numberMagnitude zvsCapApproximately33TenthsMicrofarad = 33
numberMagnitude zvsOneMegohm = 1
numberMagnitude zvsTwoMegohm = 2
numberMagnitude zvsFourMegohm = 4
numberMagnitude olderFifteenVolt = 15
numberMagnitude olderPowerSixtyTenths = 60
numberMagnitude olderPowerSeventyThreeTenths = 73
numberMagnitude olderFifteenHundredVolt = 1500
numberMagnitude olderAcoustic7800Hertz = 7800
numberMagnitude earthThreeContacts = 3
numberMagnitude earthDisplayThirtyEightTenthsVolt = 38
numberMagnitude earthDisplayFourTenthsWatt = 4
numberMagnitude earthTwoCapsDisplayFortyEightVolt = 48
numberMagnitude whiteCap333HundredthsMicrofarad = 333
numberMagnitude midpointFourDiodes = 4
numberMagnitude midpointCapTwentyThousandVolt = 20000
numberMagnitude midpointCapOneMicrofarad = 1
numberMagnitude midpointAlternateTenThousandVolt = 10000
numberMagnitude midpointAlternateTwoMicrofarad = 2
numberMagnitude midpointApproxFourThousandVolt = 4000
numberMagnitude smithFigureTenPage = 28
numberMagnitude smithFigureElevenPage = 29
numberMagnitude smithFigureFortyPage = 65
numberMagnitude smithSplitSecondaryFirstSeventeen = 17
numberMagnitude smithSplitSecondarySecondSeventeen = 17
numberMagnitude smithIllustrativeTwoHundredFortyDegree = 240
numberMagnitude smithIllustrativeL2HalfOneHundredSixtyInch = 160
numberMagnitude smithIllustrativeL1FortyInch = 40
numberMagnitude smithIllustrativeL1TwoHundredTwentyFiveHundredthInch = 225
numberMagnitude smithApproxL1FiveHundredSixtyFiveHundredthTurns = 565
numberMagnitude smithOptionalParallelFortySevenNanofarad = 47
numberMagnitude smithClaimedTwoThousandVolt = 2000
numberMagnitude smithClaimedSixThousandWatt = 6000


sourceStatus : ∀ {o} → SourceNumber o → EvidenceTier
sourceStatus zvsCapApproximately33TenthsMicrofarad = narratedComponent
sourceStatus zvsOneMegohm = narratedComponent
sourceStatus zvsTwoMegohm = narratedAlternative
sourceStatus zvsFourMegohm = narratedAlternative
sourceStatus olderFifteenVolt = olderObservationUnpaired
sourceStatus olderPowerSixtyTenths = olderObservationUnpaired
sourceStatus olderPowerSeventyThreeTenths = olderObservationUnpaired
sourceStatus olderFifteenHundredVolt = olderObservationUnpaired
sourceStatus olderAcoustic7800Hertz = olderObservationUnpaired
sourceStatus earthThreeContacts = narratedComponent
sourceStatus earthDisplayThirtyEightTenthsVolt = reportedMeterDisplay
sourceStatus earthDisplayFourTenthsWatt = reportedMeterDisplay
sourceStatus earthTwoCapsDisplayFortyEightVolt = reportedMeterDisplay
sourceStatus whiteCap333HundredthsMicrofarad = narratedComponent
sourceStatus midpointFourDiodes = userTranscribedProposal
sourceStatus midpointCapTwentyThousandVolt = userTranscribedProposal
sourceStatus midpointCapOneMicrofarad = userTranscribedProposal
sourceStatus midpointAlternateTenThousandVolt = userTranscribedProposal
sourceStatus midpointAlternateTwoMicrofarad = userTranscribedProposal
sourceStatus midpointApproxFourThousandVolt = userTranscribedProposal
sourceStatus smithFigureTenPage = sourceCompiledDiagram
sourceStatus smithFigureElevenPage = sourceCompiledDiagram
sourceStatus smithFigureFortyPage = sourceCompiledDiagram
sourceStatus smithSplitSecondaryFirstSeventeen = sourceCompiledDiagram
sourceStatus smithSplitSecondarySecondSeventeen = sourceCompiledDiagram
sourceStatus smithIllustrativeTwoHundredFortyDegree = sourceCompiledDiagram

sourceStatus smithIllustrativeL2HalfOneHundredSixtyInch = sourceCompiledDiagram
sourceStatus smithIllustrativeL1FortyInch = sourceCompiledDiagram
sourceStatus smithIllustrativeL1TwoHundredTwentyFiveHundredthInch = sourceCompiledDiagram
sourceStatus smithApproxL1FiveHundredSixtyFiveHundredthTurns = sourceCompiledDiagram
sourceStatus smithOptionalParallelFortySevenNanofarad = sourceCompiledDiagram
sourceStatus smithClaimedTwoThousandVolt = sourceCompiledDiagram
sourceStatus smithClaimedSixThousandWatt = sourceCompiledDiagram

originalEarthReelIsNotShuntReel :
  earthThreeElectrodeReel ≡ zvsShuntReel → Contradiction
originalEarthReelIsNotShuntReel ()

originalEarthReelIsNotMidpointTranscript :
  earthThreeElectrodeReel ≡ midpointSparkTranscript → Contradiction
originalEarthReelIsNotMidpointTranscript ()

originalPDFIsNotFilsingerMidpoint :
  smithKellyDarrerPDF ≡ midpointSparkTranscript → Contradiction
originalPDFIsNotFilsingerMidpoint ()

-- This is already a source-owned distinction. Do not equate the narrated
-- Filsinger EARTH and proposed portable plates by treating "ground" as a
-- universal electrical circuit node.
sourceEarthAndPortableDifferent :
  Reel.filsingerEarthNarration ≡ Reel.filsingerPortableProposal →
  Reel.Contradiction
sourceEarthAndPortableDifferent = Reel.earthNotPortable

-- The PDF source itself already owns the distinction between diagrams.
sourceSmithFigureTenAndElevenDifferent :
  Smith.smithSuitcaseFigureTen ≡ Smith.smithSuitcaseFigureEleven →
  Smith.Contradiction
sourceSmithFigureTenAndElevenDifferent = Smith.suitcaseDiagramsDistinct

-- Confirm one source-indexed numeral definitionally, NOT any empirical V*I.
earthReelThreeElectrodesIsThree :
  numberMagnitude earthThreeContacts ≡ 3
earthReelThreeElectrodesIsThree = refl

midpointNarratesFourDiodes :
  numberMagnitude midpointFourDiodes ≡ 4
midpointNarratesFourDiodes = refl

-- NO proof here equates component ratings to operating voltages, wire-length
-- ratios to voltage gain, or across-reel indications to one power interval.
