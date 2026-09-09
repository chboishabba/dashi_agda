module DASHI.Cognition.PNF.SensibLawCullenOALCPNFInputParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawOALCLegislationParserInputContractExact as OALC

------------------------------------------------------------------------
-- CULLEN OALC -> spaCy -> PNF PARITY FIXTURE
--
-- Runtime target mirrored by SLR's run_cullen_oalc_pnf.py:
--   2 exact OALC NSW legislation documents
--   -> 8 source-preserving statutory slices
--   -> spaCy observations
--   -> sensiblaw-stream / PNF receipts.
--
-- OALC remains latest-known-only for temporal coverage unless a separate
-- historical equivalence receipt is supplied. No manual legal/Atomic labels
-- are part of this parser-input contract.
------------------------------------------------------------------------

cullenOALCDocumentCount : String
cullenOALCDocumentCount = "2"

cullenOALCSectionCount : String
cullenOALCSectionCount = "8"

cullenOALCCivilLiabilityCitation : String
cullenOALCCivilLiabilityCitation = OALC.cullenCivilLiabilityActCitation

cullenOALCVicariousCitation : String
cullenOALCVicariousCitation = OALC.cullenVicariousLiabilityActCitation

cullenOALCCivilLiabilitySections : String
cullenOALCCivilLiabilitySections = OALC.cullenCivilLiabilitySections

cullenOALCVicariousSections : String
cullenOALCVicariousSections = OALC.cullenVicariousLiabilitySections

cullenOALCTemporalCoverage : OALC.OALCTemporalCoverage
cullenOALCTemporalCoverage = OALC.latestKnownOnly

cullenOALCParserPipeline : String
cullenOALCParserPipeline =
  "local OALC corpus.jsonl -> pinned corpus revision -> exact NSW legislation record -> source-preserving section slice -> spacy_stream.py -> sensiblaw-stream -> PNF receipt"

record CullenOALCPNFParityBoundary : Set where
  constructor cullen-oalc-pnf-parity-boundary
  field
    exactlyTwoLegislationDocuments : Bool
    exactlyEightStatutorySlices : Bool
    pinnedCorpusRevisionRequired : Bool
    sourceSpansAndDigestsRetained : Bool
    latestKnownOnlyRetained : Bool
    historical2017EquivalenceClaimed : Bool
    manualAtomicLabelsRequired : Bool
    parserOutputCreatesLegalAuthority : Bool
    parserOutputCreatesAtomicGate : Bool

canonicalCullenOALCPNFParityBoundary : CullenOALCPNFParityBoundary
canonicalCullenOALCPNFParityBoundary =
  cullen-oalc-pnf-parity-boundary
    true true true true true false false false false

data OALCParserRunPays2017HistoricalEquivalence : Set where
data OALCParserRunCreatesCullenBreachGate : Set where
data OALCParserRunCreatesVicariousLiability : Set where
data MissingHistoricalReceiptBlocksParserExperiment : Set where

parserRunDoesNotPay2017HistoricalEquivalence :
  OALCParserRunPays2017HistoricalEquivalence → ⊥
parserRunDoesNotPay2017HistoricalEquivalence ()

parserRunDoesNotCreateCullenBreachGate :
  OALCParserRunCreatesCullenBreachGate → ⊥
parserRunDoesNotCreateCullenBreachGate ()

parserRunDoesNotCreateVicariousLiability :
  OALCParserRunCreatesVicariousLiability → ⊥
parserRunDoesNotCreateVicariousLiability ()

missingHistoricalReceiptDoesNotBlockParserExperiment :
  MissingHistoricalReceiptBlocksParserExperiment → ⊥
missingHistoricalReceiptDoesNotBlockParserExperiment ()

cullenOALCReading : String
cullenOALCReading =
  "Use the pinned local OALC corpus as the operational parser source for the two governing NSW Acts. Preserve latest-known-only temporal status through all eight section-slice PNF receipts. Historical equivalence to 2017-01-26 remains a separate unresolved source coordinate and does not block parser/PNF experimentation."
