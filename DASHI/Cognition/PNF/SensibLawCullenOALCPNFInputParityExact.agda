module DASHI.Cognition.PNF.SensibLawCullenOALCPNFInputParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawOALCLegislationParserInputContractExact as OALC

------------------------------------------------------------------------
-- CULLEN LEGALFOLLOW -> OALC -> spaCy -> PNF PARITY FIXTURE
--
-- Runtime target mirrored by SLR's run_cullen_oalc_pnf.py:
--   2 exact LegalFollow primary-legislation demands
--   -> governed OALC resolution / retained document receipts
--   -> 8 source-preserving statutory slices
--   -> spaCy observations
--   -> sensiblaw-stream / PNF receipts.
--
-- No corpus.jsonl path is part of the public contract. A local JSONL snapshot
-- may still serve an offline provider backend, but it is not required by the
-- consumer, LegalFollow demand, or parser handoff.
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
  "LegalFollow exact source demand -> governed OALC resolution -> retained dataset/version/digest receipt -> source-preserving statutory slice -> spacy_stream.py -> sensiblaw-stream -> PNF receipt"

record CullenOALCPNFParityBoundary : Set where
  constructor cullen-oalc-pnf-parity-boundary
  field
    exactlyTwoLegislationDemands : Bool
    exactlyTwoResolvedDocuments : Bool
    exactlyEightStatutorySlices : Bool
    localCorpusPathRequired : Bool
    datasetRevisionPinnedAtResolution : Bool
    sourceSpansAndDigestsRetained : Bool
    latestKnownOnlyRetained : Bool
    historical2017EquivalenceClaimed : Bool
    manualAtomicLabelsRequired : Bool
    parserOutputCreatesLegalAuthority : Bool
    parserOutputCreatesAtomicGate : Bool

canonicalCullenOALCPNFParityBoundary : CullenOALCPNFParityBoundary
canonicalCullenOALCPNFParityBoundary =
  cullen-oalc-pnf-parity-boundary
    true true true false true true true false false false false

data LocalCorpusAbsenceBlocksLegalFollowOALC : Set where
data OALCParserRunPays2017HistoricalEquivalence : Set where
data OALCParserRunCreatesCullenBreachGate : Set where
data OALCParserRunCreatesVicariousLiability : Set where
data MissingHistoricalReceiptBlocksParserExperiment : Set where

localCorpusAbsenceDoesNotBlockLegalFollowOALC :
  LocalCorpusAbsenceBlocksLegalFollowOALC → ⊥
localCorpusAbsenceDoesNotBlockLegalFollowOALC ()

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
  "LegalFollow identifies the two governing primary-legislation source demands. The governed OALC provider resolves and retains only those exact latest-known documents, pins the observed corpus revision in the receipt, and passes eight source-preserving section slices into spaCy/PNF. No local corpus.jsonl is required. Historical equivalence to 2017-01-26 remains a separate unresolved source coordinate and does not block parser experimentation."
