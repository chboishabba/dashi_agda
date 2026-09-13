module DASHI.Wikimedia.IbrahimFirstLinkParserTestHarnessArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimFirstLinkHistoricalDiscriminatorParetoExact as Pareto

------------------------------------------------------------------------
-- IBRAHIM PARSER TEST-HARNESS ARCHAEOLOGY
--
-- The released parser_tests notebook does not replay frozen 2014 XML fixtures.
-- It calls English Wikipedia Special:Export live for named pages and compares
-- the result against hard-coded expected first links.  Stored notebook output
-- already contains numerous mismatches.  Therefore it is parser-development
-- evidence, not a historical-corpus reproduction receipt.
------------------------------------------------------------------------

record ParserTestHarnessReceipt : Set where
  constructor parser-test-harness-receipt
  field
    notebookLink : String
    fetchSurface : String
    expectedEdgesHardCoded : Bool
    historicalRevisionPinned : Bool
    historicalDumpPinned : Bool
    storedMismatchesPresent : Bool
    usefulAsParserDevelopmentEvidence : Bool
    certifiesOctober2014Fln : Bool
    certifiesNovember2014Fln : Bool
open ParserTestHarnessReceipt public

releasedParserTestHarness : ParserTestHarnessReceipt
releasedParserTestHarness = parser-test-harness-receipt
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/tests/parser_tests.ipynb"
  "https://en.wikipedia.org/wiki/Special:Export/<page>"
  true false false true true false false

record StoredMismatchWitness : Set where
  constructor stored-mismatch-witness
  field
    page : String
    expected : String
    storedObserved : String
    reading : String
open StoredMismatchWitness public

donaukanalMismatch : StoredMismatchWitness
donaukanalMismatch = stored-mismatch-witness
  "Donaukanal" "Danube" "Project:AWB"
  "stored live-page notebook output differs from the hard-coded expectation; this does not determine whether parser logic or page revision caused the difference"

mutationKnotMismatch : StoredMismatchWitness
mutationKnotMismatch = stored-mismatch-witness
  "Mutation (knot theory)" "Mathematics" "knot genus"
  "another stored mismatch demonstrating that the notebook is not a frozen historical regression receipt"

------------------------------------------------------------------------
-- Consequence for the Pareto investigation.
------------------------------------------------------------------------

historicalReplayRequirement : String
historicalReplayRequirement =
  "replace live Special:Export acquisition with exact timestamp/revision or exact dump-page XML, then replay the released parser and compare against primary-paper edges and the published FLN map"

historicalReplayTarget : Pareto.ParetoTarget
historicalReplayTarget = Pareto.thirdTarget

data LiveSpecialExportCreatesHistoricalFixture : Set where
data HardCodedExpectationIdentifiesCorpus : Set where
data StoredMismatchProvesParserBug : Set where
data StoredMatchProvesHistoricalReproduction : Set where

liveExportDoesNotCreateHistoricalFixture : LiveSpecialExportCreatesHistoricalFixture → ⊥
liveExportDoesNotCreateHistoricalFixture ()

expectationDoesNotIdentifyCorpus : HardCodedExpectationIdentifiesCorpus → ⊥
expectationDoesNotIdentifyCorpus ()

storedMismatchDoesNotByItselfProveParserBug : StoredMismatchProvesParserBug → ⊥
storedMismatchDoesNotByItselfProveParserBug ()

storedMatchDoesNotProveHistoricalReproduction : StoredMatchProvesHistoricalReproduction → ⊥
storedMatchDoesNotProveHistoricalReproduction ()

record ParserHarnessBoundary : Set where
  constructor parser-harness-boundary
  field
    liveAcquisitionExplicit : Bool
    hardCodedExpectationsExplicit : Bool
    storedMismatchExplicit : Bool
    historicalFixtureStatusPaid : Bool
    octoberCertificationPaid : Bool
    novemberCertificationPaid : Bool
open ParserHarnessBoundary public

canonicalParserHarnessBoundary : ParserHarnessBoundary
canonicalParserHarnessBoundary =
  parser-harness-boundary true true true false false false
