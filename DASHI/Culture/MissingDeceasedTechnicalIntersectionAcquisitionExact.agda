module DASHI.Culture.MissingDeceasedTechnicalIntersectionAcquisitionExact where

------------------------------------------------------------------------
-- PROOF-DIRECTED ACQUISITION FOR TECHNICAL INTERSECTIONS
--
-- Candidate domain adjacency is not promoted to dependency.  Instead it emits
-- the exact evidence object that would be sufficient to upgrade the edge.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TechnicalDependencyHypergraphExact as H
import DASHI.Culture.MissingDeceasedTechnicalDependencyHypergraphExact as Graph
import DASHI.Core.ReopenableHypothesisForestExact as Forest

------------------------------------------------------------------------
-- Acquisition targets.
------------------------------------------------------------------------

data TechnicalIntersectionTarget : Set where
  rezaMcCaslandAirForceAwardOrContract
  rezaMcCaslandJointProgrammeDocument
  rezaMcCaslandNamedPersonnelRoster
  scorpiusSpaceNuclearSharedSupplierOrTechnologyTransfer
  scorpiusSpaceNuclearSharedPersonnel
  plasmaSpaceNuclearSharedProgramme
  jplPlanetarySharedMissionOrInstrument
  jplPlanetarySharedPublicationOrProposal
  : TechnicalIntersectionTarget

data TargetStatus : Set where
  targetNotLocated
  targetPresent
  targetKnownAbsent
  : TargetStatus

record TechnicalIntersectionAcquisition : Set where
  constructor technical-intersection-acquisition
  field
    target : TechnicalIntersectionTarget
    status : TargetStatus
    candidateConnection : String
    preferredSource : String
    fallbackSource : String
    upgradeRule : String

open TechnicalIntersectionAcquisition public

rezaMcCaslandContractAcquisition : TechnicalIntersectionAcquisition
rezaMcCaslandContractAcquisition =
  technical-intersection-acquisition
    rezaMcCaslandAirForceAwardOrContract
    targetNotLocated
    "Monica Reza advanced materials <-> William McCasland / AFRL-space programme"
    "Air Force/AFRL award, contract, SBIR/STTR, programme-office, procurement or archival programme record naming Reza/Jacinto, her employer, patent/alloy, and the relevant programme"
    "JPL/Rocketdyne/Boeing archival project record or authenticated personnel correspondence containing a programme/contract identifier"
    "upgrade reportedRelationshipOnly/domainSimilarityOnly only if a primary same-programme or funding receipt is recovered"

rezaMcCaslandProgrammeAcquisition : TechnicalIntersectionAcquisition
rezaMcCaslandProgrammeAcquisition =
  technical-intersection-acquisition
    rezaMcCaslandJointProgrammeDocument
    targetNotLocated
    "Reza <-> McCasland alleged early-2000s Air Force-funded advanced-materials programme"
    "primary programme report, technical memorandum, final report, award abstract, or official team roster"
    "archived institutional biography/CV or contemporaneous conference/patent acknowledgement naming the programme"
    "same-object weld requires named programme plus role-specific person edges"

nuclearSystemsSupplierAcquisition : TechnicalIntersectionAcquisition
nuclearSystemsSupplierAcquisition =
  technical-intersection-acquisition
    scorpiusSpaceNuclearSharedSupplierOrTechnologyTransfer
    targetNotLocated
    "Scorpius/DARHT pulsed-power diagnostics <-> NASA space nuclear propulsion/fission instrumentation"
    "procurement/contract/technology-transfer record identifying a shared component technology or supplier"
    "shared patent/publication or named cross-programme technical working group"
    "broad nuclear engineering similarity is insufficient without a common technical object"

nuclearSystemsPersonnelAcquisition : TechnicalIntersectionAcquisition
nuclearSystemsPersonnelAcquisition =
  technical-intersection-acquisition
    scorpiusSpaceNuclearSharedPersonnel
    targetNotLocated
    "Scorpius/DARHT <-> NASA space nuclear systems"
    "official team rosters or author lists showing the same named engineer/scientist on both technical programmes"
    "conference proceedings / working-group minutes with same-object identity receipts"
    "shared person must have role-bearing edges to both programmes"

plasmaSpaceProgrammeAcquisition : TechnicalIntersectionAcquisition
plasmaSpaceProgrammeAcquisition =
  technical-intersection-acquisition
    plasmaSpaceNuclearSharedProgramme
    targetNotLocated
    "MIT fusion/plasma physics <-> space nuclear/fission systems"
    "grant/contract/programme record naming both technical streams or shared investigators"
    "joint publication, workshop programme, advisory panel or technology-transfer record"
    "physics-domain adjacency alone remains unresolved candidate"

planetarySharedMissionAcquisition : TechnicalIntersectionAcquisition
planetarySharedMissionAcquisition =
  technical-intersection-acquisition
    jplPlanetarySharedMissionOrInstrument
    targetNotLocated
    "Hicks planetary defence/NEO work <-> Maiwald planetary mass spectrometry/biosignature work"
    "NASA/JPL mission or instrument team roster naming both people"
    "joint proposal, publication, instrument development record or mission archive"
    "common JPL employment and common planetary-science domain do not suffice"

planetarySharedPublicationAcquisition : TechnicalIntersectionAcquisition
planetarySharedPublicationAcquisition =
  technical-intersection-acquisition
    jplPlanetarySharedPublicationOrProposal
    targetNotLocated
    "Hicks <-> Maiwald technical intersection"
    "publication/proposal with both names and a shared scientific object"
    "conference abstract or institutional project record naming both"
    "co-occurrence must be scientific/technical, not merely institutional"

------------------------------------------------------------------------
-- Reopenable semantics: unresolved candidate != refuted candidate.
------------------------------------------------------------------------

data TechnicalConnectionHypothesis : Set where
  rezaMcCaslandTechnicalConnection
  scorpiusSpaceNuclearTechnicalConnection
  plasmaSpaceNuclearTechnicalConnection
  hicksMaiwaldTechnicalConnection
  : TechnicalConnectionHypothesis

technicalConnectionSemantics : Forest.HypothesisSemantics TechnicalConnectionHypothesis
technicalConnectionSemantics =
  Forest.hypothesisSemantics
    (λ _ → ⊥)
    (λ _ _ → ⊤)

rezaMcCaslandDeferred :
  Forest.HypothesisTransition
    technicalConnectionSemantics
    rezaMcCaslandTechnicalConnection
    Forest.active
    (Forest.reopenable Forest.ambiguityUnresolved)
rezaMcCaslandDeferred = Forest.defer Forest.ambiguityUnresolved

noAcquisitionResultDoesNotRefuteTechnicalConnection :
  Forest.HypothesisTransition
    technicalConnectionSemantics
    rezaMcCaslandTechnicalConnection
    (Forest.reopenable Forest.ambiguityUnresolved)
    Forest.refuted → ⊥
noAcquisitionResultDoesNotRefuteTechnicalConnection = Forest.noDirectDormantRefutation

record TechnicalIntersectionAcquisitionBoundary : Set where
  constructor technical-intersection-acquisition-boundary
  field
    candidateAdjacencyCreatesTargetedAcquisition : Bool
    candidateAdjacencyCreatesTargetedAcquisitionIsTrue :
      candidateAdjacencyCreatesTargetedAcquisition ≡ true

    failedSearchEqualsKnownAbsence : Bool
    failedSearchEqualsKnownAbsenceIsFalse : failedSearchEqualsKnownAbsence ≡ false

    missingSharedProgrammeRefutesAllPossibleConnection : Bool
    missingSharedProgrammeRefutesAllPossibleConnectionIsFalse :
      missingSharedProgrammeRefutesAllPossibleConnection ≡ false

    primarySharedProgrammeReceiptCanUpgradeConnection : Bool
    primarySharedProgrammeReceiptCanUpgradeConnectionIsTrue :
      primarySharedProgrammeReceiptCanUpgradeConnection ≡ true

canonicalTechnicalIntersectionAcquisitionBoundary :
  TechnicalIntersectionAcquisitionBoundary
canonicalTechnicalIntersectionAcquisitionBoundary =
  technical-intersection-acquisition-boundary
    true refl
    false refl
    false refl
    true refl
