module DASHI.Culture.CohnInstitutionalExpandedCandidateFibreAskExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Culture.CohnInstitutionalResidualDiagnosisExact as Diagnosis
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionThreeExact as Ext3
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFourExact as Ext4
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFiveExact as Ext5
import DASHI.Governance.MoretonRobinsonRecognitionSovereigntyBoundaryExact as Sovereignty

------------------------------------------------------------------------
-- EXPANDED CANDIDATE FIBRE ASK
--
-- Source acquisition expands candidate questions; it does not silently add
-- observations to the existing synthetic institutional worlds.
--
-- Therefore this audit distinguishes three outcomes:
--   * separates          : the current fixture already contains an observed
--                          coordinate that differs across the collision;
--   * doesNotSeparate    : the current fixture contains the coordinate and its
--                          values coincide across the collision;
--   * fixtureInsufficient: the source family is relevant, but this fixture has
--                          no typed observation for that coordinate yet.
--
-- The third state is essential. Treating every acquired source as if it already
-- supplied world facts would collapse provenance into proof and would rewrite
-- the synthetic collision after the fact.
------------------------------------------------------------------------

data CandidateOutcome : Set where
  separates doesNotSeparate fixtureInsufficient : CandidateOutcome

record ExpandedCandidateFibreAsk : Set where
  constructor expanded-candidate-fibre-ask
  field
    -- Existing six coordinates are already instantiated by the fixture.
    subjectPositionOutcome : CandidateOutcome
    provenanceOutcome : CandidateOutcome
    permissionOutcome : CandidateOutcome
    ignoranceProductionOutcome : CandidateOutcome
    hermeneuticalRefusalOutcome : CandidateOutcome
    criticalUptakeOutcome : CandidateOutcome

    -- Extension-three candidates.
    structuralEpistemicExclusionOutcome : CandidateOutcome
    epistemicLabourOutcome : CandidateOutcome
    outsiderWithinStandpointOutcome : CandidateOutcome
    participationPowerOutcome : CandidateOutcome
    twoEyedCoexistenceActionOutcome : CandidateOutcome

    -- Extension-four candidates/reuse.
    epistemicActivismOutcome : CandidateOutcome
    internalExclusionOutcome : CandidateOutcome
    twoEyedCoLearningOutcome : CandidateOutcome

    -- Extension-five candidate.
    relationalResearchBurdenOutcome : CandidateOutcome

    -- Canonical governance/sovereignty reuse frontiers.
    governancePermissionOutcome : CandidateOutcome
    sovereignAuthorityOutcome : CandidateOutcome

open ExpandedCandidateFibreAsk public

canonicalExpandedCandidateFibreAsk : ExpandedCandidateFibreAsk
canonicalExpandedCandidateFibreAsk = expanded-candidate-fibre-ask
  separates
  doesNotSeparate
  doesNotSeparate
  doesNotSeparate
  separates
  doesNotSeparate
  fixtureInsufficient
  fixtureInsufficient
  fixtureInsufficient
  fixtureInsufficient
  fixtureInsufficient
  fixtureInsufficient
  fixtureInsufficient
  fixtureInsufficient
  fixtureInsufficient
  fixtureInsufficient
  fixtureInsufficient

------------------------------------------------------------------------
-- Why the old six have determinate answers.
------------------------------------------------------------------------

subjectPositionObservedSeparating : Bool
subjectPositionObservedSeparating = Diagnosis.subjectPositionSeparates

provenanceObservedNonSeparating : Bool
provenanceObservedNonSeparating = Diagnosis.provenanceSeparates

permissionObservedNonSeparating : Bool
permissionObservedNonSeparating = Diagnosis.permissionSeparates

ignoranceProductionObservedNonSeparating : Bool
ignoranceProductionObservedNonSeparating = Diagnosis.ignoranceProductionSeparates

hermeneuticalRefusalObservedSeparating : Bool
hermeneuticalRefusalObservedSeparating = Diagnosis.hermeneuticalRefusalSeparates

criticalUptakeObservedNonSeparating : Bool
criticalUptakeObservedNonSeparating = Diagnosis.criticalUptakeSeparates

------------------------------------------------------------------------
-- Source and theorem reuse witnesses. These establish that the candidate
-- families exist; they do NOT fill in missing world observations.
------------------------------------------------------------------------

extensionThreeBoundary : Ext3.AcquisitionThreeBoundary
extensionThreeBoundary = Ext3.canonicalAcquisitionThreeBoundary

extensionFourBoundary : Ext4.AcquisitionFourBoundary
extensionFourBoundary = Ext4.canonicalAcquisitionFourBoundary

extensionFiveBoundary : Ext5.AcquisitionFiveBoundary
extensionFiveBoundary = Ext5.canonicalAcquisitionFiveBoundary

sovereigntyBoundary : Sovereignty.MoretonRobinsonBoundary
sovereigntyBoundary = Sovereignty.canonicalMoretonRobinsonBoundary

------------------------------------------------------------------------
-- Observation debts for the current fixture.
------------------------------------------------------------------------

record ExpandedObservationDebt : Set where
  constructor expanded-observation-debt
  field
    coordinateFamily : String
    missingObservation : String
    acquisitionStatus : String
    admissionRule : String

open ExpandedObservationDebt public

participationPowerDebt : ExpandedObservationDebt
participationPowerDebt = expanded-observation-debt
  "participation power"
  "the current two-world fixture does not encode consultation, influence, control or decision-power observations"
  "source family acquired from Arnstein"
  "instantiate only when a declared consumer observes participation/influence separately from coarse institutional presence"

internalExclusionDebt : ExpandedObservationDebt
internalExclusionDebt = expanded-observation-debt
  "internal exclusion / effective communicative influence"
  "the current fixture does not encode formal access plus communicative uptake/influence"
  "source family acquired from Young"
  "do not infer internal exclusion merely from originating/refused subject-position labels"

epistemicLabourDebt : ExpandedObservationDebt
epistemicLabourDebt = expanded-observation-debt
  "epistemic labour burden"
  "the current fixture does not encode explanatory labour, burden, compensation or coercion"
  "source family acquired from Berenstain"
  "do not infer labour burden from silencing/refusal alone"

epistemicActivismDebt : ExpandedObservationDebt
epistemicActivismDebt = expanded-observation-debt
  "epistemic activism / resistant uptake"
  "the current fixture does not encode collective protest, public formation or resistant communicative uptake"
  "source family acquired from Medina"
  "do not infer activism from the mere existence of disagreement"

relationalResearchBurdenDebt : ExpandedObservationDebt
relationalResearchBurdenDebt = expanded-observation-debt
  "ethical/equitable rights-holder research relation"
  "the current fixture does not encode research partnership, relational labour, systemic support or rights-holder relation"
  "source family acquired from Reid et al. 2024"
  "knowledge inclusion or Indigenous provenance does not populate this coordinate"

sovereignAuthorityDebt : ExpandedObservationDebt
sovereignAuthorityDebt = expanded-observation-debt
  "sovereign authority"
  "the current fixture does not encode recognition/sovereignty observations"
  "canonical Moreton-Robinson theorem owner already exists"
  "reuse the canonical sovereignty boundary only when the institutional consumer actually asks an authority/recognition question"

------------------------------------------------------------------------
-- Global boundary: acquisition changes the candidate frontier, not the facts.
------------------------------------------------------------------------

record ExpandedCandidateBoundary : Set where
  constructor expanded-candidate-boundary
  field
    acquisitionExpandsCandidateQuestionSet : Bool
    acquisitionAloneMayRewriteExistingWorldFacts : Bool
    missingObservationMayBeFilledFromSourceLabel : Bool
    fixtureInsufficientMeansSourceTheoryFalse : Bool
    existingSeparatingCoordinateMayBeRetroactivelyDeleted : Bool
    currentFixtureStillSelectsHermeneuticalRefusal : Bool
    richerFutureFixtureMaySelectDifferentResidual : Bool
    sourceIdentityCreatesRepairAuthority : Bool

open ExpandedCandidateBoundary public

canonicalExpandedCandidateBoundary : ExpandedCandidateBoundary
canonicalExpandedCandidateBoundary = expanded-candidate-boundary
  true false false false false true true false

selectedResidualRemainsHermeneuticalRefusal :
  Diagnosis.selectedResidualIsHermeneuticalRefusal ≡ true
selectedResidualRemainsHermeneuticalRefusal = refl

------------------------------------------------------------------------
-- Pareto result of asking the current fibre.
------------------------------------------------------------------------

record ExpandedCandidateAskFrontier : Set where
  constructor expanded-candidate-ask-frontier
  field
    currentSeparators : String
    currentNonSeparators : String
    currentFixtureInsufficientFamilies : String
    sourceAcquisitionGain : String
    nextHighValueMove : String
    stopRule : String

open ExpandedCandidateAskFrontier public

canonicalExpandedCandidateAskFrontier : ExpandedCandidateAskFrontier
canonicalExpandedCandidateAskFrontier = expanded-candidate-ask-frontier
  "subject position; hermeneutical refusal"
  "provenance; permission; ignorance production; critical uptake"
  "structural epistemic exclusion; epistemic labour; outsider-within standpoint; participation power; Two-Eyed coexistence/action; epistemic activism; internal exclusion; co-learning; relational research burden; governance/permission refinement; sovereign authority"
  "the source follow decomposes the question space and tells us exactly which observations a richer institutional consumer would need; it does not alter the existing synthetic diagnosis"
  "construct or reuse a concrete institutional fixture that actually observes one or more insufficient coordinates, then rerun the existing discriminator/proof-search/369 admission machinery"
  "do not assign values to an unobserved coordinate merely because a source makes that coordinate conceptually available"
