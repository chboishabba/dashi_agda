module DASHI.Cognition.PNF.SensibLawBrightonS185ViolationElementFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Law.SensibLawBrightonPremisesConditionEvidenceExact as Condition
import DASHI.Law.SensibLawBrightonMaintenanceChronologyEvidenceExact as Chronology
import DASHI.Law.SensibLawBrightonS185ApplicabilityEvidenceExact as Applicability
import DASHI.Cognition.PNF.SensibLawBrightonS185Subsection3aCompilerExact as S185

------------------------------------------------------------------------
-- BRIGHTON s 185: MINIMAL LIVE FRONTIER
--
-- Paid:
--   * material premises-condition / agent non-liveability recognition;
--   * remediation remained outstanding on 20 January 2023;
--   * fixed-term tenancy continued on 24 January 2023;
--   * ordinary general-tenancy carrier is within s 185 rather than the
--     moveable-dwelling-site exclusion;
--   * direct historical s 185(3)(a) compiler.
--
-- Therefore the first surviving coordinate is no longer generic statutory
-- non-performance.  It is the source/evidence classification needed by the
-- direct compiler:
--
--   premises objectively unfit for the tenant to live in at the evaluation time.
--
-- Agent characterisation, photos, remediation delay and a Form 12 labelled
-- non-liveability are strong evidence carriers but are not silently promoted to
-- that objective legal classification here.
------------------------------------------------------------------------

conditionElementReference : String
conditionElementReference =
  "Brighton material premises-condition / agent non-liveability recognition"

outstandingRemediationElementReference : String
outstandingRemediationElementReference =
  "Brighton known remediation remained outstanding on 20 January 2023"

continuingTenancyElementReference : String
continuingTenancyElementReference =
  "Brighton tenancy continuing on 24 January 2023"

s185ApplicabilityElementReference : String
s185ApplicabilityElementReference =
  "Brighton general tenancy within historical RTRA s185"

objectiveUnfitnessElementReference : String
objectiveUnfitnessElementReference =
  "Brighton premises objectively unfit for tenant to live in at evaluation time"

conditionElementEvaluation :
  (wrongTypeReference : Ontology.StableId) → Legal.WrongElementEvaluation
conditionElementEvaluation wrong =
  Legal.wrongElementEvaluation wrong conditionElementReference Legal.elementSatisfied []
    "paid narrowly by BrightonPremisesConditionEvidenceExact"

outstandingRemediationElementEvaluation :
  (wrongTypeReference : Ontology.StableId) → Legal.WrongElementEvaluation
outstandingRemediationElementEvaluation wrong =
  Legal.wrongElementEvaluation wrong outstandingRemediationElementReference Legal.elementSatisfied []
    "paid narrowly by BrightonMaintenanceChronologyEvidenceExact"

continuingTenancyElementEvaluation :
  (wrongTypeReference : Ontology.StableId) → Legal.WrongElementEvaluation
continuingTenancyElementEvaluation wrong =
  Legal.wrongElementEvaluation wrong continuingTenancyElementReference Legal.elementSatisfied []
    "paid by private Form18a fixed-term receipt: 2022-08-09 to 2023-02-08"

s185ApplicabilityElementEvaluation :
  (wrongTypeReference : Ontology.StableId) → Legal.WrongElementEvaluation
s185ApplicabilityElementEvaluation wrong =
  Legal.wrongElementEvaluation wrong s185ApplicabilityElementReference Legal.elementSatisfied []
    "paid by ordinary general-tenancy Form18a carrier and historical s185 source boundary"

firstOpenElementReference : String
firstOpenElementReference = objectiveUnfitnessElementReference

firstOpenElementEvaluation :
  (wrongTypeReference : Ontology.StableId) → Legal.WrongElementEvaluation
firstOpenElementEvaluation wrong =
  Legal.wrongElementEvaluation wrong firstOpenElementReference Legal.elementUnresolved []
    "direct s185(3)(a) compiler is ready; objective legal unfitness remains the first uninhabited source/evidence coordinate"

conditionElementDispositionIsSatisfied :
  ∀ wrong → Legal.disposition (conditionElementEvaluation wrong) ≡ Legal.elementSatisfied
conditionElementDispositionIsSatisfied wrong = refl

outstandingRemediationDispositionIsSatisfied :
  ∀ wrong → Legal.disposition (outstandingRemediationElementEvaluation wrong) ≡ Legal.elementSatisfied
outstandingRemediationDispositionIsSatisfied wrong = refl

continuingTenancyDispositionIsSatisfied :
  ∀ wrong → Legal.disposition (continuingTenancyElementEvaluation wrong) ≡ Legal.elementSatisfied
continuingTenancyDispositionIsSatisfied wrong = refl

s185ApplicabilityDispositionIsSatisfied :
  ∀ wrong → Legal.disposition (s185ApplicabilityElementEvaluation wrong) ≡ Legal.elementSatisfied
s185ApplicabilityDispositionIsSatisfied wrong = refl

firstOpenElementDispositionIsUnresolved :
  ∀ wrong → Legal.disposition (firstOpenElementEvaluation wrong) ≡ Legal.elementUnresolved
firstOpenElementDispositionIsUnresolved wrong = refl

conditionBundlePaysNarrowCoordinate :
  Condition.narrowConditionCoordinatePaid Condition.canonicalBrightonPremisesConditionEvidenceBundle ≡ true
conditionBundlePaysNarrowCoordinate = refl

chronologyPaysOutstandingRemediationCoordinate :
  Chronology.narrowOutstandingRemediationCoordinatePaid Chronology.canonicalBrightonMaintenanceChronologyEvidence ≡ true
chronologyPaysOutstandingRemediationCoordinate = refl

applicabilityPaysContinuingTenancyCoordinate :
  Applicability.continuingTenancyCoordinatePaid Applicability.canonicalBrightonS185ApplicabilityEvidence ≡ true
applicabilityPaysContinuingTenancyCoordinate = refl

applicabilityPaysS185Coordinate :
  Applicability.subsection185AppliesCoordinatePaid Applicability.canonicalBrightonS185ApplicabilityEvidence ≡ true
applicabilityPaysS185Coordinate = refl

objectiveUnfitnessWouldCompileNonPerformance :
  S185.PremisesObjectivelyUnfitAtEvaluation → S185.S185Subsection3aNonPerformance
objectiveUnfitnessWouldCompileNonPerformance = S185.brightonS185Subsection3aFromObjectiveUnfitness

data AgentSaysNonLiveableAutomaticallyObjectiveUnfitness : Set where
data NonLiveabilityForm12AutomaticallyObjectiveUnfitness : Set where
data PhotosAutomaticallyObjectiveUnfitness : Set where
data OutstandingRemediationAutomaticallyObjectiveUnfitness : Set where
data ObjectiveUnfitnessAutomaticallyEqualsWholeViolation : Set where

agentCharacterisationDoesNotAutoPayObjectiveUnfitness :
  AgentSaysNonLiveableAutomaticallyObjectiveUnfitness → ⊥
agentCharacterisationDoesNotAutoPayObjectiveUnfitness ()

form12LabelDoesNotAutoPayObjectiveUnfitness :
  NonLiveabilityForm12AutomaticallyObjectiveUnfitness → ⊥
form12LabelDoesNotAutoPayObjectiveUnfitness ()

photosDoNotAutoPayObjectiveUnfitness : PhotosAutomaticallyObjectiveUnfitness → ⊥
photosDoNotAutoPayObjectiveUnfitness ()

outstandingRemediationDoesNotAutoPayObjectiveUnfitness :
  OutstandingRemediationAutomaticallyObjectiveUnfitness → ⊥
outstandingRemediationDoesNotAutoPayObjectiveUnfitness ()

objectiveUnfitnessDoesNotAutoEqualWholeViolation :
  ObjectiveUnfitnessAutomaticallyEqualsWholeViolation → ⊥
objectiveUnfitnessDoesNotAutoEqualWholeViolation ()

record BrightonS185ViolationElementFrontierBoundary : Set where
  constructor brighton-s185-violation-element-frontier-boundary
  field
    conditionElementSatisfied : Bool
    outstandingRemediationElementSatisfied : Bool
    continuingTenancyElementSatisfied : Bool
    s185ApplicabilityElementSatisfied : Bool
    directSubsection3aCompilerReady : Bool
    firstOpenElementIsObjectiveUnfitness : Bool
    firstOpenElementDispositionUnresolved : Bool
    agentCharacterisationAutomaticallyPaysObjectiveUnfitness : Bool
    form12LabelAutomaticallyPaysObjectiveUnfitness : Bool
    photosAutomaticallyPayObjectiveUnfitness : Bool
    outstandingRemediationAutomaticallyPaysObjectiveUnfitness : Bool
    objectiveUnfitnessAutomaticallyEqualsWholeViolation : Bool

canonicalBrightonS185ViolationElementFrontierBoundary :
  BrightonS185ViolationElementFrontierBoundary
canonicalBrightonS185ViolationElementFrontierBoundary =
  brighton-s185-violation-element-frontier-boundary
    true true true true true true true
    false false false false false
