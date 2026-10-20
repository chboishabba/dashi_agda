module DASHI.Ontology.EducationOntologyMappingPNFExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)

import DASHI.Cognition.PNF.TypePressure as PNFPressure
open import DASHI.Ontology.EducationOntologyMappingSSSOMExact

------------------------------------------------------------------------
-- SSSOM <-> PNF SEMANTIC BRIDGE
--
-- SSSOM is an exchange/provenance surface for mapping assertions.
-- PNF TypePressure is an internal evidence-evaluation surface carrying signed
-- pressure, provenance and scope while explicitly refusing to promote pressure
-- alone into type truth.
--
-- Therefore the bridge is interpretive, not definitional:
--   mapping row != signed pressure
--   predicate != pressure direction
--   confidence != pressure magnitude
--   mapped object != asserted type
------------------------------------------------------------------------

record MappingPNFInterpretation (mapping : SSSOMMapping) : Set where
  constructor mappingPNFInterpretation
  field
    interpretedPressure : ℤ
    interpretationProvenance : String
    interpretationScope : String

open MappingPNFInterpretation public

asTypePressureContribution :
  {mapping : SSSOMMapping} →
  MappingPNFInterpretation mapping →
  PNFPressure.TypePressureContribution
    {Subject = String}
    {CandidateType = String}
    {Evidence = SSSOMMapping}
    (subjectId mapping)
    (objectId mapping)
asTypePressureContribution {mapping} interpretation =
  PNFPressure.typePressureContribution
    mapping
    (interpretedPressure interpretation)
    (interpretationProvenance interpretation)
    (interpretationScope interpretation)

mappingEvidencePreserved :
  {mapping : SSSOMMapping}
  (interpretation : MappingPNFInterpretation mapping) →
  PNFPressure.evidence (asTypePressureContribution interpretation) ≡ mapping
mappingEvidencePreserved interpretation = refl

mappingPressurePreserved :
  {mapping : SSSOMMapping}
  (interpretation : MappingPNFInterpretation mapping) →
  PNFPressure.signedPressure (asTypePressureContribution interpretation)
  ≡ interpretedPressure interpretation
mappingPressurePreserved interpretation = refl

mappingProvenancePreserved :
  {mapping : SSSOMMapping}
  (interpretation : MappingPNFInterpretation mapping) →
  PNFPressure.provenance (asTypePressureContribution interpretation)
  ≡ interpretationProvenance interpretation
mappingProvenancePreserved interpretation = refl

mappingScopePreserved :
  {mapping : SSSOMMapping}
  (interpretation : MappingPNFInterpretation mapping) →
  PNFPressure.scope (asTypePressureContribution interpretation)
  ≡ interpretationScope interpretation
mappingScopePreserved interpretation = refl

------------------------------------------------------------------------
-- NO AUTOMATIC PRESSURE FROM EXCHANGE METADATA
------------------------------------------------------------------------

data MappingPredicateDeterminesPressure : Set where

data MappingConfidenceDeterminesPressure : Set where

data MappingJustificationDeterminesPressure : Set where

predicateDoesNotDeterminePressure : MappingPredicateDeterminesPressure → ⊥
predicateDoesNotDeterminePressure ()

confidenceDoesNotDeterminePressure : MappingConfidenceDeterminesPressure → ⊥
confidenceDoesNotDeterminePressure ()

justificationDoesNotDeterminePressure : MappingJustificationDeterminesPressure → ⊥
justificationDoesNotDeterminePressure ()

------------------------------------------------------------------------
-- PNF PRESSURE REMAINS EVIDENCE, NOT TYPE ASSERTION
------------------------------------------------------------------------

mappingPressureCannotAssertType :
  PNFPressure.TypePressurePromotionPermission → ⊥
mappingPressureCannotAssertType = PNFPressure.pressureAloneCannotAssertType

mappingRowCannotAssertOntologyTruth :
  MappingTruthPermission mappingForReviewOnly → ⊥
mappingRowCannotAssertOntologyTruth = mappingCannotAssertOntologyTruth

------------------------------------------------------------------------
-- REVIEW FINDINGS AS REOPENABLE RESIDUAL STATE
--
-- This is intentionally coarse: it records whether mapping review has paid the
-- local concern.  It does not identify a review finding with a PNF pressure or
-- fabricate a repair operation.
------------------------------------------------------------------------

data MappingResidualState : Set where
  noResidual : MappingResidualState
  reviewResidual : MappingResidualState
  openResidual : MappingResidualState

mappingFindingToResidual : MappingReviewFinding → MappingResidualState
mappingFindingToResidual noObservedMappingConflict = noResidual
mappingFindingToResidual predicateTooStrong = reviewResidual
mappingFindingToResidual sourceVersionDrift = reviewResidual
mappingFindingToResidual hierarchyConflict = openResidual
mappingFindingToResidual disjointnessConflict = openResidual
mappingFindingToResidual unresolvedMappingConflict = openResidual

unresolvedFindingRemainsOpen :
  mappingFindingToResidual unresolvedMappingConflict ≡ openResidual
unresolvedFindingRemainsOpen = refl

hierarchyConflictRemainsOpen :
  mappingFindingToResidual hierarchyConflict ≡ openResidual
hierarchyConflictRemainsOpen = refl

disjointnessConflictRemainsOpen :
  mappingFindingToResidual disjointnessConflict ≡ openResidual
disjointnessConflictRemainsOpen = refl

------------------------------------------------------------------------
-- CONCEPTUAL CORRESPONDENCE RECEIPT
------------------------------------------------------------------------

record MappingPNFCorrespondenceStatus : Set where
  constructor mappingPNFCorrespondenceStatus
  field
    mappingRowUsedAsEvidence : Bool
    signedPressureRequiresInterpretation : Bool
    provenanceAndScopePreserved : Bool
    confidencePressureSeparated : Bool
    predicatePressureSeparated : Bool
    pressureDoesNotAssertType : Bool
    unresolvedReviewRemainsResidual : Bool

    mappingRowUsedAsEvidenceIsTrue : mappingRowUsedAsEvidence ≡ true
    signedPressureRequiresInterpretationIsTrue : signedPressureRequiresInterpretation ≡ true
    provenanceAndScopePreservedIsTrue : provenanceAndScopePreserved ≡ true
    confidencePressureSeparatedIsTrue : confidencePressureSeparated ≡ true
    predicatePressureSeparatedIsTrue : predicatePressureSeparated ≡ true
    pressureDoesNotAssertTypeIsTrue : pressureDoesNotAssertType ≡ true
    unresolvedReviewRemainsResidualIsTrue : unresolvedReviewRemainsResidual ≡ true

open MappingPNFCorrespondenceStatus public

canonicalMappingPNFCorrespondenceStatus : MappingPNFCorrespondenceStatus
canonicalMappingPNFCorrespondenceStatus =
  mappingPNFCorrespondenceStatus
    true true true true true true true
    refl refl refl refl refl refl refl
