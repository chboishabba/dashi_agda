module DASHI.Wikimedia.SensibLawNatClimateReviewHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.NativeStatementExact as WD
import DASHI.Wikimedia.NativeReferenceSemanticsExact as Ref
import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact as Handoff
import DASHI.Wikimedia.SourceProvenanceExact as Source

------------------------------------------------------------------------
-- SENSIBLAW NAT / CLIMATE P5991 -> P14143 HANDOFF CALIBRATION
--
-- Source donors on SensibLaw/main d25cddf...:
--   docs/planning/wikidata_ontology_group_handoff_nat_lane_20260401.md
--   docs/planning/wikidata_climate_change_property_migration_protocol_20260327.md
--   schemas/sl.source_unit.v1.schema.yaml
--   docs/planning/wikidata_review_packet_contract_20260401.md
--
-- The handoff is a governed review workflow, not a theorem that every P5991
-- statement should migrate to P14143.
------------------------------------------------------------------------

carbonFootprintP5991 : Id.PropertyId
carbonFootprintP5991 = Id.propertyId "P5991"

annualGreenhouseGasEmissionsP14143 : Id.PropertyId
annualGreenhouseGasEmissionsP14143 = Id.propertyId "P14143"

qualifierP3831 : Id.PropertyId
qualifierP3831 = Id.propertyId "P3831"

qualifierP459 : Id.PropertyId
qualifierP459 = Id.propertyId "P459"

qualifierP518 : Id.PropertyId
qualifierP518 = Id.propertyId "P518"

qualifierP580 : Id.PropertyId
qualifierP580 = Id.propertyId "P580"

qualifierP582 : Id.PropertyId
qualifierP582 = Id.propertyId "P582"

expectedNatQualifiers : List Id.PropertyId
expectedNatQualifiers =
  qualifierP3831 ∷ qualifierP459 ∷ qualifierP518 ∷ qualifierP580 ∷ qualifierP582 ∷ []

expectedNatReferences : List Id.PropertyId
expectedNatReferences = Ref.p854 ∷ []

record NatClimateBoundedState : Set where
  constructor nat-climate-bounded-state
  field
    sourceProperty : Id.PropertyId
    targetProperty : Id.PropertyId
    boundedCandidateCount : Nat
    widerCandidateCount : Nat
    boundedDisposition : Handoff.MigrationDisposition
    widerDisposition : Handoff.MigrationDisposition
    expectedQualifiers : List Id.PropertyId
    expectedReferences : List Id.PropertyId
    checkedSafeSubsetPresent : Bool
    nextLayer : String
    sourceReference : String
open NatClimateBoundedState public

currentNatClimateState : NatClimateBoundedState
currentNatClimateState =
  nat-climate-bounded-state
    carbonFootprintP5991
    annualGreenhouseGasEmissionsP14143
    53
    188
    Handoff.splitRequired
    Handoff.splitRequired
    expectedNatQualifiers
    expectedNatReferences
    false
    "generic reviewer packets over split-heavy rows using bounded source units and followed-source receipts"
    "SensibLaw docs/planning/wikidata_ontology_group_handoff_nat_lane_20260401.md"

boundedNatIsSplitRequired :
  boundedDisposition currentNatClimateState ≡ Handoff.splitRequired
boundedNatIsSplitRequired = refl

widerNatIsSplitRequired :
  widerDisposition currentNatClimateState ≡ Handoff.splitRequired
widerNatIsSplitRequired = refl

checkedSafeSubsetStillAbsent :
  checkedSafeSubsetPresent currentNatClimateState ≡ false
checkedSafeSubsetStillAbsent = refl

------------------------------------------------------------------------
-- P854 reference shape cross-pollinates directly into native reference
-- semantics, but remains only a source candidate.
------------------------------------------------------------------------

natExampleReferenceSnak : WD.ReferenceSnak
natExampleReferenceSnak =
  WD.referenceSnak Ref.p854 (WD.stringValue "bounded-reference-url")

natP854IsSourceCandidate : Ref.ClassifiedReferenceSnak
natP854IsSourceCandidate = Ref.p854SourceCandidate natExampleReferenceSnak refl

natReferenceRoleExact :
  Ref.role natP854IsSourceCandidate ≡ Ref.sourceCandidate
natReferenceRoleExact = refl

------------------------------------------------------------------------
-- Routing and authority boundaries from the handoff.
------------------------------------------------------------------------

data P5991AlwaysMigratesToP14143 : Set where
data SplitRequiredMeansDirectRewrite : Set where
data CleanQualifierShapeMeansSemanticEquivalence : Set where
data P854PresenceMeansReferenceVerified : Set where
data WikiProjectConsensusMeansDashiPromotion : Set where

p5991DoesNotAlwaysMigrate : P5991AlwaysMigratesToP14143 → ⊥
p5991DoesNotAlwaysMigrate ()

splitRequiredDoesNotMeanDirectRewrite : SplitRequiredMeansDirectRewrite → ⊥
splitRequiredDoesNotMeanDirectRewrite ()

cleanShapeDoesNotMeanSemanticEquivalence : CleanQualifierShapeMeansSemanticEquivalence → ⊥
cleanShapeDoesNotMeanSemanticEquivalence ()

p854PresenceDoesNotVerifyReference : P854PresenceMeansReferenceVerified → ⊥
p854PresenceDoesNotVerifyReference ()

wikiProjectConsensusDoesNotCreateDashiPromotion : WikiProjectConsensusMeansDashiPromotion → ⊥
wikiProjectConsensusDoesNotCreateDashiPromotion ()

record NatClimateHandoffBoundary : Set where
  constructor nat-climate-handoff-boundary
  field
    fullStatementBundleIsReviewUnit : Bool
    splitHeavyRowsStayReviewFirst : Bool
    p854IsSourceCandidate : Bool
    p854CreatesSourceAuthority : Bool
    cleanShapeCreatesSemanticEquivalence : Bool
    directWholePropertyRewrite : Bool

canonicalNatClimateHandoffBoundary : NatClimateHandoffBoundary
canonicalNatClimateHandoffBoundary =
  nat-climate-handoff-boundary true true true false false false
