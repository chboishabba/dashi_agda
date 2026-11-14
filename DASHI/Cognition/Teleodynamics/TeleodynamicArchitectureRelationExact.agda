module DASHI.Cognition.Teleodynamics.TeleodynamicArchitectureRelationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy
import DASHI.Cognition.Teleodynamics.TeleodynamicsPrincipiaTwoExact as T

------------------------------------------------------------------------
-- TELEODYNAMIC ARCHITECTURE RELATION
--
-- Principia-II writes one cosine-like architectural similarity.  DASHI lifts
-- that scalar into the existing task-relative relation/representation framework:
-- representation family, comparison geometry, held consumer scope, dynamic
-- trace safety, and realization remain independent obligations.
------------------------------------------------------------------------

record TeleodynamicArchitectureRelation : Set where
  constructor teleodynamicArchitectureRelation
  field
    sourceSimilarityLabel : String
    representationFamilyLabel : String
    comparisonGeometryLabel : String
    consumerScopeLabel : String
    dynamicTraceLabel : String
    realizationLabel : String

record ArchitectureRelationBoundary : Set where
  constructor architectureRelationBoundary
  field
    cosineIsPermittedCandidateGeometry : Bool
    similaritySelectsOntology : Bool
    oneConsumerClosesAllConsumers : Bool
    staticFitProvesDynamicSafety : Bool
    architectureSimilarityProvesPhysicalCoupling : Bool

open ArchitectureRelationBoundary public

canonicalArchitectureRelationBoundary : ArchitectureRelationBoundary
canonicalArchitectureRelationBoundary =
  architectureRelationBoundary true false false false false

canonicalTeleodynamicArchitectureRelation : TeleodynamicArchitectureRelation
canonicalTeleodynamicArchitectureRelation =
  teleodynamicArchitectureRelation
    "Principia-II normalized Frobenius/cosine-like architecture similarity"
    "declared relation representation family"
    "declared comparison geometry"
    "declared consumer family"
    "dynamic trace obligation"
    "target realization obligation"
