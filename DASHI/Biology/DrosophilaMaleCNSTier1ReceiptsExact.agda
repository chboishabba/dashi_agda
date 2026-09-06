module DASHI.Biology.DrosophilaMaleCNSTier1ReceiptsExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Runtime-generated authority receipts for canonical MaleCNS v1.0 Tier 1.
-- These are artifact/schema facts, not biological theorems.
------------------------------------------------------------------------

record Tier1ArtifactReceipt : Set where
  constructor tier1ArtifactReceipt
  field
    artifactKey : String
    exactFilename : String
    byteSize : Nat
    sha256 : String
    rowCount : Nat
    columnCount : Nat
    sourceAuthorOrConsortium : String
    sourceTitle : String
    sourceStableIdentifier : String
    hashVerifiedByRuntime : Bool

open Tier1ArtifactReceipt public

weightsReceipt : Tier1ArtifactReceipt
weightsReceipt = tier1ArtifactReceipt
  "connectome_weights_significant"
  "connectome-weights-male-cns-v1.0-minconf-0.5-significant-only.feather"
  502169298
  "5c536423a62a688e59e7b441f9c04d6272c9a1f017e35814cf561f8c275d9e9e"
  25568639
  5
  "Berg et al."
  "Sexual dimorphism in the complete Drosophila male central nervous system connectome"
  "doi:10.1016/j.cell.2026.08.015"
  true

annotationsReceipt : Tier1ArtifactReceipt
annotationsReceipt = tier1ArtifactReceipt
  "body_annotations"
  "body-annotations-male-cns-v1.0-minconf-0.5.feather"
  14483314
  "2177e246113e4cfbf1e7772ec37c6da1955ff22e8063d0b1f833101f99a9a3b2"
  211577
  36
  "Berg et al."
  "Sexual dimorphism in the complete Drosophila male central nervous system connectome"
  "doi:10.1016/j.cell.2026.08.015"
  true

neurotransmitterReceipt : Tier1ArtifactReceipt
neurotransmitterReceipt = tier1ArtifactReceipt
  "body_neurotransmitters"
  "body-neurotransmitters-male-cns-v1.0.feather"
  43282834
  "95c9289220663abeb3409f3ad9e5a7f8a53f8093f5139d15502cd08da8879621"
  1835518
  10
  "Berg et al."
  "Sexual dimorphism in the complete Drosophila male central nervous system connectome"
  "doi:10.1016/j.cell.2026.08.015"
  true

canonicalTier1Receipts : List Tier1ArtifactReceipt
canonicalTier1Receipts = weightsReceipt ∷ annotationsReceipt ∷ neurotransmitterReceipt ∷ []

record MaleCNSSchemaReading : Set where
  constructor maleCNSSchemaReading
  field
    structuralPreColumn : String
    structuralPostColumn : String
    structuralWeightColumn : String
    typePreColumn : String
    typePostColumn : String
    annotationIDColumn : String
    biologicalCoarseRegionColumn : String
    superclassColumn : String
    classColumn : String
    subclassColumn : String
    transmitterBodyColumn : String
    transmitterPredictionColumn : String
    transmitterConsensusColumn : String

open MaleCNSSchemaReading public

maleCNSv1Schema : MaleCNSSchemaReading
maleCNSv1Schema = maleCNSSchemaReading
  "body_pre"
  "body_post"
  "weight"
  "type_pre"
  "type_post"
  "bodyId"
  "somaNeuromere"
  "superclass"
  "class"
  "subclass"
  "body"
  "predicted_nt"
  "consensus_nt"

record Tier1Boundary : Set where
  constructor tier1Boundary
  field
    somaNeuromereIsCoarseBiologicalGroupingNotNeuronIdentity : Bool
    transmitterSignIsModelFeatureNotReceptorResolvedPhysiology : Bool
    runtimeHashReceiptDoesNotProveDownstreamBenchmark : Bool
    tier1VerificationDoesNotVerifyFunctionalOrRegistrationTiers : Bool

canonicalTier1Boundary : Tier1Boundary
canonicalTier1Boundary = tier1Boundary true true true true
