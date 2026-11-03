{-# OPTIONS --safe #-}
module DASHI.Codec.GenBankComponentOntologyFiniteCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Codec.GenBankLocationFiniteCore as Location

------------------------------------------------------------------------
-- Source-annotation classes, NOT assertions of biological function.
-- INSDC DDBJ/ENA/GenBank Feature Table Definition v11.4 (April 2026).
-- Source creator and parser remain separate provenance owners.
------------------------------------------------------------------------

data FeatureClass : Set where
  sourceMetadata : FeatureClass
  geneAnnotation : FeatureClass
  codingSequenceAnnotation : FeatureClass
  transcriptAnnotation : FeatureClass
  transcriptStructureAnnotation : FeatureClass
  regulatoryAnnotation : FeatureClass
  replicationAnnotation : FeatureClass
  transferOriginAnnotation : FeatureClass
  mobileElementAnnotation : FeatureClass
  repeatAnnotation : FeatureClass
  bindingAnnotation : FeatureClass
  recombinationAnnotation : FeatureClass
  structuralAnnotation : FeatureClass
  unclassifiedAnnotation : FeatureClass

data RepliconContext : Set where
  sourceAnnotatedPlasmid : RepliconContext
  sourceAnnotatedChromosome : RepliconContext
  sourceQualifierConflict : RepliconContext
  unresolvedReplicon : RepliconContext

data MolecularTopology : Set where
  circularTopology : MolecularTopology
  linearTopology : MolecularTopology

record SourceRecordContext : Set where
  constructor sourceRecordContext
  field
    topology : MolecularTopology
    repliconContext : RepliconContext
open SourceRecordContext public

-- Record topology is independent of claimed replicon identity.
-- In particular, one can describe circular DNA without asserting plasmid.
circularUnknownContext : SourceRecordContext
circularUnknownContext = sourceRecordContext circularTopology unresolvedReplicon

circularUnknownHasNoPlasmidClaim :
  repliconContext circularUnknownContext ≡ unresolvedReplicon
circularUnknownHasNoPlasmidClaim = refl

-- Only an explicit source-derived classification may provide this witness.
-- It is *not* proof of successful assembly, replication or mobility.
data PlasmidSourceQualifier : RepliconContext → Set where
  annotatedPlasmid : PlasmidSourceQualifier sourceAnnotatedPlasmid

unknownCircularCannotPromotePlasmid :
  PlasmidSourceQualifier unresolvedReplicon → ⊥
unknownCircularCannotPromotePlasmid ()

conflictCannotPromotePlasmid :
  PlasmidSourceQualifier sourceQualifierConflict → ⊥
conflictCannotPromotePlasmid ()

-- A repeat_region or a misc_feature with a suggestive label is not a
-- mobile_element feature. Subtype interpretation is a separate source step.
data ExplicitMobileFeatureKey : FeatureClass → Set where
  annotatedMobileElement :
    ExplicitMobileFeatureKey mobileElementAnnotation

repeatCannotProveMobileElement :
  ExplicitMobileFeatureKey repeatAnnotation → ⊥
repeatCannotProveMobileElement ()

miscCannotProveMobileElement :
  ExplicitMobileFeatureKey unclassifiedAnnotation → ⊥
miscCannotProveMobileElement ()

codingSequenceCannotProveMobileElement :
  ExplicitMobileFeatureKey codingSequenceAnnotation → ⊥
codingSequenceCannotProveMobileElement ()

-- Source qualifier subtype, not a demonstration of transposition.
data MobileElementSubtype : Set where
  transposonSourceType : MobileElementSubtype
  retrotransposonSourceType : MobileElementSubtype
  integronSourceType : MobileElementSubtype
  insertionSequenceSourceType : MobileElementSubtype
  nonLTRRetrotransposonSourceType : MobileElementSubtype
  sineSourceType : MobileElementSubtype
  miteSourceType : MobileElementSubtype
  lineSourceType : MobileElementSubtype
  otherSourceType : MobileElementSubtype
  unresolvedMobileSubtype : MobileElementSubtype

-- A typed feature owns its original location, rather than a new
-- biological sequence. Complement/rotation of locations requires a
-- separate source-coordinate commuting-square proof.
record SourceComponent : Set where
  constructor sourceComponent
  field
    sourceFeatureIndex : Nat
    sourceFeatureClass : FeatureClass
    sourceLocation : Location.Location
    sourceKeyText : String
    sourceReopenRef : String
open SourceComponent public

-- The biology-level non-Golden adapter reuses DNAFirstFormalism.
-- This standalone --safe core does not import a potentially non-safe owner.

-- A candidate source annotation does not supply stronger experimental
-- authority. The absence of a constructor blocks accidental conversion.
data SourceAnnotationProvesBiologicalFunction : Set where

data SourceAnnotationAuthorizesOntologyEdit : Set where

annotationCannotProveFunction :
  SourceAnnotationProvesBiologicalFunction → ⊥
annotationCannotProveFunction ()

annotationCannotAuthorizeOntologyEdit :
  SourceAnnotationAuthorizesOntologyEdit → ⊥
annotationCannotAuthorizeOntologyEdit ()
