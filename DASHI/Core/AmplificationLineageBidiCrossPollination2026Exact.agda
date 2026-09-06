module DASHI.Core.AmplificationLineageBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Culture.CulturalInstitutionalAmplificationCoreExact as CultureAmp
import DASHI.Biology.DrosophilaSameTrialProvenanceDependenceExact as FlyDep

------------------------------------------------------------------------
-- AMPLIFICATION LINEAGE -- BIDI CROSS-POLLINATION
--
-- DASHI extension.  Donor authority:
--   CulturalInstitutionalAmplificationCoreExact (merged PR #698)
--   DrosophilaSameTrialProvenanceDependenceExact
--     repository commit da7fb693c3ba0cc38346779c8632a852e6006c39.
--
-- The cross-pollination is structural: downstream visibility/impact can be
-- amplified without generating the upstream object, while multiple visible
-- descendants may share one provenance root and therefore fail to constitute
-- independent replication.
------------------------------------------------------------------------

data LineageEdgeKind : Set where
  generatedFrom transformedBy selectedBy fundedBy circulatedBy reportedBy verifiedBy amplifiedBy : LineageEdgeKind

record LineageNode : Set where
  constructor lineage-node
  field
    nodeID : String
    objectReference : String

open LineageNode public

record LineageEdge (source target : LineageNode) : Set where
  constructor lineage-edge
  field
    edgeKind : LineageEdgeKind
    receiptReference : String

open LineageEdge public

record SharedRootWitness (left right : LineageNode) : Set where
  constructor shared-root-witness
  field
    root : LineageNode
    leftPathReference : String
    rightPathReference : String

open SharedRootWitness public

record IndependenceReceipt (left right : LineageNode) : Set where
  constructor independence-receipt
  field
    provenanceAuditReference : String
    noSharedRelevantRoot : Bool
    noSharedRelevantRootIsTrue : noSharedRelevantRoot ≡ true

open IndependenceReceipt public

------------------------------------------------------------------------
-- Edge semantics are not interchangeable.
------------------------------------------------------------------------

data AmplifiedMeansGenerated : Set where
data ReportedMeansVerified : Set where
data SameRootMeansIndependent : Set where
data ManyDescendantsMeanManyIndependentProducers : Set where

amplifiedDoesNotMeanGenerated : AmplifiedMeansGenerated → ⊥
amplifiedDoesNotMeanGenerated ()

reportedDoesNotMeanVerified : ReportedMeansVerified → ⊥
reportedDoesNotMeanVerified ()

sameRootDoesNotMeanIndependent : SameRootMeansIndependent → ⊥
sameRootDoesNotMeanIndependent ()

manyDescendantsDoNotMeanManyIndependentProducers :
  ManyDescendantsMeanManyIndependentProducers → ⊥
manyDescendantsDoNotMeanManyIndependentProducers ()

------------------------------------------------------------------------
-- Donor adapters keep the lineage reading explicit without identifying the
-- domain carriers.
------------------------------------------------------------------------

record CulturalAmplificationLineage : Set₁ where
  constructor cultural-amplification-lineage
  field
    workReference : String
    donorReading : String
    amplificationDoesNotCreateWork : Bool
    amplificationDoesNotCreateWorkIsTrue : amplificationDoesNotCreateWork ≡ true

record ExperimentalDependenceLineage : Set where
  constructor experimental-dependence-lineage
  field
    relation : FlyDep.EvidenceRelation
    provenanceReference : String
    independenceNeedsSeparateClosure : Bool
    independenceNeedsSeparateClosureIsTrue : independenceNeedsSeparateClosure ≡ true

open CulturalAmplificationLineage public
open ExperimentalDependenceLineage public

record AmplificationLineageBoundary : Set where
  constructor amplification-lineage-boundary
  field
    edgeKindMatters : Bool
    amplificationDistinctFromGeneration : Bool
    reportingDistinctFromVerification : Bool
    visibilityCountDistinctFromIndependentProducerCount : Bool

canonicalAmplificationLineageBoundary : AmplificationLineageBoundary
canonicalAmplificationLineageBoundary =
  amplification-lineage-boundary true true true true
