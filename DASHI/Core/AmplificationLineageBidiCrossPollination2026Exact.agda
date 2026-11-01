module DASHI.Core.AmplificationLineageBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Culture.CulturalInstitutionalAmplificationCoreExact as CultureAmp
import DASHI.Biology.DrosophilaSameTrialProvenanceDependenceExact as FlyDep

data LineageEdgeKind : Set where
  generatedFrom : LineageEdgeKind
  transformedBy : LineageEdgeKind
  selectedBy : LineageEdgeKind
  fundedBy : LineageEdgeKind
  circulatedBy : LineageEdgeKind
  reportedBy : LineageEdgeKind
  verifiedBy : LineageEdgeKind
  amplifiedBy : LineageEdgeKind

record LineageNode : Set where
  constructor lineage-node
  field nodeID objectReference : String
open LineageNode public

record LineageEdge (source target : LineageNode) : Set where
  constructor lineage-edge
  field edgeKind : LineageEdgeKind
        receiptReference : String
open LineageEdge public

record SharedRootWitness (left right : LineageNode) : Set where
  constructor shared-root-witness
  field root : LineageNode
        leftPathReference rightPathReference : String
open SharedRootWitness public

record IndependenceReceipt (left right : LineageNode) : Set where
  constructor independence-receipt
  field provenanceAuditReference : String
        noSharedRelevantRoot : Bool
        noSharedRelevantRootIsTrue : noSharedRelevantRoot ≡ true
open IndependenceReceipt public

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
manyDescendantsDoNotMeanManyIndependentProducers : ManyDescendantsMeanManyIndependentProducers → ⊥
manyDescendantsDoNotMeanManyIndependentProducers ()

record ExperimentalDependenceLineage : Set where
  constructor experimental-dependence-lineage
  field relation : FlyDep.EvidenceRelation
        provenanceReference : String
        independenceNeedsSeparateClosure : Bool
        independenceNeedsSeparateClosureIsTrue : independenceNeedsSeparateClosure ≡ true
open ExperimentalDependenceLineage public

record AmplificationLineageBoundary : Set where
  constructor amplification-lineage-boundary
  field edgeKindMatters amplificationDistinctFromGeneration reportingDistinctFromVerification visibilityCountDistinctFromIndependentProducerCount : Bool

canonicalAmplificationLineageBoundary : AmplificationLineageBoundary
canonicalAmplificationLineageBoundary = amplification-lineage-boundary true true true true
