module DASHI.Governance.ObservationRelativeReificationRegressionExact where

------------------------------------------------------------------------
-- FINITE REGRESSION: COLLISION ALONE IS NOT REIFICATION
--
-- Two fine causal edges are intentionally compressed to one coarse edge.
-- Under a query language that observes the same result on both, the compression
-- is query-safe even though the raw edge map is non-injective.  Under a richer
-- query language that separates the two edges, the SAME compression carries an
-- observation-relevant reification loss and cannot be query-safe.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.CausalResolutionExact as Resolution
import DASHI.Governance.FutureSafeCausalCompressionExact as Compression

------------------------------------------------------------------------
-- Fine/coarse graphs.
------------------------------------------------------------------------

data FineNode : Set where f0 f1 : FineNode
data FineEdge : Set where leftMechanism rightMechanism : FineEdge

fineSource : FineEdge → FineNode
fineSource leftMechanism = f0
fineSource rightMechanism = f0

fineTarget : FineEdge → FineNode
fineTarget leftMechanism = f1
fineTarget rightMechanism = f1

fineGraph : Resolution.CausalGraph
fineGraph = record
  { Node = FineNode
  ; Edge = FineEdge
  ; source = fineSource
  ; target = fineTarget
  }

data CoarseNode : Set where c0 c1 : CoarseNode
data CoarseEdge : Set where compressedMechanism : CoarseEdge

coarseSource : CoarseEdge → CoarseNode
coarseSource compressedMechanism = c0

coarseTarget : CoarseEdge → CoarseNode
coarseTarget compressedMechanism = c1

coarseGraph : Resolution.CausalGraph
coarseGraph = record
  { Node = CoarseNode
  ; Edge = CoarseEdge
  ; source = coarseSource
  ; target = coarseTarget
  }

nodeMap : FineNode → CoarseNode
nodeMap f0 = c0
nodeMap f1 = c1

edgeMap : FineEdge → CoarseEdge
edgeMap leftMechanism = compressedMechanism
edgeMap rightMechanism = compressedMechanism

compression : Resolution.GraphCompression fineGraph coarseGraph
compression = record
  { nodeMap = nodeMap
  ; edgeMap = edgeMap
  ; sourceCommutes = λ edge → refl
  ; targetCommutes = λ edge → refl
  }

mechanismsDistinct : leftMechanism ≡ rightMechanism → ⊥
mechanismsDistinct ()

structuralCollision :
  Resolution.ReificationLoss fineGraph coarseGraph compression
structuralCollision = record
  { leftEdge = leftMechanism
  ; rightEdge = rightMechanism
  ; edgesDistinct = mechanismsDistinct
  ; compressedTogether = refl
  }

------------------------------------------------------------------------
-- Coarse query language: both fine mechanisms answer the declared question in
-- exactly the same way.  The collision is therefore harmless relative to this
-- query language.
------------------------------------------------------------------------

data CoarseQuery : Set where operationalOutcome : CoarseQuery
data SameResult : Set where sameResult : SameResult

coarseObserve : CoarseQuery → FineEdge → SameResult
coarseObserve operationalOutcome leftMechanism = sameResult
coarseObserve operationalOutcome rightMechanism = sameResult

coarseLanguage : Compression.EdgeQueryLanguage fineGraph
coarseLanguage =
  Compression.edgeQueryLanguage CoarseQuery SameResult coarseObserve

coarseCompressionSafe :
  Compression.QuerySafeCompression
    fineGraph coarseGraph compression coarseLanguage
coarseCompressionSafe =
  Compression.querySafeCompression
    (λ collision query → refl)

rawCollisionCanStillBeQuerySafe :
  Resolution.ReificationLoss fineGraph coarseGraph compression
rawCollisionCanStillBeQuerySafe = structuralCollision

------------------------------------------------------------------------
-- Rich query language: one admissible question separates the mechanisms.
------------------------------------------------------------------------

data RichQuery : Set where mechanismIdentity : RichQuery
data RichResult : Set where leftResult rightResult : RichResult

richObserve : RichQuery → FineEdge → RichResult
richObserve mechanismIdentity leftMechanism = leftResult
richObserve mechanismIdentity rightMechanism = rightResult

richLanguage : Compression.EdgeQueryLanguage fineGraph
richLanguage =
  Compression.edgeQueryLanguage RichQuery RichResult richObserve

richObservationRelevantLoss :
  Compression.ObservationRelevantReificationLoss
    fineGraph coarseGraph compression richLanguage
richObservationRelevantLoss =
  Compression.observationRelevantReificationLoss
    structuralCollision
    mechanismIdentity
    (λ ())

richQuerySafetyImpossible :
  Compression.QuerySafeCompression
    fineGraph coarseGraph compression richLanguage →
  ⊥
richQuerySafetyImpossible safe =
  Compression.querySafeCompressionExcludesRelevantReificationLoss
    safe richObservationRelevantLoss

------------------------------------------------------------------------
-- Exact lesson: the same graph compression can be safe for one declared query
-- language and information-losing for another.  Reification is therefore
-- observation/query relative rather than identical to non-injectivity alone.
------------------------------------------------------------------------
