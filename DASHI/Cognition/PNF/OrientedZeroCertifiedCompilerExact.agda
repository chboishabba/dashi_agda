module DASHI.Cognition.PNF.OrientedZeroCertifiedCompilerExact where

open import DASHI.Core.Prelude
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

import DASHI.Cognition.PNF.OrientedZeroCanonicalFutureExact as Canonical
import DASHI.Cognition.PNF.OrientedZeroCanonicalPartitionPresentationExact as Presentation
import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave
import DASHI.Core.CertifiedFiniteFutureQuotientCompilerExact as Compiler
import DASHI.Core.FiniteRankedRefinementStabilizationExact as Ranked
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge

------------------------------------------------------------------------
-- EXECUTABLE TWO-STAGE PARTITION CODE
------------------------------------------------------------------------

data PartitionCode : Set where
  scalarPartition orientedPartition : PartitionCode

advanceCode : PartitionCode → PartitionCode
advanceCode scalarPartition = orientedPartition
advanceCode orientedPartition = orientedPartition

stableCode? : (code : PartitionCode) → Dec (code ≡ advanceCode code)
stableCode? scalarPartition = no λ()
stableCode? orientedPartition = yes refl

blockRank : PartitionCode → Nat
blockRank scalarPartition = 3
blockRank orientedPartition = 4

rankBounded : (code : PartitionCode) → blockRank code ≤ 4
rankBounded scalarPartition = s≤s (s≤s (s≤s z≤n))
rankBounded orientedPartition = ≤-refl

unstableRaisesBlockRank :
  (code : PartitionCode) →
  (code ≡ advanceCode code → ⊥) →
  blockRank code < blockRank (advanceCode code)
unstableRaisesBlockRank scalarPartition unstable =
  s≤s (s≤s (s≤s (s≤s z≤n)))
unstableRaisesBlockRank orientedPartition unstable =
  ⊥-elim (unstable refl)

rankedPartitionProcess : Ranked.RankedRefinementProcess
rankedPartitionProcess = Ranked.rankedRefinementProcess
  PartitionCode
  advanceCode
  stableCode?
  blockRank
  4
  rankBounded
  unstableRaisesBlockRank

partitionRelation :
  PartitionCode → Wave.Wave4 → Wave.Wave4 → Set
partitionRelation scalarPartition =
  Refinement.RefinesToDepth 0 Wave.scalar Presentation.step
partitionRelation orientedPartition =
  Refinement.RefinesToDepth 1 Wave.scalar Presentation.step

initialCorrect :
  (left right : Wave.Wave4) →
  Compiler.RelationIff
    (partitionRelation scalarPartition left right)
    (Refinement.RefinesToDepth 0 Wave.scalar Presentation.step left right)
initialCorrect left right = Compiler.relationIff (λ x → x) (λ x → x)

advanceCorrect :
  (code : PartitionCode) →
  (left right : Wave.Wave4) →
  Compiler.RelationIff
    (partitionRelation (advanceCode code) left right)
    (Compiler.RefineOnce Wave.scalar Presentation.step
      (partitionRelation code) left right)
advanceCorrect scalarPartition left right =
  Compiler.relationIff (λ x → x) (λ x → x)
advanceCorrect orientedPartition left right =
  Compiler.relationIff
    (Refinement.forwardStable Presentation.orientedZeroStableAtDepthOne)
    (Refinement.backwardStable Presentation.orientedZeroStableAtDepthOne)

orientedZeroCompiler :
  Compiler.CertifiedPartitionRefiner
    Wave.Wave4 Canonical.Action Wave.Scalar3
orientedZeroCompiler = Compiler.certifiedPartitionRefiner
  Wave.scalar
  Presentation.step
  Presentation.label
  rankedPartitionProcess
  scalarPartition
  partitionRelation
  initialCorrect
  advanceCorrect

compiledOrientedZeroQuotient : Compiler.CompiledFutureQuotient orientedZeroCompiler
compiledOrientedZeroQuotient = Compiler.compileFutureQuotient orientedZeroCompiler

compilerFindsDepthOne :
  Compiler.stableDepth compiledOrientedZeroQuotient ≡ 1
compilerFindsDepthOne = refl

compilerReturnsCanonicalFutureExactness :
  (left right : Wave.Wave4) →
  (Refinement.RefinesToDepth
      (Compiler.stableDepth compiledOrientedZeroQuotient)
      Wave.scalar Presentation.step left right →
    Future.FutureObservationEquivalent
      (Bridge.deterministicSystem Presentation.step Presentation.label)
      Wave.scalar left right)
  ×
  (Future.FutureObservationEquivalent
      (Bridge.deterministicSystem Presentation.step Presentation.label)
      Wave.scalar left right →
    Refinement.RefinesToDepth
      (Compiler.stableDepth compiledOrientedZeroQuotient)
      Wave.scalar Presentation.step left right)
compilerReturnsCanonicalFutureExactness =
  Compiler.canonicalExact compiledOrientedZeroQuotient
