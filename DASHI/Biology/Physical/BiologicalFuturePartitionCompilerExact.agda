module DASHI.Biology.Physical.BiologicalFuturePartitionCompilerExact where

------------------------------------------------------------------------
-- AN ACTUAL INSTANCE OF THE CANONICAL FINITE FUTURE QUOTIENT COMPILER
--
-- The selected observer is the five-coordinate history-sensitive coarse
-- biological code, NOT morphology alone.  Its kernel is stable at depth 0:
-- the named interventions act on that code without needing the omitted
-- synthetic chromatin marker.  This does not claim minimality of the
-- morphology-only quotient, nor physical validation of the fixture.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.CertifiedFiniteFutureQuotientCompilerExact as Compiler
import DASHI.Core.FiniteRankedRefinementStabilizationExact as Ranked
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge

stableBiologicalCodeAtZero :
  Refinement.StableAt 0 Bio.project Bio.step
stableBiologicalCodeAtZero =
  Refinement.stableAt preserve Refinement.refinementMonotone
  where
    preserve :
      ∀ {left right} →
      Refinement.RefinesToDepth 0 Bio.project Bio.step left right →
      Refinement.RefinesToDepth 1 Bio.project Bio.step left right
    preserve {left} {right} same =
      same , λ a →
        trans
          (Bio.projectionCommutes a left)
          (trans
            (cong (Bio.coarseStep a) same)
            (sym (Bio.projectionCommutes a right)))

data PartitionCode : Set where
  stableCode : PartitionCode

advanceCode : PartitionCode → PartitionCode
advanceCode stableCode = stableCode

stableCode? : (code : PartitionCode) → Dec (code ≡ advanceCode code)
stableCode? stableCode = yes refl

rankCode : PartitionCode → Nat
rankCode stableCode = 1

boundedRank : (code : PartitionCode) → rankCode code ≤ 1
boundedRank stableCode = ≤-refl

noUnstableCode :
  (code : PartitionCode) →
  (code ≡ advanceCode code → ⊥) →
  rankCode code < rankCode (advanceCode code)
noUnstableCode stableCode unstable = ⊥-elim (unstable refl)

partitionProcess : Ranked.RankedRefinementProcess
partitionProcess =
  Ranked.rankedRefinementProcess
    PartitionCode advanceCode stableCode? rankCode 1
    boundedRank noUnstableCode

partitionRelation :
  PartitionCode → Bio.BiologicalState → Bio.BiologicalState → Set
partitionRelation stableCode =
  Refinement.RefinesToDepth 0 Bio.project Bio.step

biologicalCompiler :
  Compiler.CertifiedPartitionRefiner
    Bio.BiologicalState Bio.Intervention Bio.FutureSufficientCode
biologicalCompiler =
  Compiler.certifiedPartitionRefiner
    Bio.project Bio.step Bio.actionLabel
    partitionProcess stableCode partitionRelation
    (λ left right → Compiler.relationIff (λ x → x) (λ x → x))
    (λ code left right →
      Compiler.relationIff
        (Refinement.forwardStable stableBiologicalCodeAtZero)
        (Refinement.backwardStable stableBiologicalCodeAtZero))

compiledBiologicalCode :
  Compiler.CompiledFutureQuotient biologicalCompiler
compiledBiologicalCode = Compiler.compileFutureQuotient biologicalCompiler

compilerStabilizesAtZero :
  Compiler.stableDepth compiledBiologicalCode ≡ 0
compilerStabilizesAtZero = refl

compiledCodeExactlyCapturesFutureLanguage :
  (left right : Bio.BiologicalState) →
  (Bio.project left ≡ Bio.project right →
    Future.FutureObservationEquivalent
      (Bridge.deterministicSystem Bio.step Bio.actionLabel)
      Bio.project left right)
  ×
  (Future.FutureObservationEquivalent
      (Bridge.deterministicSystem Bio.step Bio.actionLabel)
      Bio.project left right →
    Bio.project left ≡ Bio.project right)
compiledCodeExactlyCapturesFutureLanguage left right =
  Compiler.canonicalExact compiledBiologicalCode left right

-- Real science still needs a biology-specific observation and update law.
-- For example the morphology-only observation has a strictly larger kernel,
-- and the compiler above does not declare that coarser kernel future-safe.
