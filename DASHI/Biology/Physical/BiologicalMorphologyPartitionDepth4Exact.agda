module DASHI.Biology.Physical.BiologicalMorphologyPartitionDepth4Exact where

------------------------------------------------------------------------
-- P1: THE ACTUAL MORPHOLOGY OBSERVER, NOT A PRESELECTED SAFE CODE.
--
-- The canonical finite partition refiner starts from CURRENT morphology
-- and advances through 0,1,2,3,4 intervention steps. At depth four,
-- five explicit diagnostic histories recover the 18-class minimal code.
-- The rank-bounded refinement process terminates at this true fixed point.
--
-- All proof statements are for the finite Boolean intervention fixture.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Biology.Physical.BiologicalMinimalMorphologyFutureQuotientExact as Mini
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge
import DASHI.Core.CertifiedFiniteFutureQuotientCompilerExact as Compiler
import DASHI.Core.FiniteRankedRefinementStabilizationExact as Ranked
import DASHI.Core.FutureObservationLanguageQuotientExact as Future

depthFourPresent :
  ∀ {left right} →
  Refinement.RefinesToDepth 4 Bio.observe Bio.step left right →
  Mini.readTrace [] left ≡ Mini.readTrace [] right
depthFourPresent related =
  Refinement.traceObservationFromDepth []
    (Bridge.dropLeadingDepth 4 0 related)

depthFourGenome :
  ∀ {left right} →
  Refinement.RefinesToDepth 4 Bio.observe Bio.step left right →
  Mini.readTrace Mini.genomeWord left ≡ Mini.readTrace Mini.genomeWord right
depthFourGenome related =
  Refinement.traceObservationFromDepth Mini.genomeWord
    (Bridge.dropLeadingDepth 0 4 related)

depthFourMemory :
  ∀ {left right} →
  Refinement.RefinesToDepth 4 Bio.observe Bio.step left right →
  Mini.readTrace Mini.memoryWord left ≡ Mini.readTrace Mini.memoryWord right
depthFourMemory related =
  Refinement.traceObservationFromDepth Mini.memoryWord
    (Bridge.dropLeadingDepth 1 3 related)

depthFourJunction :
  ∀ {left right} →
  Refinement.RefinesToDepth 4 Bio.observe Bio.step left right →
  Mini.readTrace Mini.junctionWord left ≡ Mini.readTrace Mini.junctionWord right
depthFourJunction related =
  Refinement.traceObservationFromDepth Mini.junctionWord
    (Bridge.dropLeadingDepth 1 3 related)

depthFourEnvironment :
  ∀ {left right} →
  Refinement.RefinesToDepth 4 Bio.observe Bio.step left right →
  Mini.readTrace Mini.environmentWord left
    ≡ Mini.readTrace Mini.environmentWord right
depthFourEnvironment related =
  Refinement.traceObservationFromDepth Mini.environmentWord
    (Bridge.dropLeadingDepth 1 3 related)

depthFourDeterminesDiagnostic :
  ∀ {left right} →
  Refinement.RefinesToDepth 4 Bio.observe Bio.step left right →
  Mini.diagnosticOf left ≡ Mini.diagnosticOf right
depthFourDeterminesDiagnostic related
  rewrite depthFourPresent related
        | depthFourGenome related
        | depthFourMemory related
        | depthFourJunction related
        | depthFourEnvironment related = refl

depthFourExactlyDeterminesMinimalCode :
  ∀ {left right} →
  Refinement.RefinesToDepth 4 Bio.observe Bio.step left right →
  Mini.minimalProject left ≡ Mini.minimalProject right
depthFourExactlyDeterminesMinimalCode {left} {right} related =
  trans
    (sym (Mini.diagnosticRecoversCode left))
    (trans
      (cong Mini.decodeDiagnostic
        (depthFourDeterminesDiagnostic related))
      (Mini.diagnosticRecoversCode right))

minimalCodeAlreadyRelatedAtDepthFour :
  ∀ {left right} →
  Mini.minimalProject left ≡ Mini.minimalProject right →
  Refinement.RefinesToDepth 4 Bio.observe Bio.step left right
minimalCodeAlreadyRelatedAtDepthFour same =
  Bridge.traceEquivalentImpliesEveryDepth
    (Mini.minimalCodeImpliesTraceEquivalence same) 4

-- A genuine fixed point of the original morphology-observer refinement,
-- not of the stronger five-coordinate observer from the first compiler.
morphologyStableAtDepthFour :
  Refinement.StableAt 4 Bio.observe Bio.step
morphologyStableAtDepthFour =
  Refinement.stableAt
    (λ {left} {right} related →
      Bridge.traceEquivalentImpliesEveryDepth
        (Mini.minimalCodeImpliesTraceEquivalence
          (depthFourExactlyDeterminesMinimalCode related)) 5)
    Refinement.refinementMonotone

data MorphologyPartitionStage : Set where
  d0 d1 d2 d3 d4 : MorphologyPartitionStage

advanceStage : MorphologyPartitionStage → MorphologyPartitionStage
advanceStage d0 = d1
advanceStage d1 = d2
advanceStage d2 = d3
advanceStage d3 = d4
advanceStage d4 = d4

stageStable? :
  (stage : MorphologyPartitionStage) →
  Dec (stage ≡ advanceStage stage)
stageStable? d0 = no (λ ())
stageStable? d1 = no (λ ())
stageStable? d2 = no (λ ())
stageStable? d3 = no (λ ())
stageStable? d4 = yes refl

stageDepth : MorphologyPartitionStage → Nat
stageDepth d0 = 0
stageDepth d1 = 1
stageDepth d2 = 2
stageDepth d3 = 3
stageDepth d4 = 4

depthBounded : (stage : MorphologyPartitionStage) → stageDepth stage ≤ 4
depthBounded d0 = z≤n
depthBounded d1 = s≤s z≤n
depthBounded d2 = s≤s (s≤s z≤n)
depthBounded d3 = s≤s (s≤s (s≤s z≤n))
depthBounded d4 = ≤-refl

unstableStageRaisesRank :
  (stage : MorphologyPartitionStage) →
  (stage ≡ advanceStage stage → ⊥) →
  stageDepth stage < stageDepth (advanceStage stage)
unstableStageRaisesRank d0 unstable = ≤-refl
unstableStageRaisesRank d1 unstable = ≤-refl
unstableStageRaisesRank d2 unstable = ≤-refl
unstableStageRaisesRank d3 unstable = ≤-refl
unstableStageRaisesRank d4 unstable = ⊥-elim (unstable refl)

morphologyPartitionProcess : Ranked.RankedRefinementProcess
morphologyPartitionProcess =
  Ranked.rankedRefinementProcess
    MorphologyPartitionStage
    advanceStage
    stageStable?
    stageDepth
    4
    depthBounded
    unstableStageRaisesRank

stageRelation :
  MorphologyPartitionStage →
  Bio.BiologicalState → Bio.BiologicalState → Set
stageRelation stage =
  Refinement.RefinesToDepth (stageDepth stage) Bio.observe Bio.step

morphologyCompiler :
  Compiler.CertifiedPartitionRefiner
    Bio.BiologicalState Bio.Intervention Bool
morphologyCompiler =
  Compiler.certifiedPartitionRefiner
    Bio.observe Bio.step Bio.actionLabel
    morphologyPartitionProcess d0 stageRelation
    (λ left right → Compiler.relationIff (λ x → x) (λ x → x))
    advanceCorrect
  where
    advanceCorrect :
      (stage : MorphologyPartitionStage) →
      (left right : Bio.BiologicalState) →
      Compiler.RelationIff
        (stageRelation (advanceStage stage) left right)
        (Compiler.RefineOnce Bio.observe Bio.step
          (stageRelation stage) left right)
    advanceCorrect d0 left right =
      Compiler.relationIff (λ x → x) (λ x → x)
    advanceCorrect d1 left right =
      Compiler.relationIff (λ x → x) (λ x → x)
    advanceCorrect d2 left right =
      Compiler.relationIff (λ x → x) (λ x → x)
    advanceCorrect d3 left right =
      Compiler.relationIff (λ x → x) (λ x → x)
    advanceCorrect d4 left right =
      Compiler.relationIff
        (Refinement.forwardStable morphologyStableAtDepthFour)
        (Refinement.backwardStable morphologyStableAtDepthFour)

compiledOriginalMorphologyQuotient :
  Compiler.CompiledFutureQuotient morphologyCompiler
compiledOriginalMorphologyQuotient =
  Compiler.compileFutureQuotient morphologyCompiler

-- Depth 4 is a selected exact fixed point. It is independently witnessed
-- by a four-action genome diagnostic, rather than a rank-bound guess.
morphologyCompilerStopsAtFour :
  Compiler.stableDepth compiledOriginalMorphologyQuotient ≡ 4
morphologyCompilerStopsAtFour = refl

originalMorphologyFutureIsCertified :
  (left right : Bio.BiologicalState) →
  (Refinement.RefinesToDepth
     (Compiler.stableDepth compiledOriginalMorphologyQuotient)
     Bio.observe Bio.step left right →
   Future.FutureObservationEquivalent
     (Bridge.deterministicSystem Bio.step Bio.actionLabel)
     Bio.observe left right)
  ×
  (Future.FutureObservationEquivalent
     (Bridge.deterministicSystem Bio.step Bio.actionLabel)
     Bio.observe left right →
   Refinement.RefinesToDepth
     (Compiler.stableDepth compiledOriginalMorphologyQuotient)
     Bio.observe Bio.step left right)
originalMorphologyFutureIsCertified left right =
  Compiler.canonicalExact compiledOriginalMorphologyQuotient left right
