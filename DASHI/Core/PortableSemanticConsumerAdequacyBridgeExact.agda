module DASHI.Core.PortableSemanticConsumerAdequacyBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.PortableSemanticInterpretationExact as Portable
import DASHI.Core.PortableLoopInterpretationExact as Loop

------------------------------------------------------------------------
-- REUSE EXISTING ADMISSIBILITY / CONSUMER-ADEQUACY STRATUM
--
-- Semantic refinement discharges the consumer-adequacy gate for the declared
-- query.  Ranking remains downstream in the existing MDL/Pareto calculus.
------------------------------------------------------------------------

loopBackendSelectionProblem : MDL.ConsumerMDLProblem
loopBackendSelectionProblem =
  MDL.consumerMDLProblem
    Loop.LoopBackend
    (λ _ → ⊤)
    (λ backend →
      Portable.SemanticRefinement
        Loop.loopProblem backend Loop.canonicalInput tt)
    descriptionLength
    (λ _ _ → ⊤)
    backendReference
    "synthetic backend-description coordinate; not runtime cost"
    "canonical exact finite loop-result consumer"
  where
    descriptionLength : Loop.LoopBackend → Nat
    descriptionLength Loop.jsSequential = 1
    descriptionLength Loop.gpuParallel = 2

    backendReference : Loop.LoopBackend → String
    backendReference Loop.jsSequential = "jsSequential role fixture"
    backendReference Loop.gpuParallel = "gpuParallel role fixture"

jsSequentialEligible :
  MDL.Eligible loopBackendSelectionProblem Loop.jsSequential
jsSequentialEligible = tt , Loop.jsRefinesLogicalResult

gpuParallelEligible :
  MDL.Eligible loopBackendSelectionProblem Loop.gpuParallel
gpuParallelEligible = tt , Loop.gpuRefinesLogicalResult

semanticAdequacyRequiredByEligibility :
  (backend : Loop.LoopBackend) →
  MDL.Eligible loopBackendSelectionProblem backend →
  Portable.SemanticRefinement
    Loop.loopProblem backend Loop.canonicalInput tt
semanticAdequacyRequiredByEligibility backend eligible = proj₂ eligible

record PortableSemanticConsumerAdequacyBoundary : Set where
  constructor portableSemanticConsumerAdequacyBoundary
  field
    shorterDescriptionMayBypassSemanticAdequacy : Bool
    shorterDescriptionMayBypassSemanticAdequacyIsFalse :
      shorterDescriptionMayBypassSemanticAdequacy ≡ false
    semanticAdequacyDeterminesUniversalBestBackend : Bool
    semanticAdequacyDeterminesUniversalBestBackendIsFalse :
      semanticAdequacyDeterminesUniversalBestBackend ≡ false
    rankingRemainsConsumerIndexed : Bool
    rankingRemainsConsumerIndexedIsTrue :
      rankingRemainsConsumerIndexed ≡ true

canonicalPortableSemanticConsumerAdequacyBoundary :
  PortableSemanticConsumerAdequacyBoundary
canonicalPortableSemanticConsumerAdequacyBoundary =
  portableSemanticConsumerAdequacyBoundary
    false refl
    false refl
    true refl
