module DASHI.Cognition.PNF.DynamicApproximateMultiResolutionErrorExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- DYNAMIC APPROXIMATE MULTI-RESOLUTION ERROR ACCUMULATION
--
-- Fine and compressed states evolve under the same query trace.  A supplied
-- one-step theorem bounds the next representation error by the current error
-- plus four independently typed local defects: compression, selection, local
-- residual and modality.  Induction gives the complete finite-trace budget.
------------------------------------------------------------------------

record LocalDefect : Set where
  constructor localDefect
  field
    compression selection localResidual modality : Nat

open LocalDefect public

defectTotal : LocalDefect → Nat
defectTotal defect =
  compression defect + selection defect + localResidual defect + modality defect

record ApproxDynamicAbstraction
    (Fine Compressed Query : Set) : Set₁ where
  constructor approxDynamicAbstraction
  field
    fineStep : Query → Fine → Fine
    compressedStep : Query → Compressed → Compressed
    representationError : Fine → Compressed → Nat
    localDefect : Query → Fine → Compressed → LocalDefect
    oneStepError :
      (query : Query) → (fine : Fine) → (compressed : Compressed) →
      representationError
        (fineStep query fine)
        (compressedStep query compressed)
      ≤ representationError fine compressed
        + defectTotal (localDefect query fine compressed)

open ApproxDynamicAbstraction public

runFine :
  ∀ {Fine Compressed Query} →
  ApproxDynamicAbstraction Fine Compressed Query →
  List Query → Fine → Fine
runFine system [] fine = fine
runFine system (query ∷ rest) fine =
  runFine system rest (fineStep system query fine)

runCompressed :
  ∀ {Fine Compressed Query} →
  ApproxDynamicAbstraction Fine Compressed Query →
  List Query → Compressed → Compressed
runCompressed system [] compressed = compressed
runCompressed system (query ∷ rest) compressed =
  runCompressed system rest (compressedStep system query compressed)

traceDefectBudget :
  ∀ {Fine Compressed Query} →
  ApproxDynamicAbstraction Fine Compressed Query →
  List Query → Fine → Compressed → Nat
traceDefectBudget system [] fine compressed = 0
traceDefectBudget system (query ∷ rest) fine compressed =
  defectTotal (localDefect system query fine compressed)
  + traceDefectBudget system rest
      (fineStep system query fine)
      (compressedStep system query compressed)

traceErrorBound :
  ∀ {Fine Compressed Query}
    (system : ApproxDynamicAbstraction Fine Compressed Query)
    (queries : List Query)
    (fine : Fine)
    (compressed : Compressed) →
  representationError system
    (runFine system queries fine)
    (runCompressed system queries compressed)
  ≤ representationError system fine compressed
    + traceDefectBudget system queries fine compressed
traceErrorBound system [] fine compressed = ≤-refl
traceErrorBound system (query ∷ rest) fine compressed =
  ≤-trans
    (traceErrorBound system rest
      (fineStep system query fine)
      (compressedStep system query compressed))
    rearrange
  where
    local : Nat
    local = defectTotal (localDefect system query fine compressed)

    tail : Nat
    tail = traceDefectBudget system rest
      (fineStep system query fine)
      (compressedStep system query compressed)

    firstStep :
      representationError system
        (fineStep system query fine)
        (compressedStep system query compressed)
      ≤ representationError system fine compressed + local
    firstStep = oneStepError system query fine compressed

    rearrange :
      representationError system
        (fineStep system query fine)
        (compressedStep system query compressed)
        + tail
      ≤ representationError system fine compressed + (local + tail)
    rearrange =
      ≤-trans
        (+-mono-≤ firstStep ≤-refl)
        (≤-reflexive (+-assoc
          (representationError system fine compressed) local tail))

------------------------------------------------------------------------
-- With zero initial representation error, trace distortion is bounded solely
-- by the sum of typed local defects.
------------------------------------------------------------------------

zeroInitialTraceErrorBound :
  ∀ {Fine Compressed Query}
    (system : ApproxDynamicAbstraction Fine Compressed Query)
    (queries : List Query)
    (fine : Fine)
    (compressed : Compressed) →
  representationError system fine compressed ≡ 0 →
  representationError system
    (runFine system queries fine)
    (runCompressed system queries compressed)
  ≤ traceDefectBudget system queries fine compressed
zeroInitialTraceErrorBound system queries fine compressed initialZero
  rewrite initialZero = traceErrorBound system queries fine compressed
