module DASHI.Cognition.PNF.DynamicMultiQueryMultiResolutionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- DYNAMIC MULTI-QUERY MULTI-RESOLUTION ABSTRACTION
--
-- The earlier theorem factors each query observation through compressed global
-- state plus local residual.  Here the retained carrier itself evolves across
-- an arbitrary query trace, and the abstraction commutes with every step.
------------------------------------------------------------------------

record DynamicMultiResolutionSystem
    (Fine Coarse Local Query Observation : Set) : Set₁ where
  constructor dynamicMultiResolutionSystem
  field
    compressGlobal : Fine → Coarse
    localResidual : Fine → Local

    fineStep : Query → Fine → Fine
    coarseStep : Query → Coarse → Coarse
    localStep : Query → Local → Local

    observeFine : Fine → Observation
    observeRetained : Coarse → Local → Observation

    compressCommutes :
      (query : Query) → (fine : Fine) →
      compressGlobal (fineStep query fine)
      ≡ coarseStep query (compressGlobal fine)

    localCommutes :
      (query : Query) → (fine : Fine) →
      localResidual (fineStep query fine)
      ≡ localStep query (localResidual fine)

    observationFactors :
      (fine : Fine) →
      observeFine fine
      ≡ observeRetained (compressGlobal fine) (localResidual fine)

open DynamicMultiResolutionSystem public

runFine :
  ∀ {Fine Coarse Local Query Observation} →
  DynamicMultiResolutionSystem Fine Coarse Local Query Observation →
  List Query → Fine → Fine
runFine system [] fine = fine
runFine system (query ∷ rest) fine =
  runFine system rest (fineStep system query fine)

runCoarse :
  ∀ {Fine Coarse Local Query Observation} →
  DynamicMultiResolutionSystem Fine Coarse Local Query Observation →
  List Query → Coarse → Coarse
runCoarse system [] coarse = coarse
runCoarse system (query ∷ rest) coarse =
  runCoarse system rest (coarseStep system query coarse)

runLocal :
  ∀ {Fine Coarse Local Query Observation} →
  DynamicMultiResolutionSystem Fine Coarse Local Query Observation →
  List Query → Local → Local
runLocal system [] local = local
runLocal system (query ∷ rest) local =
  runLocal system rest (localStep system query local)

compressCommutesWithEveryQueryTrace :
  ∀ {Fine Coarse Local Query Observation}
    (system : DynamicMultiResolutionSystem Fine Coarse Local Query Observation)
    (queries : List Query)
    (fine : Fine) →
  compressGlobal system (runFine system queries fine)
  ≡ runCoarse system queries (compressGlobal system fine)
compressCommutesWithEveryQueryTrace system [] fine = refl
compressCommutesWithEveryQueryTrace system (query ∷ rest) fine =
  trans
    (compressCommutesWithEveryQueryTrace system rest (fineStep system query fine))
    (cong (runCoarse system rest) (compressCommutes system query fine))

localResidualCommutesWithEveryQueryTrace :
  ∀ {Fine Coarse Local Query Observation}
    (system : DynamicMultiResolutionSystem Fine Coarse Local Query Observation)
    (queries : List Query)
    (fine : Fine) →
  localResidual system (runFine system queries fine)
  ≡ runLocal system queries (localResidual system fine)
localResidualCommutesWithEveryQueryTrace system [] fine = refl
localResidualCommutesWithEveryQueryTrace system (query ∷ rest) fine =
  trans
    (localResidualCommutesWithEveryQueryTrace system rest (fineStep system query fine))
    (cong (runLocal system rest) (localCommutes system query fine))

traceObservationFactorsThroughEvolvedRetainedCarrier :
  ∀ {Fine Coarse Local Query Observation}
    (system : DynamicMultiResolutionSystem Fine Coarse Local Query Observation)
    (queries : List Query)
    (fine : Fine) →
  observeFine system (runFine system queries fine)
  ≡ observeRetained system
      (runCoarse system queries (compressGlobal system fine))
      (runLocal system queries (localResidual system fine))
traceObservationFactorsThroughEvolvedRetainedCarrier system queries fine =
  trans
    (observationFactors system (runFine system queries fine))
    (cong₂
      (observeRetained system)
      (compressCommutesWithEveryQueryTrace system queries fine)
      (localResidualCommutesWithEveryQueryTrace system queries fine))
  where
    cong₂ :
      ∀ {A B C : Set} (f : A → B → C)
        {a a′ : A} {b b′ : B} →
      a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
    cong₂ f refl refl = refl

sameInitialRetainedCarrierImpliesSameObservationAfterEveryQueryTrace :
  ∀ {Fine Coarse Local Query Observation}
    (system : DynamicMultiResolutionSystem Fine Coarse Local Query Observation)
    {left right : Fine} →
  compressGlobal system left ≡ compressGlobal system right →
  localResidual system left ≡ localResidual system right →
  (queries : List Query) →
  observeFine system (runFine system queries left)
  ≡ observeFine system (runFine system queries right)
sameInitialRetainedCarrierImpliesSameObservationAfterEveryQueryTrace
  system {left} {right} coarseEqual localEqual queries =
  trans
    (traceObservationFactorsThroughEvolvedRetainedCarrier system queries left)
    (trans
      (cong₂
        (observeRetained system)
        (cong (runCoarse system queries) coarseEqual)
        (cong (runLocal system queries) localEqual))
      (sym (traceObservationFactorsThroughEvolvedRetainedCarrier system queries right)))
  where
    cong₂ :
      ∀ {A B C : Set} (f : A → B → C)
        {a a′ : A} {b b′ : B} →
      a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
    cong₂ f refl refl = refl

------------------------------------------------------------------------
-- This is the state-abstraction theorem missing from one-query factorization:
-- the same retained carrier remains sufficient under arbitrary query traces
-- provided both global and local components commute with the fine dynamics.
------------------------------------------------------------------------
