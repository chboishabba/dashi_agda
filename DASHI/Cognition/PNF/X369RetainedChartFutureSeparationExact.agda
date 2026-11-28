module DASHI.Cognition.PNF.X369RetainedChartFutureSeparationExact where

-- Same-object retained-chart weld. Reuses the existing input-indexed
-- future-consumer proof; observed finite paths are negative witnesses,
-- not an assertion that a partial native graph is closed.
-- Original Leech-LILA: Anatolii Kornienko. DASHI extension.
-- Source-written, kernel acceptance deferred.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

module RetainedChart
  (H U O Q R : Set)
  (step : U → H → H)
  (observe : U → H → O)
  (coarse : H → Q)
  (residual : H → R) where

  repaired : H → Q × R
  repaired h = coarse h , residual h

  advance : List U → H → H
  advance [] h = h
  advance (u ∷ us) h = advance us (step u h)

  module Stable
    (outputStable : (u : U) (x y : H) →
      repaired x ≡ repaired y → observe u x ≡ observe u y)
    (transitionStable : (u : U) (x y : H) →
      repaired x ≡ repaired y →
      repaired (step u x) ≡ repaired (step u y)) where

    futureOutputStable :
      (us : List U) (x y : H) → repaired x ≡ repaired y →
      Future.trace step observe us x ≡ Future.trace step observe us y
    futureOutputStable =
      Future.inputIndexedTraceDescent step observe repaired
        outputStable transitionStable

    futureRepairedStable :
      (us : List U) (x y : H) → repaired x ≡ repaired y →
      repaired (advance us x) ≡ repaired (advance us y)
    futureRepairedStable [] x y same = same
    futureRepairedStable (u ∷ us) x y same =
      futureRepairedStable us (step u x) (step u y)
        (transitionStable u x y same)

    futureCoarseStable :
      (us : List U) (x y : H) → repaired x ≡ repaired y →
      coarse (advance us x) ≡ coarse (advance us y)
    futureCoarseStable us x y same =
      Future.cong proj₁ (futureRepairedStable us x y same)

    -- Each common chronological word ending in a different retained
    -- chart is a necessary residual separation, independently of logits.
    retainedChartWitnessForcesResidual :
      (us : List U) (x y : H) →
      coarse x ≡ coarse y →
      (coarse (advance us x) ≡ coarse (advance us y) → ⊥) →
      residual x ≡ residual y → ⊥
    retainedChartWitnessForcesResidual us x y sameCoarse separated sameResidual =
      separated (futureCoarseStable us x y
        (Future.cong₂ _,_ sameCoarse sameResidual))

    -- Likewise an actual future consumer trace difference.
    consumerWitnessForcesResidual :
      (us : List U) (x y : H) →
      coarse x ≡ coarse y →
      (Future.trace step observe us x ≡
       Future.trace step observe us y → ⊥) →
      residual x ≡ residual y → ⊥
    consumerWitnessForcesResidual us x y sameCoarse separated sameResidual =
      separated (futureOutputStable us x y
        (Future.cong₂ _,_ sameCoarse sameResidual))

  -- The unconditional fallback is the full original state. This is a
  -- constructive upper bound, not a claim of compression.
  fullLift : H → Q × H
  fullLift h = coarse h , h

  fullReopen : Q × H → H
  fullReopen = proj₂

  fullBidi : (h : H) → fullReopen (fullLift h) ≡ h
  fullBidi h = refl

  fullOutputStable :
    (u : U) (x y : H) → fullLift x ≡ fullLift y →
    observe u x ≡ observe u y
  fullOutputStable u x y same =
    Future.cong (observe u) (Future.cong fullReopen same)

  fullTransitionStable :
    (u : U) (x y : H) → fullLift x ≡ fullLift y →
    fullLift (step u x) ≡ fullLift (step u y)
  fullTransitionStable u x y same =
    Future.cong (λ h → fullLift (step u h)) (Future.cong fullReopen same)

  fullFutureStable :
    (us : List U) (x y : H) → fullLift x ≡ fullLift y →
    Future.trace step observe us x ≡ Future.trace step observe us y
  fullFutureStable = Future.inputIndexedTraceDescent
    step observe fullLift fullOutputStable fullTransitionStable
